#!/bin/bash
# Run every DataRaceBench port under ThreadSanitizer, as a sanity check that
# the OCaml translation keeps the race.
#
# Usage: ./run_tsan.sh [-h|--help] [LOGDIR [WORKDIR]]
#
# LOGDIR (default: WORKDIR/logs) receives one log per benchmark, named
# <benchmark>.log, in which the output of each run follows a line
# `===== run <k>/<RUNS>: <class> (exit <status>) =====`, and summary.txt.
# The logs and summary of a previous run in LOGDIR are removed; other files
# are left untouched.
#
# WORKDIR (default: a fresh `mktemp -d`) holds the TSan opam switch, a copy of
# the sources and the build. Pass an existing WORKDIR to reuse its switch
# instead of rebuilding the compiler.
#
# Environment:
#   RUNS     number of runs per benchmark (default 100)
#   TIMEOUT  per-run timeout in seconds (default 5)
#   START_BARRIER
#            if set to 1, the two domains of [Drb.par] wait for each other
#            before running their branch (default 0). Otherwise, the main
#            domain often completes its branch before the other domain has
#            finished spawning, which orders their accesses and hides races
#            from TSan (e.g. DRB185).
#
# Each run of each benchmark is classified as one of:
#   race        TSan reported a race involving the benchmark's own code
#   other       TSan reported races, but none involving the benchmark's code
#   none        the program terminated without any report
#   timeout     the program did not terminate within TIMEOUT
#   crash       the program failed without any report
# The summary gives, for each benchmark, the number of runs of each class;
# a benchmark counts as detected if at least one of its runs is a race.
set -euo pipefail
IFS=$'\n\t'

# Print the comment at the top of this file.
if [ "${1:-}" = "-h" ] || [ "${1:-}" = "--help" ]; then
  sed -n '2,/^[^#]/{/^#/s/^# \{0,1\}//p}' "${BASH_SOURCE[0]}"
  exit 0
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="${2:-$(mktemp -d -t drb-tsan-XXXXXX)}"
WORK="$(cd "$WORK" && pwd)"
RUNS="${RUNS:-100}"
TIMEOUT="${TIMEOUT:-5}"
START_BARRIER="${START_BARRIER:-0}"
SWITCH="$WORK/switch"
SRC="$WORK/src"
LOGS="${1:-$WORK/logs}"
mkdir -p "$LOGS"
LOGS="$(cd "$LOGS" && pwd)"
# Use OCaml >= 5.5: before, TSan did not instrument loads nested in a store
# (`r := !r + 1`, ocaml/ocaml#14332), and the runtime did not build with
# GCC 15's TSan (runtime/weak.c).
OCAML_VERSION="5.5.1"

echo "Working directory: $WORK"

# Create the TSan switch, unless WORKDIR already has one.
export OPAMYES=true
SWITCH_STATE="reused"
if [ ! -x "$SWITCH/_opam/bin/dune" ] \
   || [ ! -d "$SWITCH/_opam/lib/domainslib" ] \
   || [ "$("$SWITCH/_opam/bin/ocamlopt" -version)" != "$OCAML_VERSION" ]; then
  # conf-unwind (required by ocaml-option-tsan) needs the libunwind headers.
  if ! pkg-config --exists libunwind; then
    echo "error: libunwind headers not found (Debian/Ubuntu: apt install libunwind-dev)" >&2
    exit 1
  fi
  # Remove the leftovers of a previous failed attempt.
  if [ -d "$SWITCH/_opam" ]; then
    opam switch remove "$SWITCH" || rm -rf "$SWITCH/_opam"
  fi
  echo "Creating a TSan opam switch (this compiles OCaml)..."
  mkdir -p "$SWITCH"
  opam switch create "$SWITCH" --no-install \
    --packages "ocaml-variants.$OCAML_VERSION+options,ocaml-option-tsan"
  opam install --switch="$SWITCH" dune domainslib
  SWITCH_STATE="created"
fi
run_in_switch() { opam exec --switch="$SWITCH" -- "$@"; }
echo "TSan switch ready ($SWITCH_STATE): $SWITCH" \
  "(OCaml $(run_in_switch ocamlopt -version))"

# Copy the sources and add one executable dispatching on its argument.
rm -rf "$SRC"
mkdir -p "$SRC/bin" "$SRC/tsan"
cp "$HERE/dune-project" "$SRC/"
cp -r "$HERE/lib" "$SRC/"
cp "$HERE"/bin/*.ml "$HERE/bin/dune" "$SRC/bin/"

if [ "$START_BARRIER" = 1 ]; then
  echo "Using a start barrier in Drb.par"
  # The original [par] becomes unused once shadowed.
  sed -i 's/^let par f g =/let[@warning "-32"] par f g =/' "$SRC/lib/drb.ml"
  cat >> "$SRC/lib/drb.ml" <<'EOF'

(* Added by run_tsan.sh (START_BARRIER=1): shadows [par] above. *)
let par f g =
  let ready = Atomic.make 0 in
  let barrier () =
    Atomic.incr ready;
    while Atomic.get ready < 2 do Domain.cpu_relax () done
  in
  let t = Domain.spawn (fun () -> barrier (); f ()) in
  barrier ();
  g ();
  Domain.join t
EOF
fi

BENCHS=()
for f in "$SRC"/bin/*.ml; do
  BENCHS+=("$(basename "$f" .ml)")
done

{
  echo "let () ="
  echo "  match Sys.argv.(1) with"
  for b in "${BENCHS[@]}"; do
    echo "  | \"$b\" -> Cases.${b^}.main ()"
  done
  echo "  | s -> failwith (\"unknown benchmark \" ^ s)"
} > "$SRC/tsan/tsan_main.ml"
cat > "$SRC/tsan/dune" <<'EOF'
(executable
 (name tsan_main)
 (libraries cases))
EOF

echo "Building..."
(cd "$SRC" && run_in_switch dune build ./tsan/tsan_main.exe)
EXE="$SRC/_build/default/tsan/tsan_main.exe"

# Run the benchmarks.
rm -f "$LOGS"/*.log "$LOGS/summary.txt"
# Shorten the reports: print each frame as `#<n> <function> <file>:<line>`,
# without the module offset and build id, and print the files of the OCaml
# distribution (e.g. stdlib/domain.ml) relative to its build directory.
OCAML_BUILD="$SWITCH/_opam/.opam-switch/build/ocaml-compiler.$OCAML_VERSION/"
export TSAN_OPTIONS="halt_on_error=0 stack_trace_format='    #%n %f %S'\
 strip_path_prefix=$OCAML_BUILD"
SUMMARY="$LOGS/summary.txt"
CPU_MODEL="$(sed -n 's/^model name[[:space:]]*: //p' /proc/cpuinfo | head -n 1)"
{
  echo "# date:          $(date -Iseconds)"
  echo "# cores:         $(nproc)"
  echo "# cpu:           ${CPU_MODEL:-unknown}"
  echo "# ocaml:         $OCAML_VERSION (TSan)"
  echo "# runs:          $RUNS (per benchmark)"
  echo "# timeout:       ${TIMEOUT}s"
  echo "# start barrier: $START_BARRIER"
  echo "#"
} | tee "$SUMMARY"

printf "%-36s %7s %7s %7s %7s %7s\n" \
  benchmark race other none timeout crash | tee -a "$SUMMARY"

# Each run is classified on its own output, then appended to the log of its
# benchmark.
RUN_LOG="$WORK/run.log"
detected=0
for b in "${BENCHS[@]}"; do
  n_race=0 n_other=0 n_none=0 n_timeout=0 n_crash=0
  for ((r = 1; r <= RUNS; r++)); do
    status=0
    timeout "$TIMEOUT" "$EXE" "$b" > "$RUN_LOG" 2>&1 || status=$?
    if grep -q "WARNING: ThreadSanitizer: data race" "$RUN_LOG"; then
      # Stack frames mention the benchmark through its symbol or source file.
      if grep -qi "$b" "$RUN_LOG"; then
        class=race n_race=$((n_race + 1))
      else
        class=other n_other=$((n_other + 1))
      fi
    elif [ "$status" -eq 124 ]; then
      class=timeout n_timeout=$((n_timeout + 1))
    elif [ "$status" -ne 0 ]; then
      class=crash n_crash=$((n_crash + 1))
    else
      class=none n_none=$((n_none + 1))
    fi
    {
      echo "===== run $r/$RUNS: $class (exit $status) ====="
      cat "$RUN_LOG"
    } >> "$LOGS/$b.log"
  done
  [ "$n_race" -eq 0 ] || detected=$((detected + 1))
  printf "%-36s %7d %7d %7d %7d %7d\n" \
    "$b" "$n_race" "$n_other" "$n_none" "$n_timeout" "$n_crash" \
    | tee -a "$SUMMARY"
done

rm -f "$RUN_LOG"
echo
echo "Detected: $detected/${#BENCHS[@]}" | tee -a "$SUMMARY"
echo "Summary: $SUMMARY"
echo "Logs:    $LOGS"
