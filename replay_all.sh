#!/usr/bin/env bash
# Replay every case of one benchmark, dumping each run's raw stream-json to
# <out>/<code>.jsonl and the proof it wrote to <out>/<code>.v, where <out> is
# run/ unless --out DIR is given (relative to this script's directory).
# Continues on failure and prints a pass/fail summary (replay.py exits 0 only
# when a run is VERIFIED).
#
# Modes: Lin (linNNN) and DRB (drbNNN), the cases the proof guide was tuned
# on, and Linheld (linheldNNN) and DRBheld (drbheldNNN), the held-out cases.
#
# A case whose <out>/<code>.jsonl already exists is SKIPPED (resume-friendly).
# Pass --force (or -f) to re-run every case, overwriting existing dumps.
# Pass --model NAME to pick the model (default: claude-opus-5-5) and
# --effort LEVEL for the reasoning effort (default: low).
# Pass --save-solutions to replay nothing and instead copy the proof of every
# prior run (<out>/<code>.v) into solutions/ as the case's reference solution,
# overwriting any existing one.
#
# Runs are blind: replay.py removes every reference solution from disk for the
# run. The solutions/ dirs are snapshotted once at startup and restored after each
# case, so uncommitted edits survive. Nothing is committed: commit <out>/
# yourself once the batch is done.
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

MODEL="claude-opus-5-5"
EFFORT="low"
SAVE_SOLUTIONS=0
OUT="run"

usage() {
    echo "usage: $0 <Lin|Linheld|DRB|DRBheld> [--force] [--model NAME] [--effort LEVEL] [--out DIR] [--save-solutions]" >&2
    exit 2
}

# mode -> replay.py mode
declare -A REPLAY_MODE=( [Lin]="Lin" [Linheld]="Lin" [DRB]="DRB" [DRBheld]="DRB" )
# mode -> (case dir, case glob)
declare -A CASE_DIR=( [Lin]="src/linearizable/cases" [Linheld]="src/linearizable/cases"
                      [DRB]="src/dataracebench/cases" [DRBheld]="src/dataracebench/cases" )
declare -A CASE_GLOB=( [Lin]="lin[0-9]*__code.v" [Linheld]="linheld[0-9]*__code.v"
                       [DRB]="drb[0-9]*__code.v" [DRBheld]="drbheld[0-9]*__code.v" )
# Solution dirs (solution files: Lin=<code>_mgc.v, DRB=<code>_<name>__proof.v).
# replay.py wipes the solutions of both benchmarks, so both are snapshotted.
SOL_DIRS=(src/linearizable/solutions src/dataracebench/solutions)
# Cases never replayed: drb001 is the worked example printed in full in the
# DRB proof guide, so a run on it only measures copying.
EXCLUDE=(drb001)

MODE="${1:-}"
[ -n "${REPLAY_MODE[$MODE]+x}" ] || usage

FORCE=0
shift
while [ "$#" -gt 0 ]; do
    case "$1" in
        -f|--force) FORCE=1 ;;
        --model) [ "$#" -ge 2 ] || usage; MODEL="$2"; shift ;;
        --model=*) MODEL="${1#--model=}" ;;
        --effort) [ "$#" -ge 2 ] || usage; EFFORT="$2"; shift ;;
        --effort=*) EFFORT="${1#--effort=}" ;;
        --out) [ "$#" -ge 2 ] || usage; OUT="$2"; shift ;;
        --out=*) OUT="${1#--out=}" ;;
        --save-solutions) SAVE_SOLUTIONS=1 ;;
        *) usage ;;
    esac
    shift
done

# --save-solutions: copy the proofs of prior runs into solutions/, then stop.
if [ "$SAVE_SOLUTIONS" -eq 1 ]; then
    for case_file in ${CASE_DIR[$MODE]}/${CASE_GLOB[$MODE]}; do
        [ -f "$case_file" ] || continue
        base="$(basename "$case_file")"
        code="${base%%_*}"
        if [[ " ${EXCLUDE[*]} " == *" $code "* ]]; then
            continue
        fi
        if [ ! -f "$OUT/$code.v" ]; then
            printf "  %-10s %s\n" "$code" "no prior run"
            continue
        fi
        if [ "${REPLAY_MODE[$MODE]}" = Lin ]; then
            dest="src/linearizable/solutions/${code}_mgc.v"
        else
            dest="src/dataracebench/solutions/${base/__code.v/__proof.v}"
        fi
        cp "$OUT/$code.v" "$dest"
        printf "  %-10s %s\n" "$code" "saved to $dest"
    done
    exit 0
fi

# Snapshot the solutions/ dirs; restore() puts them back exactly (removing any file a
# run created there, e.g. a fresh drbheld proof, once it is archived in <out>/).
SNAP="$(mktemp -d)"
for d in "${SOL_DIRS[@]}"; do
    mkdir -p "$SNAP/$d"
    cp -a "$d/." "$SNAP/$d/"
done
restore() {
    for d in "${SOL_DIRS[@]}"; do
        rm -rf "$d"
        mkdir -p "$d"
        cp -a "$SNAP/$d/." "$d/"
    done
}

mkdir -p "$OUT"
declare -A STATUS

# Discover all case codes (e.g. lin001, linheld016, drb016, drbheld033) from
# the cases dir.
mapfile -t CODES < <(
    ls ${CASE_DIR[$MODE]}/${CASE_GLOB[$MODE]} 2>/dev/null \
        | xargs -n1 basename | sed -E 's/_.*//' | sort -u
)
if [ "${#CODES[@]}" -eq 0 ]; then
    echo "error: no case files found for $MODE" >&2
    exit 1
fi

ALL_CODES=()
for code in "${CODES[@]}"; do
    if [[ " ${EXCLUDE[*]} " == *" $code "* ]]; then
        echo ">>> excluding $code (see EXCLUDE)"
        continue
    fi
    ALL_CODES+=("$code")
    if [ "$FORCE" -eq 0 ] && [ -f "$OUT/$code.jsonl" ]; then
        echo ">>> skipping $code ($OUT/$code.jsonl exists; use --force to re-run)"
        STATUS[$code]="SKIPPED"
        continue
    fi
    echo "=============================================================="
    echo ">>> replaying $code ($MODE)"
    echo "=============================================================="
    if python3 replay.py "${REPLAY_MODE[$MODE]}" "$code" \
            --model "$MODEL" \
            --effort "$EFFORT" \
            --dump "$OUT/$code.jsonl"; then
        STATUS[$code]="VERIFIED"
    else
        STATUS[$code]="NOT VERIFIED"
    fi

    # Archive the proof the run wrote (if any), then restore the solutions.
    rm -f "$OUT/$code.v"
    for sol in "${SOL_DIRS[@]}"; do
        for f in "$sol/${code}"_*.v; do
            [ -f "$f" ] && cp "$f" "$OUT/$code.v"
        done
    done
    restore
done
rm -rf "$SNAP"

echo
echo "=============================================================="
echo "summary"
echo "=============================================================="
for code in "${ALL_CODES[@]}"; do
    printf "  %-10s %s\n" "$code" "${STATUS[$code]}"
done
