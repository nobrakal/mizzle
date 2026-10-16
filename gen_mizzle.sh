#! /bin/bash
# Translate the OCaml sources of a nested dune project into Rocq AST under
# src/<project>/, using the vendored ocaml2mizzle (see ocaml2mizzle/VENDORED.md).
#
# The translator emits requires against Mizzle's vendored language directly, so
# this script no longer post-processes the generated files; the mapping of
# library names onto Rocq logical paths lives in ocaml2mizzle/lib/mizzlelang/mizzle.ml and
# is steered by the --rocq-* options below.
#
# Usage: gen_mizzle.sh <DRB|Lin>
#   DRB -> dataracebench/  into  src/dataracebench/
#   Lin -> linearizable/   into  src/linearizable/
set -euo pipefail

cd "$(dirname "$0")"

usage() { echo "usage: $0 <DRB|Lin>" >&2; exit 2; }

MODE="${1:-}"
case "$MODE" in
    DRB) SRC="dataracebench"; DST="src/dataracebench" ;;
    Lin) SRC="linearizable";  DST="src/linearizable" ;;
    *) usage ;;
esac

# Always run the freshly built in-tree translator, never one on PATH.
OCAML2MIZZLE="$PWD/_build/default/ocaml2mizzle/bin/ocaml2mizzle.exe"
dune build ocaml2mizzle/bin/ocaml2mizzle.exe

# ocaml2mizzle reads .cmt files from the project's _build, so build it first.
(cd "$SRC" && dune build)

if [ "$MODE" = "DRB" ]; then
    # The __types.v files carry no useful content for DRB, so they are neither
    # generated nor required; the `drb` support library is the hand-written
    # `drb_axiom` on the Rocq side.
    "$OCAML2MIZZLE" -f --only=cases \
        --no-types \
        --rocq-lib drb=mizzle:drb_axiom \
        "$SRC" "$DST"
else
    # The __types.v files carry the variant tag notations (e.g. Push/Pop), so
    # they are kept; `cases` is a library of the linearizable project, which
    # lands under the mizzle.linearizable logical path.
    "$OCAML2MIZZLE" -f --only=cases \
        --rocq-prefix mizzle.linearizable \
        "$SRC" "$DST"
fi
