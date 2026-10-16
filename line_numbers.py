#!/usr/bin/env python3
"""Compute min, max and average LOC per case (ignoring comments and blank lines).

Usage: line_numbers.py {DRB|DRBheld|DRBall|Lin|Linheld|Linall}

A "case" groups all .ml files in the mode's bin/ directory sharing the same
codeNNN prefix (drbNNN / drbheldNNN / linNNN / linheldNNN). LOC is counted per
file after stripping (* ... *) comments (nested/multiline) and blank lines.
DRBall and Linall cover both the tuning and the held-out sets.
The proof guides' worked examples are not evaluated, hence not counted.
"""

import re
import sys
from collections import defaultdict
from pathlib import Path

_ROOT = Path(__file__).resolve().parent

# mode -> (benchmark directory, case-id prefixes)
MODES = {
    "DRB": ("dataracebench", ["drb"]),
    "DRBheld": ("dataracebench", ["drbheld"]),
    "DRBall": ("dataracebench", ["drb", "drbheld"]),
    "Lin": ("linearizable", ["lin"]),
    "Linheld": ("linearizable", ["linheld"]),
    "Linall": ("linearizable", ["lin", "linheld"]),
}

# Worked examples of the proof guides, which are given to the model rather
# than evaluated (the Lin guide's key_buggy_stack has no case id).
EXCLUDED = {"drb001"}


def strip_comments(text):
    """Remove OCaml (* ... *) comments, honoring nesting."""
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        two = text[i:i + 2]
        if two == "(*":
            depth += 1
            i += 2
        elif two == "*)" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def count_loc(path):
    stripped = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
    return sum(1 for line in stripped.splitlines() if line.strip())


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in MODES:
        sys.exit(f"Usage: {sys.argv[0]} {{{'|'.join(MODES)}}}")

    bench, codes = MODES[sys.argv[1]]
    root = _ROOT / bench / "bin"
    cases = defaultdict(int)
    prefix = re.compile(rf"^((?:{'|'.join(codes)})\d+)")
    for mlfile in root.glob("*.ml"):
        m = prefix.match(mlfile.name)
        if m and m.group(1) not in EXCLUDED:
            cases[m.group(1)] += count_loc(mlfile)

    if not cases:
        print(f"No {'/'.join(codes)} cases found.")
        return

    locs = sorted(cases.items())
    width = max(len(name) for name, _ in locs)
    print(f"{'case'.ljust(width)}  LOC")
    for name, loc in locs:
        print(f"{name.ljust(width)}  {loc}")

    values = list(cases.values())
    print("-" * (width + 6))
    print(f"cases : {len(values)}")
    print(f"min   : {min(values)}")
    print(f"max   : {max(values)}")
    print(f"avg   : {sum(values) / len(values):.1f}")


if __name__ == "__main__":
    main()
