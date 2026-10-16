#!/usr/bin/env python3
"""Replay a test-case proof.

Usage: replay.py {Lin|DRB} CODE

Removes the reference solution for the case being proven, then launches Claude
to read the proof guide and verify the case file matching CODE. A PreToolUse
hook (this same script, invoked as ``replay.py --hook``) confines reads to
Coq sources and Markdown docs and forbids the git history and ``_build``
directory. Runs are blind: every reference solution is removed from disk and
the hook forbids reading any of them, so no proof can be copied from an
existing answer.

Memory / user settings are disabled via ``--setting-sources project,local``
(hooks are kept, unlike ``--bare``). Built-in tools are limited to an explicit
allowlist (``--tools Read,Write,Edit,Grep,Glob``), only the Rocq MCP is loaded
(``--mcp-config`` + ``--strict-mcp-config``), and no session transcript is
persisted (``--no-session-persistence``).
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys

from meta import lin_family

# The script lives at the theories/ root; everything is resolved relative to it.
ROOT = os.path.dirname(os.path.abspath(__file__))

# mode -> benchmark dir under src/
BENCHMARKS = {
    "Lin": "linearizable",
    "DRB": "dataracebench",
}

# Filenames ending with either of these are reference solutions and are hidden.
BLOCKED_SUFFIXES = ("__proof.v", "_mgc.v")

# The only file kinds Claude may read: Coq sources (.v) and Markdown docs (.md,
# the proof guide / ARCHITECTURE). Everything else — build
# scripts, JSON dumps, .vo binaries, dune/_CoqProject, run logs — is off-limits
# so a run can't wander outside the proof material. Extend here if a run
# genuinely needs another kind (e.g. ".ml"/".mli" originals, or the "dune" /
# "_CoqProject" build files).
ALLOWED_READ_SUFFIXES = (".v", ".md")

# Off-limits whatever the file kind: the OCaml projects the cases are
# translated from, whose READMEs (.md, so past the suffix filter) describe each
# case's race, and the run*/ log dirs, whose dumps and archived proofs
# (run/<code>.v) hold past answers. The Rocq side lives under src/ and is not
# affected.
BLOCKED_DIRS = tuple(
    [os.path.join(ROOT, d) for d in ("dataracebench", "linearizable")]
    + sorted(d.rstrip(os.sep) for d in glob.glob(os.path.join(ROOT, "run*", ""))))

# Env var carrying the one solution file (abspath) Claude IS allowed to touch.
ALLOW_ENV = "REPLAY_ALLOW"

# Basename of each benchmark's proof guide (under src/<bench>/support/).
GUIDE_NAME = "PROOF_GUIDE.md"


def run_hook():
    """PreToolUse hook: deny reads of reference solutions and non-.v/.md files.

    Exit 2 blocks the tool call (stderr becomes Claude's feedback); exit 0 lets
    the call proceed. The single authorized solution (the proof for the current
    case) is passed via $REPLAY_ALLOW. Reads are also confined to Coq sources
    and Markdown docs (see ALLOWED_READ_SUFFIXES), outside the OCaml source
    projects (see BLOCKED_DIRS).
    """
    allowed = os.environ.get(ALLOW_ENV, "")
    try:
        event = json.load(sys.stdin)
    except (json.JSONDecodeError, ValueError):
        return 0
    ti = event.get("tool_input", {}) or {}
    tool = event.get("tool_name", "")
    cwd = event.get("cwd") or os.getcwd()

    def resolve(p):
        return os.path.normpath(os.path.join(cwd, os.path.expanduser(p)))

    def inside(p, d):
        return p == d or p.startswith(d + os.sep)

    # The OCaml source projects and run logs: no Read, no Glob, no Grep
    # inside them...
    targets = [ti.get(k) for k in ("file_path", "path", "notebook_path")]
    if tool == "Glob" and isinstance(ti.get("pattern"), str):
        targets.append(os.path.join(ti.get("path") or cwd, ti["pattern"]))
    for t in targets:
        if isinstance(t, str) and any(inside(resolve(t), d)
                                      for d in BLOCKED_DIRS):
            sys.stderr.write(
                "replay: the OCaml source projects (dataracebench/, "
                "linearizable/) and the run logs (run*/) are off-limits in "
                "replay mode; the cases are under src/.\n")
            return 2
    # ...and no Grep from above them, whose matches would include their
    # contents. Search src/ (or a subdirectory) instead.
    if tool == "Grep":
        base = resolve(ti.get("path") or cwd)
        if any(inside(d, base) for d in BLOCKED_DIRS):
            sys.stderr.write(
                "replay: Grep over a directory containing the OCaml source "
                "projects or the run logs is forbidden in replay mode; "
                "search under src/ instead.\n")
            return 2

    # Any path-ish string the tool might use to reach a file.
    candidates = [ti.get(k) for k in ("file_path", "path", "pattern",
                                      "notebook_path")]
    for c in candidates:
        if not isinstance(c, str):
            continue
        # The git directory may expose past versions of the solutions; the
        # _build directory holds compiled solutions.
        parts = c.replace("\\", "/").split("/")
        if ".git" in parts or c.endswith(".git"):
            sys.stderr.write(
                "replay: reading the git directory is forbidden "
                "in replay mode (history may reveal reference solutions).\n")
            return 2
        if "_build" in parts or c.endswith("_build"):
            sys.stderr.write(
                "replay: reading the _build directory is forbidden "
                "in replay mode (it holds compiled reference solutions).\n")
            return 2
        if any(suffix in c for suffix in BLOCKED_SUFFIXES):
            # Allow only an exact hit on the authorized solution file.
            if os.path.abspath(c) == allowed:
                continue
            sys.stderr.write(
                "replay: reading reference solutions "
                "(*__proof.v / *_mgc.v) is forbidden in replay mode.\n")
            return 2

    # Restrict *what kind* of file may be read to .v / .md. Applies to the whole
    # file a Read/Grep/Glob targets — not to Grep's content regex ([pattern]),
    # which is not a path.
    if tool == "Read":
        # A Read always names one concrete file: it must be .v or .md.
        fp = ti.get("file_path")
        if isinstance(fp, str) and not fp.endswith(ALLOWED_READ_SUFFIXES):
            sys.stderr.write(
                "replay: Read is restricted to .v and .md files.\n")
            return 2
    elif tool in ("Grep", "Glob"):
        # Directory searches are fine; only block pointing the search *at* a
        # single non-.v/.md file (its contents would leak via matching lines).
        p = ti.get("path")
        if isinstance(p, str):
            ext = os.path.splitext(p)[1]
            if ext and ext not in ALLOWED_READ_SUFFIXES:
                sys.stderr.write(
                    "replay: searching inside a non-.v/.md file is forbidden "
                    "in replay mode.\n")
                return 2
    return 0


def remove_solution(sol_file):
    """Remove a solution's .v and its compiled artifacts (source tree + _build).

    The .v alone is not enough: the compiled module stays importable through the
    Coq loadpath (the MCP loads _build/.../<name>.vo when a `Require Import`
    resolves it), which would leak the answer past the .v/.md read hook.
    """
    sol_rel_v = os.path.relpath(sol_file, ROOT)
    for base in (sol_file, os.path.join(ROOT, "_build", "default", sol_rel_v)):
        stem = os.path.splitext(base)[0]
        # Remove the source .v (dune keeps a copy under _build too) and every
        # compiled artifact, in both the src tree and the _build tree.
        for ext in (".v", ".vo", ".vos", ".vok", ".glob"):
            art = stem + ext
            if os.path.exists(art):
                os.remove(art)
                print(f"removed {os.path.relpath(art, ROOT)}")


def all_solution_files():
    """Every reference solution (*__proof.v / *_mgc.v) under both benchmarks."""
    files = []
    for bench in BENCHMARKS.values():
        sol_dir = os.path.join(ROOT, "src", bench, "solutions")
        for suffix in BLOCKED_SUFFIXES:
            files += glob.glob(os.path.join(sol_dir, f"*{suffix}"))
    return sorted(files)


def read_text(path):
    """Read a file's text for inlining into the prompt; '' if unreadable."""
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def opam_env():
    """Environment vars for the local opam switch (like `eval $(opam env)`).

    Returns a dict to merge into the child env, or {} if the switch/opam is
    unavailable.
    """
    if not os.path.isdir(os.path.join(ROOT, "_opam")):
        print("warning: local opam switch (_opam) not found")
        return {}
    try:
        out = subprocess.run(
            ["opam", "env", "--switch", ROOT, "--set-switch", "--shell=sh"],
            cwd=ROOT, capture_output=True, text=True, check=True,
        ).stdout
    except (FileNotFoundError, subprocess.CalledProcessError):
        print("warning: could not run `opam env`; rocq/coqc may be missing")
        return {}
    result = {}
    # Lines look like: VAR='value'; export VAR;
    for m in re.finditer(r"^(\w+)='(.*)'; export \1;", out, re.MULTILINE):
        # opam escapes embedded single quotes as '\''.
        result[m.group(1)] = m.group(2).replace("'\\''", "'")
    return result


def stream_event(event, verbose=False):
    """Render a stream-json event for live progress.

    With verbose=True, also print assistant thinking blocks as they stream.
    """
    etype = event.get("type")
    if etype == "assistant":
        for block in event.get("message", {}).get("content", []):
            btype = block.get("type")
            if btype == "text" and block.get("text", "").strip():
                print(block["text"].rstrip(), flush=True)
            elif btype == "thinking" and verbose and block.get("thinking", "").strip():
                print(f"[thinking] {block['thinking'].rstrip()}", flush=True)
            elif btype == "tool_use":
                inp = json.dumps(block.get("input", {}))
                if len(inp) > 200:
                    inp = inp[:200] + "..."
                print(f"[tool] {block.get('name', '?')} {inp}", flush=True)
    elif etype == "user":
        for block in event.get("message", {}).get("content", []):
            if block.get("type") == "tool_result":
                content = block.get("content", "")
                if isinstance(content, list):
                    content = " ".join(b.get("text", "") for b in content
                                       if isinstance(b, dict))
                content = str(content).strip().replace("\n", " ")
                if len(content) > 200:
                    content = content[:200] + "..."
                if content:
                    print(f"[result] {content}", flush=True)


def solution_path(mode, case_basename, code):
    """Path of the reference solution for the case being proven."""
    sol_dir = os.path.join(ROOT, "src", BENCHMARKS[mode], "solutions")
    if mode == "DRB":
        name = case_basename.replace("__code.v", "__proof.v")
    else:  # Lin: solution files are named <code>_mgc.v
        name = f"{code}_mgc.v"
    return os.path.join(sol_dir, name)


def warm_preamble(mode, case_path):
    """The `Require` block a solution for CASE opens with, as the reference
    solutions spell it. Handed to the run verbatim as the rocq_start preamble,
    so the import paths never have to be rediscovered from the tree."""
    base = os.path.basename(case_path)
    stem = base[:-len(".v")]
    code = base.split("_", 1)[0]
    if mode == "DRB":
        # Every DRB solution uses this block, arrays or not; cases that use
        # mutexes or assert also need the corresponding specs.
        lines = [
            "From mizzle.dataracebench.support Require Import drb_prelude.",
            "From mizzle.stdlib Require Import array.",
        ]
        with open(case_path) as f:
            src = f.read()
        for lib in ("mutex", "assert"):
            if re.search(rf"Require Import\s+{lib}\.", src):
                lines.append(f"From mizzle.stdlib Require Import {lib}.")
        lines.append(f"From mizzle.dataracebench.cases Require Import {stem}.")
        return "\n".join(lines)
    # Lin: prelude and pure model follow the data-structure family.
    prelude, model = {
        "Stack": ("mgc_prelude", "stack_model"),
        "Queue": ("mgc_prelude", "queue_opt_model"),
        "Hash table": ("htbl_prelude", "htbl_model"),
        "Two-lock queue": ("mgc_prelude", "queue_opt_model"),
        "Harris list": ("mgc_prelude", "htbl_model"),
    }.get(lin_family(code), ("mgc_prelude", None))
    lines = [f"From mizzle.linearizable.support Require Import {prelude}."]
    if model:
        lines.append(f"From mizzle.pure_logic Require Import {model}.")
    # Cases built on a mutex (the two-lock queues) also need its specs.
    with open(case_path) as f:
        if re.search(r"Require Import\s+mutex\.", f.read()):
            lines.append("From mizzle.stdlib Require Import mutex.")
    mods = [stem]
    types = case_path.replace("__code.v", "__types.v")
    if os.path.exists(types):
        mods.append(os.path.basename(types)[:-len(".v")])
    lines.append("From mizzle.linearizable.cases Require Import "
                 + " ".join(mods) + ".")
    return "\n".join(lines)


def required_theorems(mode, case_basename):
    """Top-level theorem(s) that must be present and proved for this case."""
    if mode == "DRB":
        # e.g. drb001_antidep__code.v -> drb001_antidep_racy
        stem = case_basename.replace("__code.v", "")
        return [f"{stem}_racy"]
    # Lin: the mgc adequacy theorem is the single fixed goal.
    return ["mgc_produces_non_linearizable"]


# Substrings that mark a failed / incomplete MCP whole-file check.
_COMPILE_FAIL_MARKS = ("compile_error", "error_positions", "\"error\"",
                       "'error'", "failed", "failure", "timed out", "timeout")
# Substrings that mark a successful MCP whole-file check.
_COMPILE_OK_MARKS = ("success", "compiled", "no error", "proof_finished",
                     "\"ok\": true", "'ok': true")


def compile_verdict(content):
    """Best-effort pass/fail from an MCP compile/verify result. None if unclear."""
    c = content.lower()
    if not c.strip():
        return None
    if any(m in c for m in _COMPILE_FAIL_MARKS):
        return False
    if any(m in c for m in _COMPILE_OK_MARKS):
        return True
    return None


def scan_source(sol_file, mode, case_basename):
    """Static anti-cheat scan of the produced proof (reads the file, no build).

    Returns (cheats, missing): cheat keywords present, required theorems absent.
    """
    if not os.path.exists(sol_file):
        return ["<file not written>"], required_theorems(mode, case_basename)
    with open(sol_file, encoding="utf-8", errors="replace") as f:
        src = f.read()
    cheats = [w for w in ("admit", "Admitted", "Axiom")
              if re.search(rf"\b{w}\b", src)]
    missing = [t for t in required_theorems(mode, case_basename)
               if not re.search(rf"\b(Theorem|Lemma|Corollary)\s+{re.escape(t)}\b",
                                src)]
    return cheats, missing


def main():
    p = argparse.ArgumentParser(description="Replay a test-case proof.")
    p.add_argument("mode", choices=sorted(BENCHMARKS))
    p.add_argument("code", help="case code, e.g. drb016 or lin003")
    p.add_argument("--model", default="claude-opus-5-5",
                   help="model to run (forwarded to `claude --model`), "
                        "e.g. claude-opus-5-5 or claude-sonnet-5 "
                        "(default: claude-opus-5-5)")
    p.add_argument("--effort", choices=["low", "medium", "high", "xhigh", "max"],
                   default="low",
                   help="reasoning effort forwarded to `claude --effort` "
                        "(lowest is 'low'; Claude Code defaults to 'xhigh'). "
                        "Lower effort cuts thinking/output tokens — the priciest "
                        "line item — at some cost to proof success rate "
                        "(default: low)")
    p.add_argument("--dump", metavar="FILE",
                   help="write the raw stream-json events (one JSON object per "
                        "line, JSONL) to FILE")
    p.add_argument("--verbose", action="store_true",
                   help="stream assistant thinking blocks to the console as they "
                        "arrive")
    args = p.parse_args()

    bench = BENCHMARKS[args.mode]

    # Locate the case file matching CODE.
    pattern = os.path.join(ROOT, "src", bench, "cases", f"{args.code}*__code.v")
    matches = sorted(glob.glob(pattern))
    if not matches:
        sys.exit(f"error: no case file matching {pattern}")
    if len(matches) > 1:
        rels = ", ".join(os.path.relpath(m, ROOT) for m in matches)
        sys.exit(f"error: code {args.code!r} is ambiguous: {rels}")
    case_path = matches[0]
    case_file = os.path.relpath(case_path, ROOT)

    proof_guide = os.path.join("src", bench, "support", GUIDE_NAME)

    # The one solution Claude may write/read: remove it so the proof is redone
    # (both the .v and its compiled artifacts, so the old answer cannot leak
    # back in through the Coq loadpath).
    sol_file = solution_path(args.mode, os.path.basename(case_path), args.code)
    allowed_abs = os.path.abspath(sol_file)
    remove_solution(sol_file)

    # Wipe every OTHER reference solution so the proof cannot be copied from
    # an existing answer. Combined with the hook's solution ban, no solution
    # but the one being written is readable during the run.
    for other in all_solution_files():
        if os.path.abspath(other) != allowed_abs:
            remove_solution(other)

    # Remove stale Coq .aux files under src/ (including hidden .<name>.aux).
    for dirpath, _, filenames in os.walk(os.path.join(ROOT, "src")):
        for fn in filenames:
            if fn.endswith(".aux"):
                aux = os.path.join(dirpath, fn)
                os.remove(aux)
                print(f"removed {os.path.relpath(aux, ROOT)}")

    # Remove leftover Rocq MCP scratch files (rocq_mcp_cache_*.v) from prior runs.
    for cache in glob.glob(os.path.join(ROOT, "rocq_mcp_cache_*.v")):
        os.remove(cache)
        print(f"removed {os.path.relpath(cache, ROOT)}")

    restriction = (
        "You may only read .v and .md files; every other file kind is "
        "off-limits. You are also forbidden to read the git history, the "
        "_build directory, the run logs (run*/) and the OCaml source "
        "projects (dataracebench/, linearizable/); search under src/, not "
        "from the project root. "
        "Within those limits you may freely inspect the "
        "project's .v/.md files, but reading any reference solution "
        "(*__proof.v / *_mgc.v) is forbidden — write the proof yourself. "
    )

    sol_rel = os.path.relpath(sol_file, ROOT)
    theorems = required_theorems(args.mode, os.path.basename(case_path))
    goal_desc = (f"the top-level theorem {theorems[0]!r} is stated and proved"
                 if args.mode == "Lin" else
                 f"the top-level racy theorem {theorems[0]!r} is stated and proved")
    # Mode-specific framing for the CONCEPTUAL half of the summary.
    concept_desc = (
        "insights about the bug, the witness trace, or why it is not "
        "linearizable" if args.mode == "Lin" else
        "insights about the bug, the two conflicting accesses, and why the "
        "schedule is a genuine data race")

    # Front-load the orient phase: inline the docs and the case file that the
    # run would otherwise spend several Read/Grep/Glob round-trips locating, so
    # the model can start authoring immediately. These are all files it is
    # allowed to read anyway; inlining just removes the round-trips (and the
    # growing-context re-billing they cause turn over turn).
    arch_file = os.path.join("src", "ARCHITECTURE.md")
    guide_section = (
        f"=== {proof_guide} (proof guide) ===\n"
        + read_text(os.path.join(ROOT, proof_guide)) + "\n\n")
    inlined = (
        f"=== {arch_file} (project overview) ===\n"
        + read_text(os.path.join(ROOT, arch_file)) + "\n\n"
        + guide_section +
        f"=== {case_file} (the case to verify — do NOT modify) ===\n"
        + read_text(case_path) + "\n\n"
        "=== rocq_start preamble (use verbatim; it is also the import block "
        "your proof file opens with) ===\n"
        + warm_preamble(args.mode, case_path) + "\n"
    )

    # The recurring failure mode is re-deriving what the guide already states
    # by reading framework files, so the prompt fixes what may be looked up
    # where: primitive steps are tactics (fire them), spec statements are on
    # the guide's card or one `About` away in the warm session.
    # Both guides have the same shape (two-tier rule, API card), so one rule;
    # only the primitive steps and the tactic files differ by benchmark.
    primitives, tactic_files = (
        ("fun/rec, calling a lambda, let, seq, match, if, unop/binop, an "
         "applied constructor or tuple, ref, !, <-, CAS, Fork, for) and array "
         "make/get/set",
         "goal_tactics.v, goal_proof.v, atomic_loc.v or array.v")
        if args.mode == "DRB" else
        ("fun/rec, calling a lambda, let, seq, match, if, unop/binop, an "
         "applied constructor or tuple, ref, !, <-, CAS, Fork, for) and "
         "array get/set",
         "goal_tactics.v, goal_proof.v, atomic_loc.v or array.v"))
    lookup_rule = (
        f"Lookup rule: primitive steps ({primitives} are driven ONLY by "
        "the g_* tactics the guide lists; never read "
        f"{tactic_files} to see what a tactic does — fire it and read the "
        "error. The guide's API card prints verbatim the statements of the "
        "common spec lemmas applied by hand; for a lemma absent from it, use "
        "rocq_query (Search/About/Check) on the warm session rather than "
        "reading framework files. Do not grep the "
        "framework to confirm a claim the guide makes. "
    )

    instruction = (
        f"Verify the Coq case file {case_file} by writing a proof to {sol_rel} "
        "— do not modify the case file or weaken/restate any goal. "
        "The project overview (ARCHITECTURE.md), the proof guide, "
        "the case file and the exact rocq_start preamble are inlined at the "
        "end of this message, so you do NOT need to Read or search for them — "
        "start from the inlined content. "
        + lookup_rule
        + restriction +
        # Pin what 'verified' means so the run can be scored objectively.
        "The proof is complete only if: it has no 'admit'/'Admitted' and adds "
        f"no 'Axiom', and {goal_desc}. "
        # Ground truth comes from an MCP whole-file compile, not self-report.
        "As the FINAL step, run the authoritative whole-file check with "
        f"exactly rocq_compile_file(file={sol_rel!r}, workspace={ROOT!r}, "
        "timeout=600): the file path is relative to the workspace and the "
        "workspace must be given, or the project load path is lost. "
        # MCP warm-up: one start, reused for the whole run — avoids the repeated
        # cold rocq_start retries that burn turns/latency.
        "Your FIRST tool call must warm the session EXACTLY ONCE with "
        f"rocq_start(workspace={ROOT!r}, preamble=<the preamble inlined below, "
        "verbatim>); reuse that same warm session for the rest of the run and "
        "do NOT call rocq_start again. Iterate with rocq_check against it "
        "before the final compile. "
        "Then return a short summary: what you did, and — as two clearly "
        "separated groups — the CONCEPTUAL challenges you encountered ("
        + concept_desc + ") and "
        "the TECHNICAL challenges you encountered (the Rocq/tactic/framework "
        "obstacles and how you got past them). End your reply with a "
        "final line that is exactly 'VERDICT: SUCCESS' or 'VERDICT: FAILURE'."
        "\n\n" + inlined
    )

    # PreToolUse hook: this script in --hook mode, guarding file reads.
    settings = {
        # Forbid every kind of persisted memory so nothing carried over from a
        # previous session biases the run: auto-memory off, and all CLAUDE.md
        # files (user, project, local) excluded from discovery. (--setting-sources
        # only governs settings.json; it does not touch memory / CLAUDE.md.)
        "autoMemoryEnabled": False,
        "claudeMdExcludes": [
            "~/.claude/CLAUDE.md",
            "**/CLAUDE.md",
            "**/CLAUDE.local.md",
            "**/.claude/CLAUDE.md",
        ],
        "hooks": {
            "PreToolUse": [
                {
                    "matcher": "Read|Grep|Glob",
                    "hooks": [
                        {
                            "type": "command",
                            "command": f"python3 {os.path.abspath(__file__)} "
                                       "--hook",
                        }
                    ],
                }
            ]
        }
    }

    cmd = [
        "claude",
        "-p",
    ]
    if args.model:
        cmd += ["--model", args.model]
    if args.effort:
        cmd += ["--effort", args.effort]
    cmd += [
        # Stream events line-by-line so progress is visible live; the final
        # "result" event still carries usage/duration for the summary.
        "--output-format", "stream-json",
        "--verbose",
        # Positive allowlist of built-in tools: everything else (Bash, Agent,
        # WebFetch/WebSearch, NotebookEdit, ...) does not exist in the run, so
        # nothing can bypass the read hook by cat-ing a solution, reading git,
        # fetching the repo from the web, or spawning a subagent.
        "--tools", "Read,Write,Edit,Grep,Glob",
        # Pre-authorize proof-file creation and the Rocq MCP so headless mode
        # does not auto-deny them.
        "--allowedTools", "Read", "Write", "Edit", "mcp__rocq",
        # Only the Rocq MCP server from --mcp-config; ignore any other
        # configured MCP servers.
        "--mcp-config", os.path.join(ROOT, ".mcp.json"),
        "--strict-mcp-config",
        # Do not save a resumable session transcript to disk for each replay.
        "--no-session-persistence",
        # Disable user settings but keep hooks (unlike --bare). Memory itself is
        # disabled via the settings above + CLAUDE_CODE_DISABLE_AUTO_MEMORY.
        "--setting-sources", "project,local",
        # Keep --settings last: it takes a single value, so the positional
        # prompt below is not swallowed by a variadic option (e.g. --mcp-config).
        "--settings", json.dumps(settings),
        instruction,
    ]
    # Print the command without the (now large, inlined-docs) prompt so logs
    # and the console stay readable; the prompt itself is not echoed anywhere.
    print("launching:", " ".join(cmd[:-1]),
          f"<prompt: {len(instruction)} chars>")

    env = dict(os.environ, **{ALLOW_ENV: allowed_abs,
                              "CLAUDE_CODE_DISABLE_AUTO_MEMORY": "1"})
    # Activate the local opam switch (like `eval $(opam env)`) so the MCP can
    # find rocq/coqc and resolve dependencies.
    env.update(opam_env())

    # Activate the local venv (like sourcing .venv/bin/activate) so the
    # `rocq-mcp` command is on PATH. Done after opam so venv/bin stays first.
    venv_bin = os.path.join(ROOT, ".venv", "bin")
    if os.path.isdir(venv_bin):
        env["VIRTUAL_ENV"] = os.path.join(ROOT, ".venv")
        env["PATH"] = venv_bin + os.pathsep + env.get("PATH", "")
    else:
        print("warning: .venv not found; rocq-mcp may be unavailable")

    # Optionally tee the raw stream-json (JSONL) to a file for later analysis.
    dump_fh = open(args.dump, "w", encoding="utf-8") if args.dump else None

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True, env=env)
    data = None
    # tool_use id -> tool name, to pair a later tool_result with its call.
    tool_calls = {}
    # Latest MCP compile/verify result on the solution file (ground-truth signal).
    mcp_compile_content = None
    for line in proc.stdout:
        line = line.strip()
        if not line:
            continue
        if dump_fh:
            dump_fh.write(line + "\n")
            dump_fh.flush()
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            print(line, flush=True)  # non-JSON noise: pass through
            continue
        stream_event(event, verbose=args.verbose)
        etype = event.get("type")
        if etype == "assistant":
            for block in event.get("message", {}).get("content", []):
                if block.get("type") == "tool_use":
                    tool_calls[block.get("id")] = block.get("name", "")
        elif etype == "user":
            for block in event.get("message", {}).get("content", []):
                if block.get("type") != "tool_result":
                    continue
                name = tool_calls.get(block.get("tool_use_id"), "")
                if "rocq_compile" not in name and "rocq_verify" not in name:
                    continue
                content = block.get("content", "")
                if isinstance(content, list):
                    content = " ".join(b.get("text", "") for b in content
                                       if isinstance(b, dict))
                mcp_compile_content = str(content)
        if etype == "result":
            data = event
    if dump_fh:
        dump_fh.close()
        print(f"wrote stream to {args.dump}")
    if proc.wait() != 0:
        sys.exit(f"claude exited with status {proc.returncode}")
    if data is None:
        sys.exit("error: no result event received from claude")

    usage = data.get("usage", {})
    in_tok = usage.get("input_tokens", 0)
    out_tok = usage.get("output_tokens", 0)
    cache_r = usage.get("cache_read_input_tokens", 0)
    cache_w = usage.get("cache_creation_input_tokens", 0)
    total = in_tok + out_tok + cache_r + cache_w
    duration_s = data.get("duration_ms", 0) / 1000

    # Self-reported verdict from the final text (trusted least).
    final_text = str(data.get("result", "") or "")
    m = re.search(r"VERDICT:\s*(SUCCESS|FAILURE)", final_text, re.IGNORECASE)
    self_verdict = m.group(1).upper() if m else "UNKNOWN"

    # Ground truth: the MCP whole-file compile result + a static anti-cheat scan.
    mcp_ok = compile_verdict(mcp_compile_content) if mcp_compile_content else None
    cheats, missing = scan_source(sol_file, args.mode, os.path.basename(case_path))

    print("\n--- summary ---")
    print(f"tokens: {total} (in {in_tok}, out {out_tok}, "
          f"cache read {cache_r}, cache write {cache_w})")
    print(f"time:   {duration_s:.1f}s")
    if "total_cost_usd" in data:
        print(f"cost:   ${data['total_cost_usd']:.4f}")

    print("\n--- verdict ---")
    print(f"self-reported: {self_verdict}")
    if mcp_compile_content is None:
        print("mcp compile:   NONE (no rocq_compile_file/rocq_verify observed)")
    else:
        print(f"mcp compile:   "
              f"{'PASS' if mcp_ok else 'FAIL' if mcp_ok is False else 'UNCLEAR'}")
    if cheats:
        print(f"source scan:   CHEAT — found {', '.join(cheats)}")
    elif missing:
        print(f"source scan:   INCOMPLETE — missing theorem(s): {', '.join(missing)}")
    else:
        print("source scan:   clean (no admit/Admitted/Axiom, theorem present)")

    # Overall = MCP compile passed AND nothing cheated/missing in the source.
    verified = (mcp_ok is True) and not cheats and not missing
    print(f"OVERALL:       {'VERIFIED' if verified else 'NOT VERIFIED'}")
    if self_verdict == "SUCCESS" and not verified:
        print("  (warning: Claude claimed success but ground truth disagrees)")
    sys.exit(0 if verified else 1)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--hook":
        sys.exit(run_hook())
    main()
