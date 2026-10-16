#!/usr/bin/env python3
"""Pretty-print a Claude Code session .jsonl, focusing on the input/output
conversation and eliding auxiliary data (raw rocq goal-state dumps, ids, etc.).

Usage:
    python print_session.py SESSION.jsonl [options]

Options:
    --tool-results    show (truncated) tool result bodies (hidden by default)
    --full            do not truncate anything
    --width N         truncation width for elided text (default 500)
"""
import argparse
import json
import os
import sys
import textwrap

# Tools whose output is a big rocq goal-state "prompt" we want to elide.
ROCQ_TOOLS = {"mcp__rocq__rocq_start", "mcp__rocq__rocq_check",
              "mcp__rocq__rocq_compile_file"}

C = {  # ANSI colours; disabled when not a tty
    "user": "\033[1;36m", "asst": "\033[1;32m", "tool": "\033[1;33m",
    "res": "\033[0;90m", "think": "\033[0;35m", "sys": "\033[0;90m",
    "off": "\033[0m",
}


def clip(text, width, full=False):
    text = text if text is not None else ""
    if full or len(text) <= width:
        return text
    return text[:width].rstrip() + f" …[+{len(text) - width} chars]"


def fmt_tool_input(name, inp, width, full):
    """One-line-ish summary of a tool call's arguments."""
    inp = inp or {}
    # Pick the most informative field per tool.
    if name in ("Read", "Write", "Edit"):
        head = inp.get("file_path", "")
    elif name == "Glob":
        head = inp.get("pattern", "")
    elif name == "Grep":
        head = inp.get("pattern", "") + (f"  ({inp['path']})" if inp.get("path") else "")
    elif name in ROCQ_TOOLS:
        body = inp.get("body") or inp.get("preamble") or inp.get("file") or ""
        st = inp.get("from_state")
        prefix = f"[from_state {st}] " if st is not None else ""
        head = prefix + clip(body.strip(), width, full)
    else:
        head = clip(json.dumps(inp, ensure_ascii=False), width, full)
    return head


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("session")
    ap.add_argument("--tool-results", action="store_true")
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--width", type=int, default=500)
    args = ap.parse_args()

    color = sys.stdout.isatty()
    c = C if color else {k: "" for k in C}
    W = args.width

    id2name = {}  # tool_use_id -> tool name, to label/elide tool_results

    with open(os.path.join("run", args.session)) as f:
        records = [json.loads(l) for l in f if l.strip()]

    # First pass: map tool_use ids to names.
    for r in records:
        if r.get("type") == "assistant":
            for blk in r.get("message", {}).get("content", []):
                if blk.get("type") == "tool_use":
                    id2name[blk["id"]] = blk["name"]

    def line(tag, color_key, body):
        print(f"{c[color_key]}{tag}{c['off']} {body}")

    for r in records:
        t = r.get("type")

        if t == "system" and r.get("subtype") == "init":
            model = r.get("model", "?")
            print(f"{c['sys']}── session start · model={model} ──{c['off']}")

        elif t == "user":
            content = r.get("message", {}).get("content")
            if isinstance(content, str):
                print()
                line("USER:", "user", clip(content, W, args.full))
            else:
                for blk in content or []:
                    if blk.get("type") == "tool_result":
                        tid = blk.get("tool_use_id", "")
                        name = id2name.get(tid, "?")
                        text = blk.get("content")
                        if isinstance(text, list):
                            text = "".join(p.get("text", "") for p in text
                                            if isinstance(p, dict))
                        if not args.tool_results:
                            continue
                        if name in ROCQ_TOOLS and not args.full:
                            body = f"[rocq output elided, {len(text or '')} chars]"
                        else:
                            body = clip((text or "").strip(), W, args.full)
                        line(f"  ⤷ result[{name}]:", "res", body)

        elif t == "assistant":
            for blk in r.get("message", {}).get("content", []):
                bt = blk.get("type")
                if bt == "text" and blk.get("text", "").strip():
                    print()
                    line("CLAUDE:", "asst", blk["text"].strip())
                elif bt == "tool_use":
                    line(f"  → {blk['name']}:", "tool",
                         fmt_tool_input(blk["name"], blk.get("input"), W, args.full))

        elif t == "result":
            print()
            print(f"{c['sys']}── result: {r.get('subtype')} "
                  f"({r.get('num_turns')} turns) ──{c['off']}")
            line("FINAL:", "asst", clip(r.get("result", ""), W * 4, args.full))


if __name__ == "__main__":
    main()
