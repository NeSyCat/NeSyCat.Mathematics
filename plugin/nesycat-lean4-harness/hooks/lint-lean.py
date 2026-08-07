#!/usr/bin/env python3
"""Implementation for lint-lean.sh. Reads the PostToolUse hook JSON from
stdin, and if the touched file is a *.lean file under NeSyCat/, scans the
file on disk for FORMALIZE.md hard bans (axiom, native_decide) and for a
bare `sorry` lacking an adjacent `-- TODO:` comment. Never raises past
main()."""
import json
import os
import re
import sys

SORRY_RE = re.compile(r"(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)")
COMMENT_SORRY_RE = re.compile(r"^--.*sorry")
COMMENT_RE = re.compile(r"^--")
AXIOM_RE = re.compile(r"^[ \t]*(private[ \t]+|protected[ \t]+)?axiom[ \t]")
NATIVE_DECIDE_RE = re.compile(r"(^|[^A-Za-z0-9_])native_decide([^A-Za-z0-9_]|$)")
TODO_RE = re.compile(r"--.*TODO")


def main():
    if len(sys.argv) < 2:
        return
    project_dir = sys.argv[1]

    try:
        data = json.load(sys.stdin)
    except Exception:
        return

    file_path = (data.get("tool_input") or {}).get("file_path")
    if not file_path:
        return

    if not os.path.isabs(file_path):
        abs_path = os.path.normpath(os.path.join(project_dir, file_path))
    else:
        abs_path = os.path.normpath(file_path)

    project_dir_norm = os.path.normpath(project_dir)
    try:
        rel_path = os.path.relpath(abs_path, project_dir_norm)
    except ValueError:
        return
    rel_posix = rel_path.replace(os.sep, "/")

    if not rel_posix.startswith("NeSyCat/") or not rel_posix.endswith(".lean"):
        return

    if not os.path.isfile(abs_path):
        return

    try:
        with open(abs_path, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.read().splitlines()
    except Exception:
        return

    hard_bans = []  # list of "line N: detail"
    sorry_lines = []  # line numbers with sorry-but-no-TODO

    for idx, line in enumerate(lines):
        line_no = idx + 1
        trimmed = line.strip()
        is_comment_line = bool(COMMENT_RE.match(trimmed))

        # axiom / native_decide: skip pure comment lines.
        if not is_comment_line:
            if AXIOM_RE.match(line):
                hard_bans.append(f"{rel_posix}:{line_no}: axiom -- {trimmed}")
            elif NATIVE_DECIDE_RE.search(line):
                hard_bans.append(f"{rel_posix}:{line_no}: native_decide -- {trimmed}")

        # sorry: skip pure line-comments mentioning sorry.
        if COMMENT_SORRY_RE.match(trimmed):
            continue
        if SORRY_RE.search(line):
            same = bool(TODO_RE.search(line))
            prev_line = lines[idx - 1] if idx - 1 >= 0 else ""
            next_line = lines[idx + 1] if idx + 1 < len(lines) else ""
            adjacent = bool(TODO_RE.search(prev_line)) or bool(TODO_RE.search(next_line))
            if not (same or adjacent):
                sorry_lines.append(f"{rel_posix}:{line_no}")

    if hard_bans:
        detail = "; ".join(hard_bans)
        out = {
            "decision": "block",
            "reason": f"FORMALIZE.md hard ban violated: {detail}",
        }
        print(json.dumps(out))
        return

    if sorry_lines:
        out = {
            "hookSpecificOutput": {
                "hookEventName": "PostToolUse",
                "additionalContext": (
                    "Reminder: every sorry needs an adjacent -- TODO: note "
                    f"(FORMALIZE.md sorry policy). Found at: {', '.join(sorry_lines)}"
                ),
            }
        }
        print(json.dumps(out))
        return

    # else: silent.


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
