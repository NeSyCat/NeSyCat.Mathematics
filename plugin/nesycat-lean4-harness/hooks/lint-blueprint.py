#!/usr/bin/env python3
"""Implementation for lint-blueprint.sh. Reads the PostToolUse hook JSON
from stdin, and if the touched file is a *.tex file under blueprint/src/,
scans it on disk for editorial-law smells and prints non-blocking
additionalContext reminders. Never raises past main().

This is guidance, not enforcement: the gate lives in
scripts/blueprint.sh's CORRESPONDENCE section. These are instant,
in-the-loop nudges so an agent can fix a smell before it ever reaches the
gate.
"""
import json
import os
import re
import sys

THEOREM_FAMILY_BEGIN_RE = re.compile(
    r'\\begin\{(theorem|proposition|lemma|corollary)\}')
ABBREV_BEGIN_RE = re.compile(r'\\begin\{abbreviation\}')
ABBREV_END_RE = re.compile(r'\\end\{abbreviation\}')
REMARK_BEGIN_RE = re.compile(r'\\begin\{remark\}')
REMARK_END_RE = re.compile(r'\\end\{remark\}')
END_ANY_RE = re.compile(r'\\end\{[a-zA-Z]+\}')
BEGIN_PROOF_RE = re.compile(r'\\begin\{proof\}')
LEAN_RE = re.compile(r'\\lean\{')
USES_REM_RE = re.compile(r'\\uses\{[^}]*\brem:')
DISPLAY_MATH_RE = re.compile(r'\\\[|\\begin\{(align|equation)\*?\}')


def strip_comment(line):
    i, n = 0, len(line)
    while i < n:
        if line[i] == '%' and (i == 0 or line[i - 1] != '\\'):
            return line[:i]
        i += 1
    return line


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

    if not rel_posix.startswith("blueprint/src/") or not rel_posix.endswith(".tex"):
        return

    if not os.path.isfile(abs_path):
        return

    try:
        with open(abs_path, "r", encoding="utf-8", errors="replace") as fh:
            raw_lines = fh.read().splitlines()
    except Exception:
        return

    code_lines = [strip_comment(l) for l in raw_lines]
    n = len(code_lines)
    warnings = []

    # \uses{rem:...} -- strong warning, this is a hard structural violation.
    for idx, line in enumerate(code_lines):
        if USES_REM_RE.search(line):
            warnings.append(
                f"{rel_posix}:{idx + 1}: STRONG WARNING -- \\uses{{rem:...}} "
                "cites a remark; remarks may not be depended on "
                "(scripts/blueprint.sh CORRESPONDENCE will reject this)")

    # abbreviation env without \lean{}; remark containing \lean or display
    # math (promotion candidate).
    idx = 0
    while idx < n:
        if ABBREV_BEGIN_RE.search(code_lines[idx]):
            start = idx
            end = idx
            for j in range(idx, n):
                if ABBREV_END_RE.search(code_lines[j]):
                    end = j
                    break
            body = "\n".join(code_lines[start:end + 1])
            if not LEAN_RE.search(body):
                warnings.append(
                    f"{rel_posix}:{start + 1}: abbreviation environment has "
                    "no \\lean{} name")
            idx = end + 1
            continue
        if REMARK_BEGIN_RE.search(code_lines[idx]):
            start = idx
            end = idx
            for j in range(idx, n):
                if REMARK_END_RE.search(code_lines[j]):
                    end = j
                    break
            body = "\n".join(code_lines[start:end + 1])
            if LEAN_RE.search(body):
                warnings.append(
                    f"{rel_posix}:{start + 1}: remark carries \\lean{{}} -- "
                    "promotion candidate: corollary?")
            elif DISPLAY_MATH_RE.search(body):
                warnings.append(
                    f"{rel_posix}:{start + 1}: remark contains display math "
                    "(\\[ or align/equation) -- promotion candidate: "
                    "corollary?")
            idx = end + 1
            continue
        idx += 1

    # theorem-family \begin{...} without a following \begin{proof} anywhere
    # later in the file (best-effort, whole-file scan; the gate does the
    # precise adjacency check).
    for idx, line in enumerate(code_lines):
        if THEOREM_FAMILY_BEGIN_RE.search(line):
            # Find this env's \end{...}.
            kind = THEOREM_FAMILY_BEGIN_RE.search(line).group(1)
            end_re = re.compile(r'\\end\{' + kind + r'\}')
            end_idx = None
            for j in range(idx, n):
                if end_re.search(code_lines[j]):
                    end_idx = j
                    break
            if end_idx is None:
                continue
            # Skip blank/comment lines after end_idx; check next real line.
            j = end_idx + 1
            while j < n and code_lines[j].strip() == "":
                j += 1
            if j >= n or not BEGIN_PROOF_RE.search(code_lines[j]):
                warnings.append(
                    f"{rel_posix}:{idx + 1}: {kind} environment has no "
                    "\\begin{proof} immediately following")

    if not warnings:
        return

    out = {
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": (
                "lint-blueprint (non-blocking editorial-law reminders):\n"
                + "\n".join(warnings)
            ),
        }
    }
    print(json.dumps(out))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
