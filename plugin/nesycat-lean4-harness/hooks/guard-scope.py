#!/usr/bin/env python3
"""Implementation for guard-scope.sh. Reads the PreToolUse hook JSON from
stdin, decides allow/ask/deny for Edit|Write against FORMALIZE.md's scope
rail, and prints at most one JSON object. Never raises past main()."""
import json
import os
import sys


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
        rel_path = abs_path

    rel_posix = rel_path.replace(os.sep, "/")

    protected_exact = {
        "lakefile.toml",
        "lean-toolchain",
        "lake-manifest.json",
        ".gitignore",
        "FORMALIZE.md",
        "CLAUDE.md",
    }
    protected_prefixes = (
        "scripts/",
        "target/",
        "references/",
        ".github/",
        ".claude/",
        ".foreman/",
    )

    is_protected = rel_posix in protected_exact or any(
        rel_posix.startswith(p) for p in protected_prefixes
    )

    def emit(decision, reason, extra_context=None):
        out = {
            "hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": decision,
                "permissionDecisionReason": reason,
            }
        }
        if extra_context:
            out["hookSpecificOutput"]["additionalContext"] = extra_context
        print(json.dumps(out))

    if is_protected:
        grind_mode_file = os.path.join(project_dir, ".claude", "grind-mode")
        reason = f"FORMALIZE.md scope rail: {rel_posix} is protected during grind mode"
        if os.path.exists(grind_mode_file):
            emit("deny", reason)
        else:
            emit("ask", reason)
    elif rel_posix == "NeSyCat.lean":
        emit(
            "allow",
            "NeSyCat.lean may only gain new import lines",
            "Reminder (FORMALIZE.md scope rail): only new `import NeSyCat.Pilot.*` "
            "lines may be added to NeSyCat.lean.",
        )
    # else: normal flow, emit nothing.


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
