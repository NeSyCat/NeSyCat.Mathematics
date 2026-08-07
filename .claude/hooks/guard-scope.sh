#!/usr/bin/env bash
# .claude/hooks/guard-scope.sh — PreToolUse guard for Edit|Write.
#
# Enforces FORMALIZE.md's scope rail mechanically: certain paths must
# never be touched by an autoformalization session. In grind mode
# (unattended looping) violations are denied outright; otherwise they
# fall back to a human "ask" gate. NeSyCat.lean gets a reminder instead
# of a block, since it may legitimately gain new import lines.
#
# Reads the PreToolUse hook JSON on stdin, emits at most one JSON object
# on stdout, and always exits 0 (a guard that crashes must not become an
# unconditional block).

set -uo pipefail

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

command -v python3 >/dev/null 2>&1 || exit 0

python3 "$SCRIPT_DIR/guard-scope.py" "$PROJECT_DIR"

exit 0
