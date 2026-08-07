#!/usr/bin/env bash
# .claude/hooks/lint-lean.sh — PostToolUse for Edit|Write.
#
# After a Lean file under NeSyCat/ is touched, scans the file on disk for
# FORMALIZE.md hard bans (axiom, native_decide) and for `sorry` lacking an
# adjacent `-- TODO:` comment. Hard bans block; a bare sorry only gets a
# reminder. Always exits 0.

set -uo pipefail

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

command -v python3 >/dev/null 2>&1 || exit 0

python3 "$SCRIPT_DIR/lint-lean.py" "$PROJECT_DIR"

exit 0
