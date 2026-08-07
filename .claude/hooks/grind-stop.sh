#!/usr/bin/env bash
# .claude/hooks/grind-stop.sh — Stop hook implementing Urban's re-prompting
# loop natively.
#
# State file .claude/grind-mode holds a single integer: remaining
# iterations. Absent -> not armed, do nothing. Otherwise decrement and
# re-block (re-prompt the agent to keep working) until exhausted, with a
# loop-safety escape hatch via stop_hook_active.

set -uo pipefail

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"
STATE_FILE="$PROJECT_DIR/.claude/grind-mode"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

if [ ! -f "$STATE_FILE" ]; then
  exit 0
fi

command -v python3 >/dev/null 2>&1 || exit 0

python3 "$SCRIPT_DIR/grind-stop.py" "$STATE_FILE"

exit 0
