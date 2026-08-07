#!/usr/bin/env bash
# .claude/hooks/session-start.sh — SessionStart hook.
#
# Emits a compact status digest (PROGRESS.md + sorry-report summary +
# recent git log + grind-mode arming state) as additionalContext, so a
# fresh session doesn't have to re-run the resume protocol commands by
# hand. Must complete fast (no lake build) and must never break session
# start: on any internal error, emit nothing and exit 0.

set -uo pipefail

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"

command -v python3 >/dev/null 2>&1 || exit 0

{
  cd "$PROJECT_DIR" || exit 0

  PROGRESS_CONTENT=""
  if [ -f "PROGRESS.md" ]; then
    PROGRESS_CONTENT="$(cat PROGRESS.md 2>/dev/null)"
  fi

  SORRY_SUMMARY=""
  if [ -x "scripts/sorry-report.sh" ]; then
    SORRY_SUMMARY="$(scripts/sorry-report.sh 2>/dev/null | awk '/^=== Summary ===/{flag=1} flag')"
  fi

  GIT_LOG=""
  if command -v git >/dev/null 2>&1; then
    GIT_LOG="$(git log --oneline -10 2>/dev/null)"
  fi

  GRIND_LINE="Grind mode: disarmed."
  if [ -f ".claude/grind-mode" ]; then
    REMAINING="$(cat .claude/grind-mode 2>/dev/null)"
    GRIND_LINE="Grind mode: ARMED (${REMAINING} iterations remaining)."
  fi

  CONTEXT="Formalization harness status:

## PROGRESS.md
${PROGRESS_CONTENT}

## sorry-report.sh summary
${SORRY_SUMMARY}

## git log --oneline -10
${GIT_LOG}

${GRIND_LINE}"

  python3 - "$CONTEXT" <<'PYEOF'
import json
import sys

context = sys.argv[1]
out = {
    "hookSpecificOutput": {
        "hookEventName": "SessionStart",
        "additionalContext": context,
    }
}
print(json.dumps(out))
PYEOF
} 2>/dev/null

exit 0
