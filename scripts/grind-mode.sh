#!/usr/bin/env bash
# scripts/grind-mode.sh — arm/disarm/inspect grind mode.
#
# Grind mode makes the Stop hook (.claude/hooks/grind-stop.sh) re-prompt
# the agent to keep working through the FORMALIZE.md work loop instead of
# stopping, for a bounded number of iterations. State lives in
# .claude/grind-mode (a single integer: remaining iterations); it is
# gitignored and local to a checkout.
#
# Usage:
#   scripts/grind-mode.sh N      # arm for N iterations (1 <= N <= 50)
#   scripts/grind-mode.sh off    # disarm
#   scripts/grind-mode.sh        # print current state

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd)"
STATE_FILE="$REPO_ROOT/.claude/grind-mode"

ARG="${1:-}"

if [ -z "$ARG" ]; then
  if [ -f "$STATE_FILE" ]; then
    REMAINING="$(cat "$STATE_FILE" 2>/dev/null)"
    echo "grind-mode: ARMED (${REMAINING} iterations remaining)."
  else
    echo "grind-mode: disarmed."
  fi
  exit 0
fi

if [ "$ARG" = "off" ]; then
  rm -f "$STATE_FILE"
  echo "grind-mode: disarmed."
  exit 0
fi

case "$ARG" in
  ''|*[!0-9]*)
    echo "grind-mode: error: '$ARG' is not a positive integer. Usage: scripts/grind-mode.sh N|off" >&2
    exit 1
    ;;
esac

if [ "$ARG" -lt 1 ] || [ "$ARG" -gt 50 ]; then
  echo "grind-mode: error: N must satisfy 1 <= N <= 50 (got $ARG)." >&2
  exit 1
fi

mkdir -p "$REPO_ROOT/.claude"
printf '%s' "$ARG" > "$STATE_FILE"

cat <<EOF
grind-mode: ARMED for $ARG iterations.

How it works: the Stop hook (.claude/hooks/grind-stop.sh) will block each
attempt to stop, re-prompting the agent to re-read FORMALIZE.md and
continue the work loop (pick next item, implement, check, commit), once
per remaining iteration. The counter decrements on every Stop event until
it is exhausted, after which the session is allowed to stop normally.

Disarm anytime: scripts/grind-mode.sh off
EOF
