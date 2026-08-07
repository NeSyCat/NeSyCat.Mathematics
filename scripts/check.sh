#!/usr/bin/env bash
# scripts/check.sh — fast build/checker feedback loop for the autoformalization harness.
#
# Usage:
#   scripts/check.sh                        # build the whole project
#   scripts/check.sh NeSyCat.Pilot.Sec1_1_Categories   # build one module only
#
# Exits with lake's exit code. Prints a final "CHECK: GREEN" or
# "CHECK: RED (exit <code>)" line so it is easy to grep for in agent logs.

set -uo pipefail

export PATH="$HOME/.elan/bin:$PATH"

# Resolve repo root from this script's location (scripts/check.sh -> repo root).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd)"

cd "$REPO_ROOT" || exit 1

if [ -n "${1:-}" ]; then
  lake build "$1"
else
  lake build
fi
CODE=$?

if [ "$CODE" -eq 0 ]; then
  echo "CHECK: GREEN"
else
  echo "CHECK: RED (exit $CODE)"
fi

exit "$CODE"
