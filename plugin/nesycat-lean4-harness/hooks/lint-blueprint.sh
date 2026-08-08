#!/usr/bin/env bash
# .claude/hooks/lint-blueprint.sh — PostToolUse for Edit|Write.
#
# After a blueprint/src/*.tex file is touched, scans it on disk for
# editorial-law smells (markless abbreviation, promotion-candidate
# remark, \uses{rem:...}, proofless theorem-family environment) and
# emits non-blocking additionalContext reminders. The gate lives in
# scripts/blueprint.sh's CORRESPONDENCE section -- this hook only
# advises. Always exits 0.

set -uo pipefail

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

command -v python3 >/dev/null 2>&1 || exit 0

python3 "$SCRIPT_DIR/lint-blueprint.py" "$PROJECT_DIR"

exit 0
