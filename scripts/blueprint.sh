#!/usr/bin/env bash
# scripts/blueprint.sh — end-to-end blueprint build + declaration check.
#
# Builds the pdf and web versions of the blueprint (blueprint/) via
# leanblueprint, then checks that every Lean declaration name referenced
# by a `\lean{...}` macro in the blueprint source actually exists, by
# asking `lake env lean` to `#check` each one. This is done WITHOUT any
# lakefile change (no `checkdecls` dependency): we just grep the names
# out of blueprint/src/*.tex and elaborate a scratch file against the
# NeSyCat library.
#
# Usage:
#   scripts/blueprint.sh
#
# Prints a final "BLUEPRINT: GREEN" or "BLUEPRINT: RED (exit <code>)"
# line so it is easy to grep for in agent logs (mirrors scripts/check.sh).

set -euo pipefail

# Resolve repo root from this script's location (scripts/blueprint.sh -> repo root).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd)"

cd "$REPO_ROOT"

LEANBLUEPRINT="$HOME/.venvs/leanblueprint/bin/leanblueprint"

fail() {
  local code="$1"
  echo "BLUEPRINT: RED (exit $code)"
  exit "$code"
}

# leanblueprint's `web` subcommand shells out to `plastex` by bare name, so
# the venv's bin directory must be on PATH (not just invoked via full path).
export PATH="$HOME/.venvs/leanblueprint/bin:/Library/TeX/texbin:$PATH"

echo "==> leanblueprint pdf"
"$LEANBLUEPRINT" pdf || fail $?

echo "==> leanblueprint web"
"$LEANBLUEPRINT" web || fail $?

echo "==> declaration check (grep-based, no lakefile change)"
# Portable array-fill (avoids `mapfile`, which macOS's stock bash 3.2 lacks).
DECL_NAMES=()
while IFS= read -r line; do
  [ -n "$line" ] && DECL_NAMES+=("$line")
done < <(
  grep -hoE '\\lean\{[^}]*\}' blueprint/src/*.tex 2>/dev/null \
    | sed -E 's/\\lean\{([^}]*)\}/\1/' \
    | tr ',' '\n' \
    | sed -E 's/^[[:space:]]+|[[:space:]]+$//g' \
    | sed '/^$/d' \
    | sort -u
)

if [ "${#DECL_NAMES[@]}" -eq 0 ]; then
  echo "No \\lean{...} declarations found in blueprint/src — vacuous pass."
else
  SCRATCH="$(mktemp "${TMPDIR:-/tmp}/blueprint-decl-check.XXXXXX.lean")"
  trap 'rm -f "$SCRATCH"' EXIT

  {
    echo "import NeSyCat"
    for name in "${DECL_NAMES[@]}"; do
      echo "#check $name"
    done
  } > "$SCRATCH"

  export PATH="$HOME/.elan/bin:$PATH"

  echo "Checking ${#DECL_NAMES[@]} declaration(s): ${DECL_NAMES[*]}"
  lake env lean "$SCRATCH" || fail $?
fi

echo "BLUEPRINT: GREEN"
