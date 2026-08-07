#!/usr/bin/env bash
# scripts/sorry-report.sh — scans .lean files for `sorry` scaffolding and hard
# policy violations (axiom declarations, native_decide). This script REPORTS,
# it does not gate: it always exits 0.
#
# Usage:
#   scripts/sorry-report.sh [directory]     # defaults to NeSyCat/

set -uo pipefail

DIR="${1:-NeSyCat/}"

if [ ! -d "$DIR" ]; then
  echo "sorry-report: directory '$DIR' does not exist, nothing to scan."
  exit 0
fi

FILES=$(find "$DIR" -type f -name '*.lean' | sort)

if [ -z "$FILES" ]; then
  echo "sorry-report: no .lean files found under '$DIR'."
  echo ""
  echo "=== Summary ==="
  echo "Total sorry count: 0"
  echo "Violation count: 0"
  exit 0
fi

TOTAL_SORRY=0
TOTAL_VIOLATIONS=0

echo "=== sorry occurrences ==="
declare -a FILE_COUNTS
FILE_COUNT_LINES=""

DECL_NAME_RE='^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+)*(theorem|lemma|def|instance|example)[[:space:]]+([A-Za-z_][A-Za-z0-9_.'"'"']*)'
DECL_ANON_RE='^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+)*(example)([[:space:]:]|$)'
SORRY_RE='(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)'
COMMENT_SORRY_RE='^--.*sorry'
COMMENT_RE='^--'
AXIOM_RE='^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]'
NATIVE_DECIDE_RE='(^|[^A-Za-z0-9_])native_decide([^A-Za-z0-9_]|$)'

for f in $FILES; do
  # Walk the file, tracking the nearest preceding declaration name.
  file_sorry_count=0
  last_decl="<none>"
  line_no=0
  while IFS= read -r line || [ -n "$line" ]; do
    line_no=$((line_no + 1))

    # Track nearest preceding theorem|lemma|def|instance|example.
    if [[ "$line" =~ $DECL_NAME_RE ]]; then
      last_decl="${BASH_REMATCH[2]} ${BASH_REMATCH[3]}"
    elif [[ "$line" =~ $DECL_ANON_RE ]]; then
      last_decl="example <anonymous>"
    fi

    # Report sorry occurrences (word-boundary match), skipping pure comment lines.
    trimmed="$(echo "$line" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"
    if [[ "$trimmed" =~ $COMMENT_SORRY_RE ]]; then
      : # pure line-comment mentioning sorry: not scaffolding, skip
    elif [[ "$line" =~ $SORRY_RE ]]; then
      echo "$f:$line_no: $trimmed  [in: $last_decl]"
      file_sorry_count=$((file_sorry_count + 1))
      TOTAL_SORRY=$((TOTAL_SORRY + 1))
    fi

    # VIOLATION: real axiom declarations (not comments).
    if [[ "$trimmed" =~ $COMMENT_RE ]]; then
      : # comment line, not a real declaration
    elif [[ "$line" =~ $AXIOM_RE ]]; then
      echo "$f:$line_no: VIOLATION: axiom -- $trimmed"
      TOTAL_VIOLATIONS=$((TOTAL_VIOLATIONS + 1))
    elif [[ "$line" =~ $NATIVE_DECIDE_RE ]]; then
      echo "$f:$line_no: VIOLATION: native_decide -- $trimmed"
      TOTAL_VIOLATIONS=$((TOTAL_VIOLATIONS + 1))
    fi
  done < "$f"

  if [ "$file_sorry_count" -gt 0 ]; then
    FILE_COUNT_LINES="${FILE_COUNT_LINES}${f}: ${file_sorry_count}
"
  fi
done

echo ""
echo "=== Per-file sorry counts ==="
if [ -n "$FILE_COUNT_LINES" ]; then
  printf '%s' "$FILE_COUNT_LINES"
else
  echo "(none)"
fi

echo ""
echo "=== Summary ==="
echo "Total sorry count: $TOTAL_SORRY"
echo "Violation count: $TOTAL_VIOLATIONS"

exit 0
