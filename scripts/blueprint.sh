#!/usr/bin/env bash
# scripts/blueprint.sh — end-to-end blueprint build + declaration check +
# blueprint<->Lean CORRESPONDENCE gate.
#
# Builds the pdf and web versions of the blueprint (blueprint/) via
# leanblueprint, then checks that every Lean declaration name referenced
# by a `\lean{...}` macro in the blueprint source actually exists, by
# asking `lake env lean` to `#check` each one. This is done WITHOUT any
# lakefile change (no `checkdecls` dependency): we just grep the names
# out of blueprint/src/*.tex and elaborate a scratch file against the
# NeSyCat library.
#
# It then runs a CORRESPONDENCE section (mechanical enforcement of the
# editorial laws in the blueprint's "Blueprint-to-Lean correspondence"
# paragraph):
#   a. STRUCTURE  — pure text parsing of blueprint/src/content.tex:
#      theorem-family environments are immediately followed by a proof;
#      conjectures never are (and never carry a proof-side \leanok);
#      definition/abbreviation/remark bodies carry no proof/qed
#      argumentation; no \uses{rem:...}; \leanok never appears without a
#      \lean{} in the same item; every abbreviation has >=1 \lean{} name.
#   b. KIND-CHECK — Lean-backed: every \lean name is resolved via
#      `lake env lean` (getConstInfo + isStructure/isClass/isInstance +
#      getReducibilityStatus) and checked against its environment kind
#      (theorem-family needs a theorem-kind name; abbreviation names
#      must be reducible defs; definition items need at least one
#      def/structure/class/instance-kind name — never *only*
#      theorem-kind names).
#   c. REGISTRY SYNC — every `% Lean:`-tagged macro in the sibling
#      NeSyCat.Logics/macros.sty is checked against NeSyCat/Notation.lean
#      (vacuous-ready: prints a "not yet present" note until that file
#      exists).
# The structural/kind-check logic lives in a Python helper generated at
# runtime into a scratch file (mirrors the scratch-.lean-file pattern
# already used by the decl-check section below) — this script remains
# the single versioned entry point.
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

echo "==> CORRESPONDENCE: structure + kind-check"

CORR_PY="$(mktemp "${TMPDIR:-/tmp}/blueprint-correspondence.XXXXXX.py")"
GROUPS_JSONL="$(mktemp "${TMPDIR:-/tmp}/blueprint-groups.XXXXXX.jsonl")"
KIND_LEAN="$(mktemp "${TMPDIR:-/tmp}/blueprint-kindcheck.XXXXXX.lean")"
KIND_OUT="$(mktemp "${TMPDIR:-/tmp}/blueprint-kindcheck.XXXXXX.out")"
trap 'rm -f "$SCRATCH" "$CORR_PY" "$GROUPS_JSONL" "$KIND_LEAN" "$KIND_OUT"' EXIT

cat > "$CORR_PY" << 'CORRESPONDENCE_PY_EOF'
#!/usr/bin/env python3
"""scripts/blueprint.sh CORRESPONDENCE section -- blueprint<->Lean
structural and kind-check enforcement.

Generated into a temp file at runtime by scripts/blueprint.sh (mirrors the
existing scratch-.lean-file pattern used by the decl-check section above);
not a standing repo file.

Modes (argv[1]):
  structure   <content.tex>             -- run all PART-a structural checks;
                                            emit group JSON (one per line, for
                                            the kind-check step) to stdout
                                            prefixed "GROUP\t<json>", and
                                            emit violations prefixed
                                            "VIOL\t<message>". Exit 1 if any
                                            violation was printed, else 0.
  emit-lean   <groups.jsonl>             -- print one #eval block per
                                            distinct name for the kind-check
                                            Lean scratch file.
  check-kinds <groups.jsonl> <lean.out>  -- pair the Lean kind-check output
                                            back up with the groups, apply
                                            the per-env-kind assertions,
                                            print the mapping table, and
                                            report violations. Exit 1 if any.
"""
import json
import re
import sys

THEOREM_FAMILY = {"theorem", "proposition", "lemma", "corollary"}
TARGET_KINDS = THEOREM_FAMILY | {"conjecture", "definition", "abbreviation",
                                  "remark", "proof", "example"}

BEGIN_RE = re.compile(r'\\begin\{([a-zA-Z]+)\}')
END_RE = re.compile(r'\\end\{([a-zA-Z]+)\}')
LABEL_RE = re.compile(r'\\label\{([^}]*)\}')
LEAN_RE = re.compile(r'\\lean\{([^}]*)\}')
LEANOK_RE = re.compile(r'\\leanok\b')
USES_RE = re.compile(r'\\uses\{([^}]*)\}')
PROOF_ARG_RE = re.compile(r'\\begin\{proof\}|\\qed\b')


def strip_comment(line):
    i, n = 0, len(line)
    while i < n:
        if line[i] == '%' and (i == 0 or line[i - 1] != '\\'):
            return line[:i]
        i += 1
    return line


def is_blank_or_comment(line):
    return strip_comment(line).strip() == ""


def parse_envs(code_lines):
    """Return sorted list of (kind, start_idx, end_idx) for TARGET_KINDS,
    matched non-nested (no environment here nests inside a same-kind
    sibling of the tracked kinds -- itemize/enumerate/tabular nested inside
    a body are irrelevant since we search only for the matching
    \\end{SAMEKIND})."""
    n = len(code_lines)
    begins = []
    for idx, line in enumerate(code_lines):
        for m in BEGIN_RE.finditer(line):
            k = m.group(1)
            if k in TARGET_KINDS:
                begins.append((idx, k))
    envs = []
    for (idx, k) in begins:
        for j in range(idx, n):
            m = END_RE.search(code_lines[j])
            if m and m.group(1) == k:
                envs.append((k, idx, j))
                break
    envs.sort(key=lambda e: e[1])
    return envs


def cmd_structure(tex_path):
    with open(tex_path, encoding="utf-8") as f:
        raw_lines = f.readlines()
    code_lines = [strip_comment(l) for l in raw_lines]
    envs = parse_envs(code_lines)

    violations = []
    groups = []  # for kind-check step

    def body_text(s, e):
        return "".join(code_lines[s:e + 1])

    def label_of(s, e):
        m = LABEL_RE.search(body_text(s, e))
        return m.group(1) if m else "<no-label>"

    # 1. theorem-family immediately followed by \begin{proof}; conjecture
    #    never followed by proof.
    for pos, (k, s, e) in enumerate(envs):
        label = label_of(s, e)
        nxt = envs[pos + 1] if pos + 1 < len(envs) else None
        gap_ok = True
        if nxt:
            for gi in range(e + 1, nxt[1]):
                if not is_blank_or_comment(raw_lines[gi]):
                    gap_ok = False
                    break
        if k in THEOREM_FAMILY:
            has_proof_next = bool(nxt) and nxt[0] == "proof" and gap_ok
            if not has_proof_next:
                violations.append(
                    f"line {s + 1} ({k} {label}): theorem-family environment "
                    "not immediately followed by \\begin{proof}")
        if k == "conjecture":
            if nxt and nxt[0] == "proof" and gap_ok:
                violations.append(
                    f"line {s + 1} (conjecture {label}): conjecture is "
                    "immediately followed by \\begin{proof} (conjectures "
                    "must stay unproved)")
                proof_body = body_text(nxt[1], nxt[2])
                if LEANOK_RE.search(proof_body):
                    violations.append(
                        f"line {s + 1} (conjecture {label}): its proof "
                        "carries \\leanok")

    # 2. no Proof/qed argumentation inside definition/abbreviation/remark
    #    bodies.
    for (k, s, e) in envs:
        if k in ("definition", "abbreviation", "remark"):
            if PROOF_ARG_RE.search(body_text(s, e)):
                violations.append(
                    f"line {s + 1} ({k} {label_of(s, e)}): body contains "
                    "proof/qed argumentation (\\begin{proof} or \\qed)")

    # 3. zero \uses{rem:...} anywhere.
    for idx, line in enumerate(code_lines):
        for m in USES_RE.finditer(line):
            items = [it.strip() for it in m.group(1).split(',')]
            for it in items:
                if it.startswith("rem:"):
                    violations.append(
                        f"line {idx + 1}: \\uses{{...}} cites remark "
                        f"'{it}' (remarks may not be depended on)")

    # 4. \leanok never appears in an environment with no \lean{} (statement
    #    side); combine a theorem-family environment with its immediately
    #    following proof (if the structural check above found one) so a
    #    proof-side-only \leanok is still backed by the statement's
    #    \lean{}.
    for pos, (k, s, e) in enumerate(envs):
        if k not in (THEOREM_FAMILY | {"conjecture", "definition",
                                        "abbreviation", "remark",
                                        "example"}):
            continue
        span_end = e
        if k in THEOREM_FAMILY:
            nxt = envs[pos + 1] if pos + 1 < len(envs) else None
            if nxt and nxt[0] == "proof":
                gap_ok = all(is_blank_or_comment(raw_lines[gi])
                             for gi in range(e + 1, nxt[1]))
                if gap_ok:
                    span_end = nxt[2]
        text = body_text(s, span_end)
        if LEANOK_RE.search(text) and not LEAN_RE.search(text):
            violations.append(
                f"line {s + 1} ({k} {label_of(s, e)}): \\leanok present "
                "with no \\lean{} in the same item")

    # 5. every abbreviation environment has >=1 \lean{} name.
    for (k, s, e) in envs:
        if k == "abbreviation":
            names = []
            for m in LEAN_RE.finditer(body_text(s, e)):
                names.extend(x.strip() for x in m.group(1).split(',')
                             if x.strip())
            if not names:
                violations.append(
                    f"line {s + 1} (abbreviation {label_of(s, e)}): no "
                    "\\lean{} name")

    # Build groups for the kind-check step (theorem-family, definition,
    # abbreviation, conjecture only -- these are the kinds part (b)
    # checks).
    for (k, s, e) in envs:
        fam = "theorem-family" if k in THEOREM_FAMILY else k
        if fam not in ("theorem-family", "definition", "abbreviation",
                       "conjecture", "example"):
            continue
        names = []
        for m in LEAN_RE.finditer(body_text(s, e)):
            names.extend(x.strip() for x in m.group(1).split(',')
                         if x.strip())
        groups.append({
            "kind": fam, "raw_kind": k, "label": label_of(s, e),
            "line": s + 1, "names": names,
        })

    for g in groups:
        print("GROUP\t" + json.dumps(g))
    for v in violations:
        print("VIOL\t" + v)

    n_envs = len([e for e in envs if e[0] != "proof"])
    print(f"STRUCTURE-SUMMARY\t{n_envs} environments scanned, "
          f"{len(violations)} violation(s)")

    return 1 if violations else 0


def cmd_emit_lean(groups_path):
    names = []
    seen = set()
    with open(groups_path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.startswith("GROUP\t"):
                continue
            g = json.loads(line[len("GROUP\t"):])
            for nm in g["names"]:
                if nm not in seen:
                    seen.add(nm)
                    names.append(nm)
    print("import NeSyCat")
    print()
    print("open Lean Meta")
    print()
    print("def blueprintKindOf (n : Name) : MetaM String := do")
    print("  let env <- getEnv")
    print("  match env.find? n with")
    print("  | none => pure \"NOT-FOUND\"")
    print("  | some info => do")
    print("    let base :=")
    print("      match info with")
    print("      | .thmInfo _ => \"theorem\"")
    print("      | .axiomInfo _ => \"axiom\"")
    print("      | .opaqueInfo _ => \"opaque\"")
    print("      | .ctorInfo _ => \"constructor\"")
    print("      | .recInfo _ => \"recursor\"")
    print("      | .quotInfo _ => \"quot\"")
    print("      | .inductInfo _ => if isStructure env n then \"structure\""
          " else \"inductive\"")
    print("      | .defnInfo _ => \"def\"")
    print("    let mut kind := base")
    print("    if base == \"def\" then")
    print("      let inst <- isInstance n")
    print("      if inst then kind := \"instance\"")
    print("      else if isClass env n then kind := \"class\"")
    print("      else if isStructure env n then kind := \"structure\"")
    print("    let red <- getReducibilityStatus n")
    print("    let redStr := if red matches .reducible then \"reducible\" "
          "else if red matches .irreducible then \"irreducible\" else "
          "\"regular\"")
    print("    pure s!\"{kind}|{redStr}\"")
    print()
    # The flat do-block's elaboration depth grows linearly with the name
    # count; the default maxRecDepth (512) tops out near ~123 names
    # (hit at 163 names during C2-T4). Raised with ample headroom.
    print("set_option maxRecDepth 8000 in")
    print("#eval show MetaM Unit from do")
    for nm in names:
        print(f"  IO.println (s!\"KIND\\t{nm}\\t\" ++ "
              f"(<- blueprintKindOf `{nm}))")


def cmd_check_kinds(groups_path, lean_out_path):
    groups = []
    with open(groups_path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("GROUP\t"):
                groups.append(json.loads(line[len("GROUP\t"):]))

    kind_of = {}
    with open(lean_out_path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.startswith("KIND\t"):
                continue
            _, name, rest = line.split("\t", 2)
            leankind, _, red = rest.partition("|")
            kind_of[name] = (leankind, red)

    violations = []
    print(f"{'name':45} {'blueprint-kind':15} {'lean-kind':12} "
          "reducibility")
    print("-" * 90)
    for g in groups:
        for nm in g["names"]:
            lk, red = kind_of.get(nm, ("MISSING", "-"))
            print(f"{nm:45} {g['kind']:15} {lk:12} {red}")
            if lk == "MISSING" or lk == "NOT-FOUND":
                violations.append(
                    f"{g['kind']} {g['label']} (line {g['line']}): "
                    f"\\lean name '{nm}' not found by kind-check")

    for g in groups:
        kinds_here = [kind_of.get(nm, ("MISSING", "-"))[0]
                      for nm in g["names"]]
        reds_here = [kind_of.get(nm, ("MISSING", "-"))[1]
                     for nm in g["names"]]
        if not g["names"]:
            continue
        if g["kind"] == "theorem-family":
            if "theorem" not in kinds_here:
                violations.append(
                    f"theorem-family {g['label']} (line {g['line']}): none "
                    f"of its \\lean names ({', '.join(g['names'])}) is "
                    "theorem-kind")
        elif g["kind"] == "abbreviation":
            for nm, lk, red in zip(g["names"], kinds_here, reds_here):
                if lk != "def" or red != "reducible":
                    violations.append(
                        f"abbreviation {g['label']} (line {g['line']}): "
                        f"\\lean name '{nm}' is {lk}/{red}, expected a "
                        "reducible def (abbrev)")
        elif g["kind"] == "definition":
            non_theorem = [lk for lk in kinds_here
                           if lk in ("def", "structure", "class",
                                     "instance")]
            if not non_theorem:
                violations.append(
                    f"definition {g['label']} (line {g['line']}): all of "
                    f"its \\lean names ({', '.join(g['names'])}) are "
                    "theorem-kind -- a definition item needs at least one "
                    "def/structure/class/instance-kind declaration")
        elif g["kind"] == "example":
            non_theorem = [lk for lk in kinds_here
                           if lk in ("def", "structure", "class",
                                     "instance")]
            if not non_theorem:
                violations.append(
                    f"example {g['label']} (line {g['line']}): all of "
                    f"its \\lean names ({', '.join(g['names'])}) are "
                    "theorem-kind -- an example item needs at least one "
                    "def/structure/class/instance-kind declaration "
                    "(typically an instance)")
        elif g["kind"] == "conjecture":
            pass  # any kind acceptable; no-proof-leanok already checked
            # structurally.

    for v in violations:
        print("VIOL\t" + v)

    n_names = len({nm for g in groups for nm in g["names"]})
    print(f"KIND-CHECK-SUMMARY\t{n_names} names kind-checked, "
          f"{len(violations)} violation(s)")
    return 1 if violations else 0


def main():
    if len(sys.argv) < 2:
        print("usage: correspondence.py <structure|emit-lean|check-kinds>"
              " ...", file=sys.stderr)
        return 2
    mode = sys.argv[1]
    if mode == "structure":
        return cmd_structure(sys.argv[2])
    if mode == "emit-lean":
        return cmd_emit_lean(sys.argv[2])
    if mode == "check-kinds":
        return cmd_check_kinds(sys.argv[2], sys.argv[3])
    print(f"unknown mode: {mode}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
CORRESPONDENCE_PY_EOF

command -v python3 >/dev/null 2>&1 || fail 127

# A literal tab, for portable grep/sed matching against the "TAG\tpayload"
# lines the Python helper prints (avoid relying on \t being interpreted as
# a tab by whichever grep/sed happens to be first on PATH).
TAB="$(printf '\t')"

STRUCT_OUT="$(python3 "$CORR_PY" structure blueprint/src/content.tex)" || true
STRUCT_STATUS=0
printf '%s\n' "$STRUCT_OUT" | grep -q "^VIOL${TAB}" && STRUCT_STATUS=1
printf '%s\n' "$STRUCT_OUT" | grep "^GROUP${TAB}" > "$GROUPS_JSONL" || true

N_ENVS="$(printf '%s\n' "$STRUCT_OUT" | grep "^STRUCTURE-SUMMARY${TAB}" | sed -E "s/^STRUCTURE-SUMMARY${TAB}([0-9]+).*/\\1/")"

if [ "$STRUCT_STATUS" -ne 0 ]; then
  echo "CORRESPONDENCE structural violations:"
  printf '%s\n' "$STRUCT_OUT" | grep "^VIOL${TAB}" | sed -E "s/^VIOL${TAB}/  - /"
  fail 1
fi
echo "structure: OK ($N_ENVS environments scanned)"

python3 "$CORR_PY" emit-lean "$GROUPS_JSONL" > "$KIND_LEAN"
export PATH="$HOME/.elan/bin:$PATH"
if ! lake env lean "$KIND_LEAN" > "$KIND_OUT" 2>&1; then
  echo "CORRESPONDENCE kind-check: Lean elaboration failed:"
  cat "$KIND_OUT"
  fail 1
fi

CHECK_OUT="$(python3 "$CORR_PY" check-kinds "$GROUPS_JSONL" "$KIND_OUT")" || true
CHECK_STATUS=0
printf '%s\n' "$CHECK_OUT" | grep -q "^VIOL${TAB}" && CHECK_STATUS=1

printf '%s\n' "$CHECK_OUT" | grep -v "^VIOL${TAB}" | grep -v "^KIND-CHECK-SUMMARY${TAB}"

N_NAMES="$(printf '%s\n' "$CHECK_OUT" | grep "^KIND-CHECK-SUMMARY${TAB}" | sed -E "s/^KIND-CHECK-SUMMARY${TAB}([0-9]+).*/\\1/")"

if [ "$CHECK_STATUS" -ne 0 ]; then
  echo "CORRESPONDENCE kind-check violations:"
  printf '%s\n' "$CHECK_OUT" | grep "^VIOL${TAB}" | sed -E "s/^VIOL${TAB}/  - /"
  fail 1
fi
echo "kind-check: OK ($N_NAMES names)"

echo "==> registry sync (macros.sty <-> NeSyCat/Notation.lean)"
MACROS_STY="$REPO_ROOT/../NeSyCat.Logics/macros.sty"
NOTATION_LEAN="$REPO_ROOT/NeSyCat/Notation.lean"
if [ ! -f "$MACROS_STY" ]; then
  echo "registry sync: macros.sty not found at $MACROS_STY (sibling repo not checked out here; skipping)"
else
  TWINS=()
  while IFS= read -r line; do
    [ -n "$line" ] && TWINS+=("$line")
  done < <(
    grep "Lean:" "$MACROS_STY" \
      | grep -oE '\\(new|provide)command\{?\\[A-Za-z]+' \
      | sed -E 's/^.*\\(new|provide)command\{?//'
  )
  if [ ! -f "$NOTATION_LEAN" ]; then
    echo "registry sync: Notation.lean not yet present (${#TWINS[@]} planned twins recorded: ${TWINS[*]})"
  else
    MISSING=()
    for t in "${TWINS[@]}"; do
      grep -qF -- "$t" "$NOTATION_LEAN" || MISSING+=("$t")
    done
    if [ "${#MISSING[@]}" -gt 0 ]; then
      echo "registry sync: FAILED -- macros.sty twins missing from Notation.lean: ${MISSING[*]}"
      fail 1
    fi
    echo "registry sync: OK (${#TWINS[@]} twins found in Notation.lean)"
  fi
fi

echo "CORRESPONDENCE: OK ($N_ENVS environments, $N_NAMES names kind-checked)"

echo "BLUEPRINT: GREEN"
