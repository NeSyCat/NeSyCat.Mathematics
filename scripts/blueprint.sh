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
#      theorem-family (lemma/theorem) environments are immediately
#      followed by a proof, INCLUDING an open theorem, whose proof body
#      is then required to be exactly the open marker "Open." with no
#      proof-side \leanok (C2-E4a open-theorem convention: an open
#      theorem is a theorem env with an "Open." proof, never its own
#      environment kind); definition/class/instance/abbreviation bodies
#      carry no proof/qed argumentation; no \uses{rem:...}; \leanok
#      never appears without a \lean{} in the same item; every
#      abbreviation has >=1 \lean{} name; the full env inventory is
#      EXACTLY definition/class/instance/abbreviation/lemma/theorem
#      (+proof) — remark/proposition/corollary/example/conjecture are
#      ABOLISHED (C2-E3 + C2-E4a full Lean-kind-sync decree: the
#      document is formal envs floating in continuous prose; every
#      worked instance is either an `instance` environment witnessing a
#      class, or plain narrative prose) and any surviving occurrence of
#      one is a HARD gate violation, not silently invisible.
#   b. KIND-CHECK — Lean-backed: every \lean name is resolved via
#      `lake env lean` (getConstInfo + isStructure/isClass/isInstance +
#      getReducibilityStatus) and checked against its environment kind
#      (theorem-family needs a theorem-kind name; abbreviation names
#      must be reducible defs; a `definition` item needs at least one
#      def/structure-kind name, EXCEPT the one pinned no-Lean
#      exemption def:domain-signature-notation; a `class` item needs at
#      least one class-kind name; an `instance` item needs at least one
#      instance-kind name). BIJECTION LAW (C2-E4a/A1): every marked env
#      carries EXACTLY ONE \lean{} name (>=2 is a hard structural
#      violation) -- the map envs->decls is injective, not surjective;
#      technical companions (simp/_apply lemmas, round-trip halves,
#      unit-law twins, raw/corollary doublings) are unmarked internals
#      instead, tagged `-- blueprint: internal (...)` in the Lean source.
#   c'. CENSUS (C2-E4a/A2, scoped) — every top-level declaration in a
#      fixed CENSUS_FILES list (the chapters this ticket touches, not yet
#      the whole NeSyCat namespace -- a disclosed scope reduction) is
#      either cited by exactly one env or carries the internal tag; a
#      pragmatic text-based name matcher, not a full `lake env lean`
#      environment fold.
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
import os
import re
import sys

# C2-E4a full Lean-kind sync: the blueprint's environment inventory is
# EXACTLY Lean's own declaration kinds -- def, class, instance, abbrev,
# lemma, theorem (+ proof) -- rendered here as the LaTeX env names
# definition/class/instance/abbreviation/lemma/theorem/proof. THEOREM_FAMILY
# narrows to lemma/theorem only (Lean ranks nothing between the two
# keywords). DEAD_KINDS lists every abolished env name kept in TARGET_KINDS
# purely so parse_envs still recognizes and reports a stray one -- a HARD
# gate violation, never silently invisible (remark/proposition/corollary:
# C2-E3/A1; example/conjecture: C2-E4a full kind sync -- ex:* envs became
# `instance` (a class witness) or dissolved into prose, cnj:* became a
# `theorem` with an "Open." proof).
THEOREM_FAMILY = {"theorem", "lemma"}
LEAN_MIRROR_KINDS = {"definition", "class", "instance", "abbreviation"}
DEAD_KINDS = {"remark", "proposition", "corollary", "example", "conjecture"}
TARGET_KINDS = THEOREM_FAMILY | LEAN_MIRROR_KINDS | DEAD_KINDS | {"proof"}

# The open-theorem convention's proof body, matched with surrounding
# whitespace stripped (the body text between \begin{proof} and \end{proof},
# label/comment lines aside, must be exactly this one sentence).
OPEN_PROOF_BODY = "Open."

# The one definition environment with no Lean counterpart, by standing user
# decision (blueprint/src/content.tex's "Blueprint-to-Lean correspondence"
# paragraph) -- exempted by label from the `definition` kind-check.
DEF_KIND_CHECK_EXEMPT_LABELS = {"def:domain-signature-notation"}

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

    # 1. theorem-family (lemma/theorem) immediately followed by
    #    \begin{proof} -- no exception for an open theorem, which is a
    #    theorem env like any other, just with an "Open." proof body
    #    (checked in step 1b below).
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

    # 1b. OPEN-THEOREM CONVENTION (C2-E4a, new structural check): a proof
    #     environment whose body is exactly the open marker "Open." must
    #     carry no \leanok (nothing is formalized -- there is no proof to
    #     mark), and the theorem-family environment it pairs with (the one
    #     immediately preceding it) must itself carry no \leanok either.
    for pos, (k, s, e) in enumerate(envs):
        if k != "proof":
            continue
        body = body_text(s, e)
        # Strip the \begin{proof}/\end{proof} lines and any \label/\leanok
        # line (the very thing being flagged below must not itself hide
        # the open marker from this comparison), then compare what is
        # left to the open marker.
        inner_lines = code_lines[s + 1:e]
        inner_lines = [l for l in inner_lines
                        if not LABEL_RE.search(l) and not LEANOK_RE.search(l)]
        inner = "\n".join(l for l in inner_lines if l.strip() != "").strip()
        if inner != OPEN_PROOF_BODY:
            continue
        if LEANOK_RE.search(body):
            violations.append(
                f"line {s + 1} (proof, open marker): an \"Open.\" proof "
                "carries \\leanok -- nothing is formalized, remove the mark")
        prev = envs[pos - 1] if pos > 0 else None
        if prev and prev[0] in THEOREM_FAMILY:
            prev_label = label_of(prev[1], prev[2])
            if LEANOK_RE.search(body_text(prev[1], prev[2])):
                violations.append(
                    f"line {prev[1] + 1} ({prev[0]} {prev_label}): paired "
                    "with an \"Open.\" proof but the statement carries "
                    "\\leanok")

    # 2. no Proof/qed argumentation inside definition/class/instance/
    #    abbreviation bodies (Lean-mirror kinds -- none of them are
    #    claims that get proved).
    for (k, s, e) in envs:
        if k in LEAN_MIRROR_KINDS:
            if PROOF_ARG_RE.search(body_text(s, e)):
                violations.append(
                    f"line {s + 1} ({k} {label_of(s, e)}): body contains "
                    "proof/qed argumentation (\\begin{proof} or \\qed)")

    # 3. zero \uses{rem:...} anywhere (remark is a dead/abolished kind --
    #    this check is defense in depth, kept so a stray \uses{rem:...}
    #    is caught even though no rem: label can legitimately exist).
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
        if k not in (THEOREM_FAMILY | LEAN_MIRROR_KINDS):
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

    # 6. ZERO DEAD-KIND ENVIRONMENTS (C2-E3 + C2-E4a full Lean-kind-sync
    #    decree, HARD law): remark/proposition/corollary/example/
    #    conjecture are all abolished. Each stays in TARGET_KINDS above
    #    (so parse_envs still recognizes and reports it here) precisely
    #    so a stray one is CAUGHT, not silently invisible to this gate.
    RETRIAGE = {
        "remark": "dissolve into plain narrative prose before/after the "
                   "nearest formal env",
        "proposition": "retriage to lemma (cited-as-infrastructure) or "
                        "theorem (chapter-payoff statement)",
        "corollary": "retriage to lemma (cited-as-infrastructure) or "
                      "theorem (chapter-payoff statement)",
        "example": "retriage to an `instance` env (if it witnesses a "
                    "class) or dissolve into plain narrative prose",
        "conjecture": "retriage to a `theorem` env with a proof body of "
                       "exactly \"Open.\" (the open-theorem convention)",
    }
    for (k, s, e) in envs:
        if k in DEAD_KINDS:
            violations.append(
                f"line {s + 1} ({k} {label_of(s, e)}): {k} environments "
                f"are abolished -- {RETRIAGE[k]}")

    # 7. BIJECTION LAW (C2-E4a/A1 USER DECREE, HARD law): the LaTeX<->Lean
    #    correspondence is one-to-one -- every marked environment (one
    #    that carries a \lean{} at all) carries EXACTLY ONE name, its
    #    principal declaration. The map is injective envs->decls, not
    #    surjective: technical companions (simp/_apply lemmas, round-trip
    #    halves, unit-law twins, raw/corollary doublings) are dropped from
    #    the \lean{} list and become unmarked internals (still compiled,
    #    still checked by scripts/check.sh, just not blueprint-cited) --
    #    see NeSyCat/**/*.lean's `-- blueprint: internal (...)` comments
    #    for the demoted declarations. A \lean{} list of >=2 names is a
    #    HARD violation, not a style nit.
    for (k, s, e) in envs:
        if k not in (THEOREM_FAMILY | LEAN_MIRROR_KINDS):
            continue
        names = []
        for m in LEAN_RE.finditer(body_text(s, e)):
            names.extend(x.strip() for x in m.group(1).split(',')
                         if x.strip())
        if len(names) > 1:
            violations.append(
                f"line {s + 1} ({k} {label_of(s, e)}): \\lean{{}} names "
                f"{names} violate the bijection law -- exactly one "
                "principal name per environment (demote the rest to "
                "unmarked internals)")

    # Build groups for the kind-check step (theorem-family, definition,
    # class, instance, abbreviation -- these are the kinds part (b)
    # checks; dead kinds never reach here since violations above already
    # fail the gate before check-kinds would matter).
    for (k, s, e) in envs:
        fam = "theorem-family" if k in THEOREM_FAMILY else k
        if fam not in ("theorem-family", "definition", "class", "instance",
                       "abbreviation"):
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
    print("      | .inductInfo _ => \"induct\"")
    print("      | .defnInfo _ => \"def\"")
    print("    let mut kind := base")
    # BUG FIX (C2-E4a): a Lean `class` elaborates to `.inductInfo`, not
    # `.defnInfo` -- classes ARE structures internally. The prior version
    # of this generator only ever consulted `isClass`/`isStructure` inside
    # the `base == "def"` branch, so it could never actually report
    # "class" for a real `class`/`structure` declaration (both are
    # `.inductInfo`, always landing on the `isStructure env n then
    # "structure"` fallback first). Fixed by checking isInstance/isClass/
    # isStructure unconditionally, in that priority order, regardless of
    # `base` -- this is what makes the new `class`/`instance` blueprint
    # kinds checkable at all.
    print("    let inst <- isInstance n")
    print("    if inst then kind := \"instance\"")
    print("    else if isClass env n then kind := \"class\"")
    print("    else if isStructure env n then kind := \"structure\"")
    print("    else if base == \"induct\" then kind := \"inductive\"")
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
            # Bijection law (C2-E4a/A1): exactly one name reaches here
            # (>=2 already failed structurally above), so this checks
            # THAT one name's kind, not "at least one of several".
            if "theorem" not in kinds_here:
                violations.append(
                    f"theorem-family {g['label']} (line {g['line']}): its "
                    f"\\lean name ({', '.join(g['names'])}) is not "
                    "theorem-kind")
        elif g["kind"] == "abbreviation":
            for nm, lk, red in zip(g["names"], kinds_here, reds_here):
                if lk != "def" or red != "reducible":
                    violations.append(
                        f"abbreviation {g['label']} (line {g['line']}): "
                        f"\\lean name '{nm}' is {lk}/{red}, expected a "
                        "reducible def (abbrev)")
        elif g["kind"] == "definition":
            # C2-E4a full Lean-kind sync: `definition` is now
            # kind-restricted to def/structure declarations only -- a
            # class or instance living inside a `definition` env belongs
            # in its own `class`/`instance` env instead, so class-kind
            # and instance-kind names do NOT count toward satisfying this
            # check (a definition item whose \lean names are only
            # class-kind is exactly the kind of drift this gate exists to
            # catch). The one pinned no-Lean exemption,
            # def:domain-signature-notation, is exempted by label (it has
            # zero \lean names, so it never reaches this branch at all --
            # the `if not g["names"]: continue` guard above already skips
            # it; the label check here is belt-and-suspenders).
            if g["label"] in DEF_KIND_CHECK_EXEMPT_LABELS:
                continue
            non_theorem = [lk for lk in kinds_here if lk in ("def", "structure")]
            if not non_theorem:
                violations.append(
                    f"definition {g['label']} (line {g['line']}): its "
                    f"\\lean name ({', '.join(g['names'])}) is not "
                    "def/structure-kind (class/instance-kind names belong "
                    "in a `class`/`instance` env instead)")
        elif g["kind"] == "class":
            if "class" not in kinds_here:
                violations.append(
                    f"class {g['label']} (line {g['line']}): its \\lean "
                    f"name ({', '.join(g['names'])}) is not class-kind")
        elif g["kind"] == "instance":
            if "instance" not in kinds_here:
                violations.append(
                    f"instance {g['label']} (line {g['line']}): its \\lean "
                    f"name ({', '.join(g['names'])}) is not instance-kind")

    for v in violations:
        print("VIOL\t" + v)

    n_names = len({nm for g in groups for nm in g["names"]})
    print(f"KIND-CHECK-SUMMARY\t{n_names} names kind-checked, "
          f"{len(violations)} violation(s)")
    return 1 if violations else 0



# CENSUS (C2-E4a/A2 completeness law, SCOPED implementation, disclosed):
# every top-level NeSyCat-namespace declaration is either cited by exactly
# one env (the A1 bijection) or explicitly tagged `-- blueprint: internal
# (...)` in the source. A full census would fold the *entire* Lean
# environment via `lake env lean` filtered to the NeSyCat module prefix;
# this implementation is a pragmatic TEXT-based name matcher over a fixed
# CENSUS_FILES list instead (the Truth-value-structures and semiring-monad
# chapters this ticket actually touches), not the whole namespace -- a
# disclosed scope reduction, not a silent one. Extending CENSUS_FILES to
# the rest of the library is future work (each new chapter's ticket should
# add its own files here as it goes).
CENSUS_FILES = [
    "NeSyCat/Monad/SemiringMonad.lean",
    "NeSyCat/Monad/Dist.lean",
    "NeSyCat/Monad/LogIso.lean",
    "NeSyCat/Truth/BLat2Mon.lean",
    "NeSyCat/Truth/DeMorgan.lean",
    "NeSyCat/Truth/Chain.lean",
    "NeSyCat/Truth/BoolInstance.lean",
    "NeSyCat/Truth/UnitInterval.lean",
    "NeSyCat/Truth/Impossibility.lean",
    "NeSyCat/Truth/TruthSpace.lean",
    "NeSyCat/Truth/Lifted.lean",
    "NeSyCat/Truth/ThreeLayers.lean",
]

CENSUS_DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?'
    r'(def|theorem|lemma|instance|abbrev|structure|class)\s+'
    r'([A-Za-z_][A-Za-z0-9_\.\']*)')
CENSUS_INTERNAL_RE = re.compile(r'--\s*blueprint:\s*internal\b')
# Declaration names auto-generated by a `where`/anonymous-constructor
# structure body, or by tactic blocks, are not top-level source
# declarations and are skipped by construction (this regex only matches
# lines beginning with a keyword at column 0, i.e. top-level decls, not
# indented field/`where` bodies).


def cmd_census(content_tex_path, repo_root):
    text = open(content_tex_path, encoding="utf-8").read()
    cited = set()
    for m in LEAN_RE.finditer(text):
        for nm in m.group(1).split(','):
            nm = nm.strip()
            if nm:
                # bare last segment, to match a Lean source declaration's
                # own (possibly namespace-relative) spelling.
                cited.add(nm.split('.')[-1])
                cited.add(nm)  # also keep the fully-qualified form

    total = 0
    n_cited = 0
    n_internal = 0
    unclassified = []
    for relpath in CENSUS_FILES:
        path = os.path.join(repo_root, relpath)
        if not os.path.isfile(path):
            continue
        lines = open(path, encoding="utf-8").read().split('\n')
        pending_internal = False
        in_block_comment = False  # tracks a `/- ... -/` / `/-! ... -/` /
                                   # `/-- ... -/` doc-comment block, whose
                                   # prose lines (e.g. "instance argument,
                                   # not a derived one, ...") must never be
                                   # mistaken for a top-level declaration.
        for line in lines:
            stripped = line.strip()
            if in_block_comment:
                if "-/" in line:
                    in_block_comment = False
                continue
            if stripped.startswith("/-"):
                if "-/" not in stripped[2:]:
                    in_block_comment = True
                continue
            if CENSUS_INTERNAL_RE.search(stripped):
                pending_internal = True
                continue
            m = CENSUS_DECL_RE.match(line)
            if not m:
                # A blank/comment line between the tag and the decl keeps
                # the pending flag alive; anything else resets it.
                if stripped != "" and not stripped.startswith("--"):
                    pending_internal = False
                continue
            name = m.group(2)
            total += 1
            bare = name.split('.')[-1]
            if pending_internal:
                n_internal += 1
            elif bare in cited or name in cited:
                n_cited += 1
            else:
                unclassified.append(f"{relpath}: {name}")
            pending_internal = False

    print(f"CENSUS-SUMMARY\t{total} declarations scanned "
          f"({len(CENSUS_FILES)} files): {n_cited} cited, "
          f"{n_internal} internal, {len(unclassified)} unclassified")
    for u in unclassified:
        print("VIOL\t" + f"census: {u} is neither cited by any env's "
              "\\lean{} nor tagged `-- blueprint: internal (...)`")
    return 1 if unclassified else 0


def main():
    if len(sys.argv) < 2:
        print("usage: correspondence.py "
              "<structure|emit-lean|check-kinds|census> ...",
              file=sys.stderr)
        return 2
    mode = sys.argv[1]
    if mode == "structure":
        return cmd_structure(sys.argv[2])
    if mode == "emit-lean":
        return cmd_emit_lean(sys.argv[2])
    if mode == "check-kinds":
        return cmd_check_kinds(sys.argv[2], sys.argv[3])
    if mode == "census":
        return cmd_census(sys.argv[2], sys.argv[3])
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

echo "==> completeness census (C2-E4a/A2, scoped -- see CENSUS_FILES)"
CENSUS_OUT="$(python3 "$CORR_PY" census blueprint/src/content.tex "$REPO_ROOT")" || true
CENSUS_STATUS=0
printf '%s\n' "$CENSUS_OUT" | grep -q "^VIOL${TAB}" && CENSUS_STATUS=1
printf '%s\n' "$CENSUS_OUT" | grep "^CENSUS-SUMMARY${TAB}" | sed -E "s/^CENSUS-SUMMARY${TAB}/census: /"
if [ "$CENSUS_STATUS" -ne 0 ]; then
  echo "CORRESPONDENCE census violations:"
  printf '%s\n' "$CENSUS_OUT" | grep "^VIOL${TAB}" | sed -E "s/^VIOL${TAB}/  - /"
  fail 1
fi

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
