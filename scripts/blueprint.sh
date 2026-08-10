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
#   c'. CENSUS (C2-E4a/A2, KERNEL-TRUTH FOLD as of C2-H2 item 1) — every
#      top-level declaration in the WHOLE NeSyCat namespace (no more
#      CENSUS_FILES scope restriction) is either cited by exactly one env
#      or carries the `@[blueprint_internal]` attribute (C2-H2 item 2,
#      replacing the old `-- blueprint: internal (...)` comment tag). Kernel
#      truth, not text: a generated Lean file folds over `(← getEnv).constants`
#      filtered by module prefix `NeSyCat.` (via `getModuleIdxFor?` +
#      `header.moduleNames`, not a name-prefix guess), then drops
#      auxiliary/internal declarations via a DISCLOSED filter stack:
#        (i)   `Lean.Name.isBlackListed` (Mathlib's own internal-decl
#              filter: `isInternalDetail` [`_`-prefixed components,
#              `eq_`/`match_`/`proof_`/`omega_`-prefixed names] plus
#              `isAuxRecursor`, `isNoConfusion`, `isRec`, `isMatcher`,
#              `sorryAx`, and a bare `.inj`);
#        (ii)  an extra suffix list `isBlackListed` does not already cover:
#              `.injEq`, `.sizeOf_spec`, `.sizeOf_eq`, `.brecOn`,
#              `.binductionOn`, `.below`, `.ibelow`, `.ctorIdx`;
#        (iii) constructors (`ConstantInfo.ctorInfo`);
#        (iv)  structure/class field projections, via
#              `Environment.getProjectionFnInfo?` (catches every `where`-
#              block field, including a first-parent `extends` subobject
#              embedding);
#        (v)   auto-generated parent-embedding combinators for every
#              *additional* (non-subobject) parent in a multi-`extends`
#              class, collected via `Lean.getStructureParentInfo` over
#              every NeSyCat structure/class (projFn names not already
#              caught by (iv), e.g. a second `extends` parent's `.toFoo`).
#      The `blueprintInternalAttr` declaration itself in
#      `NeSyCat/BlueprintAttr.lean` (the attribute's own definition, which
#      cannot self-tag) is exempted by declaration name, the same way
#      STRUCTURE-MIRROR exempts the Introduction (C2-E8: narrowed from a
#      whole-module exemption, so any OTHER declaration later added to
#      that file is counted like any other NeSyCat declaration).
#      What survives all five filters is real, human-authored content:
#      classes, instances (named, anonymous, or `(priority := ...)`),
#      defs, theorems, lemmas — exactly what the OLD regex census tried
#      (and, for anonymous/`(priority := ...)` instances and any
#      declaration outside its fixed 12-file CENSUS_FILES scope, failed)
#      to enumerate from source text.
#   c. REGISTRY SYNC — every `% Lean:`-tagged macro in the sibling
#      NeSyCat.Logics/macros.sty is checked against NeSyCat/Notation.lean
#      (vacuous-ready: prints a "not yet present" note until that file
#      exists).
#   d. STRUCTURE-MIRROR (C2-E6, USER DECREE 2026-08-09) — the blueprint's
#      \section/\subsection tree and the NeSyCat/ folder tree must mirror
#      each other exactly: every \section/\subsection carries a trailing
#      `% lean-dir: <path>` tag (Introduction alone may opt out with
#      `% lean-dir: -`), every tagged path must exist as a NeSyCat/
#      folder, and every NeSyCat/ folder must be tagged by some section.
#      Pure text + filesystem, no Lean elaboration; the derived tree is
#      printed. The identical check also gates every commit (see
#      scripts/git-hooks/commit-msg and its .git/hooks/ install), since a
#      mismatched tree must never even be committable.
#   e. STRUCTURAL/ARITHMETIC CLASSIFICATION (C3-EXEC item 2, corrected and
#      GATED by C3-EXEC-FIX) — every cited theorem/lemma is bucketed, from
#      its full Lean type, into carrier-agnostic (holds exactly in any
#      implementation) and carrier-algebra-dependent (holds only insofar as
#      the implementation's arithmetic realizes the axioms). The counts and
#      the structural names are asserted against the `% CLASSIFY-SENTINEL:`
#      line in content.tex; any drift is a hard gate violation, since the
#      numbers are quoted to a reader in the rendered dichotomy table.
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

# Every scratch file this run makes lives in ONE per-run directory.
# BSD `mktemp` substitutes only a TRAILING run of X's, so the old
# templates ("$TMPDIR/blueprint-decl-check.XXXXXX.lean" and friends,
# X's in the middle) created that LITERAL filename and a second
# concurrent run died with "mkstemp failed: File exists" — which is
# what broke parallel worktree runs. `mktemp -d` with trailing X's is
# unique per run, and the files inside it can keep plain readable names.
SCRATCH_DIR="$(mktemp -d "${TMPDIR:-/tmp}/blueprint-scratch.XXXXXX")"
trap 'rm -rf "$SCRATCH_DIR"' EXIT

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
  SCRATCH="$SCRATCH_DIR/decl-check.lean"

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

CORR_PY="$SCRATCH_DIR/correspondence.py"
GROUPS_JSONL="$SCRATCH_DIR/groups.jsonl"
KIND_LEAN="$SCRATCH_DIR/kindcheck.lean"
KIND_OUT="$SCRATCH_DIR/kindcheck.out"
CENSUS_LEAN="$SCRATCH_DIR/census.lean"
CENSUS_LEAN_OUT="$SCRATCH_DIR/census.out"

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
    # C2-H2 item 7: previously a FLAT sequence of N `IO.println` statements
    # inside one `do` block, whose elaboration depth grows LINEARLY with
    # the name count (the default maxRecDepth 512 topped out near ~123
    # names, hit at 163 names during C2-T4, patched at the time by simply
    # raising the budget to 8000). A `for` loop over an explicit name list
    # is a single recursive elaboration step regardless of list length --
    # O(1) elaboration depth, not O(n) -- so the raised budget is no
    # longer needed and is dropped entirely (no `set_option maxRecDepth`
    # line at all).
    print("def blueprintKindCheckNames : List Name := [")
    for nm in names:
        print(f"  `{nm},")
    print("]")
    print()
    print("#eval show MetaM Unit from do")
    print("  for n in blueprintKindCheckNames do")
    print("    IO.println (s!\"KIND\\t{n}\\t\" ++ (<- blueprintKindOf n))")


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


# KERNEL-TRUTH AXIOM AUDIT (C2-H2 item 3): for every cited name, its
# transitive axiom dependency set (`Lean.collectAxioms`, the exact
# machinery `#print axioms` itself calls) must be a subset of
# {propext, Classical.choice, Quot.sound}. This catches TRANSITIVE
# `sorryAx` -- a `sorry` several calls deep inside a private helper the
# cited name depends on -- which scripts/sorry-report.sh's source-text
# regex cannot see at all (it only scans for the literal token `sorry` in
# each file, not what a declaration's proof term actually axiomatizes).
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def cmd_emit_axiom_lean(names):
    print("import NeSyCat")
    print()
    print("open Lean Meta in")
    print("#eval show MetaM Unit from do")
    for nm in names:
        print(f"  let axs <- collectAxioms `{nm}")
        print(f"  IO.println (\"AXIOMS\\t{nm}\\t\" ++ "
              "String.intercalate \",\" (axs.toList.map toString))")


def cmd_axiom_check(axiom_out_path):
    violations = []
    n = 0
    with open(axiom_out_path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.startswith("AXIOMS\t"):
                continue
            _, name, axs_raw = line.split("\t", 2)
            n += 1
            axs = [a for a in axs_raw.split(",") if a]
            extra = [a for a in axs if a not in ALLOWED_AXIOMS]
            shown = ", ".join(axs) if axs else "(none)"
            print(f"AXIOM\t{name}: {shown}")
            if extra:
                violations.append(
                    f"{name} depends on disallowed axiom(s) "
                    f"{extra} (transitive #print axioms, via "
                    "Lean.collectAxioms) -- only propext, "
                    "Classical.choice, Quot.sound are permitted")
    for v in violations:
        print("VIOL\t" + v)
    print(f"AXIOM-CHECK-SUMMARY\t{n} names audited, "
          f"{len(violations)} violation(s)")
    return 1 if violations else 0


# CENSUS (C2-E4a/A2 completeness law; KERNEL-TRUTH FOLD as of C2-H2 item 1):
# every top-level NeSyCat-namespace declaration is either cited by exactly
# one env (the A1 bijection) or carries `@[blueprint_internal]` (C2-H2
# item 2). `cmd_emit_census_lean` prints a Lean scratch file that folds
# `(← getEnv).constants`, filtered by MODULE prefix `NeSyCat.` (not a name
# guess) and the disclosed five-stage internal/auxiliary filter documented
# at this script's top comment; `cmd_census_classify` reads that fold's
# output back and cross-references it against `blueprint/src/content.tex`'s
# `\lean{}` citations, exactly mirroring the old text-census's
# cited/internal/unclassified accounting -- just sourced from the kernel
# instead of a source-text regex, and over the WHOLE namespace instead of a
# fixed CENSUS_FILES scope.
CENSUS_EXTRA_AUX_SUFFIXES = [
    "injEq", "sizeOf_spec", "sizeOf_eq", "brecOn", "binductionOn",
    "below", "ibelow", "ctorIdx",
]
# The attribute's own defining declaration: exempted the same way
# STRUCTURE-MIRROR exempts the Introduction (it cannot self-tag -- applying
# `@[blueprint_internal]` requires the attribute to already be registered,
# which is circular on its own `initialize ... ← registerTagAttribute ...`
# line). C2-E8 narrowing: this used to exempt the WHOLE
# `NeSyCat.BlueprintAttr` MODULE (any future declaration added to that
# file would have been silently invisible to the census); narrowed to
# exempt exactly the ONE declaration `registerTagAttribute` creates,
# `blueprintInternalAttr` itself (verified directly against a scratch
# `#eval` dump of every constant in that module: `initialize x : T ←
# v` also emits a private `initFn` helper,
# `_private.NeSyCat.BlueprintAttr.0.initFn...`, but that one is already
# caught by stage (i)'s `Lean.Name.isBlackListed` -- confirmed
# `isBlackListed = true` on it directly -- so it needs no exemption of
# its own). A future declaration added to `BlueprintAttr.lean` is now
# counted like any other NeSyCat declaration, per the ticket's own
# RED-check requirement.
CENSUS_EXEMPT_DECLS = {"blueprintInternalAttr"}


def cmd_emit_census_lean():
    print("import NeSyCat")
    print("import Mathlib")
    print()
    print("open Lean Meta")
    print()
    suffixes = ", ".join(f'"{s}"' for s in CENSUS_EXTRA_AUX_SUFFIXES)
    print(f"def censusExtraAuxSuffixes : List String := [{suffixes}]")
    print()
    print("def censusHasAuxSuffix (n : Name) : Bool :=")
    print("  match n with")
    print("  | .str _ s => censusExtraAuxSuffixes.any (· == s)")
    print("  | _ => false")
    print()
    exempt = ", ".join(f"`{m}" for m in sorted(CENSUS_EXEMPT_DECLS))
    print(f"def censusExemptDecls : List Name := [{exempt}]")
    print()
    print("#eval show MetaM Unit from do")
    print("  let env <- getEnv")
    print("  -- Auto-generated parent-embedding projections (both subobject")
    print("  -- fields AND flattened multi-inheritance combinator defs) for")
    print("  -- every structure/class under the NeSyCat module prefix.")
    print("  let mut parentProjSet : NameSet := {}")
    print("  for (name, _info) in env.constants.toList do")
    print("    match env.getModuleIdxFor? name with")
    print("    | none => pure ()")
    print("    | some idx =>")
    print("      let modName := env.header.moduleNames[idx]!")
    print("      if modName.getRoot == `NeSyCat && isStructure env name then")
    print("        for pinfo in getStructureParentInfo env name do")
    print("          parentProjSet := parentProjSet.insert pinfo.projFn")
    print("  for (name, info) in env.constants.toList do")
    print("    match env.getModuleIdxFor? name with")
    print("    | none => pure ()")
    print("    | some idx =>")
    print("      let modName := env.header.moduleNames[idx]!")
    print("      if modName.getRoot == `NeSyCat "
          "&& !censusExemptDecls.contains name then")
    print("        let isCtor := match info with")
    print("          | .ctorInfo _ => true")
    print("          | _ => false")
    print("        let isProj := (env.getProjectionFnInfo? name).isSome")
    print("        let isParentProj := parentProjSet.contains name")
    print("        let isThm := match info with")
    print("          | .thmInfo _ => true")
    print("          | _ => false")
    print("        if (<- Lean.Name.isBlackListed name) "
          "|| censusHasAuxSuffix name || isCtor || isProj "
          "|| isParentProj then")
    print("          pure ()")
    print("        else")
    print("          let tagged := blueprintInternalAttr.hasTag env name")
    print("          IO.println "
          "s!\"CENSUS\\t{name}\\t{tagged}\\t{isThm}\\t{modName}\"")


def strip_lean_comments(src):
    """Strip `/- ... -/` block comments and `--` line comments from Lean
    source, tracking block-comment state across lines (shared by the
    census-classify reuse-advisory below)."""
    out_lines = []
    in_block = False
    for raw_line in src.split('\n'):
        if in_block:
            if "-/" in raw_line:
                in_block = False
                raw_line = raw_line.split("-/", 1)[1]
            else:
                continue
        while "/-" in raw_line:
            before, _, after = raw_line.partition("/-")
            if "-/" in after:
                _, _, after = after.partition("-/")
                raw_line = before + after
            else:
                raw_line = before
                in_block = True
                break
        if not in_block:
            raw_line = raw_line.split("--", 1)[0]
        out_lines.append(raw_line)
    return "\n".join(out_lines)


def cmd_census_classify(content_tex_path, census_lean_out_path, repo_root):
    text = open(content_tex_path, encoding="utf-8").read()
    cited = set()
    for m in LEAN_RE.finditer(text):
        for nm in m.group(1).split(','):
            nm = nm.strip()
            if nm:
                cited.add(nm.split('.')[-1])
                cited.add(nm)

    total = 0
    n_cited = 0
    n_internal = 0
    unclassified = []
    cited_theorem_decls = []  # (module, name) -- feeds the reuse advisory.
    with open(census_lean_out_path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.startswith("CENSUS\t"):
                continue
            _, name, tagged, is_thm, mod = line.split("\t", 4)
            total += 1
            bare = name.split('.')[-1]
            if tagged == "true":
                n_internal += 1
            elif bare in cited or name in cited:
                n_cited += 1
                if is_thm == "true":
                    cited_theorem_decls.append((mod, name))
            else:
                unclassified.append(f"{mod}: {name}")

    print(f"CENSUS-SUMMARY\t{total} declarations scanned "
          f"(kernel fold, whole NeSyCat namespace): {n_cited} cited, "
          f"{n_internal} internal, {len(unclassified)} unclassified")
    for u in unclassified:
        print("VIOL\t" + f"census: {u} is neither cited by any env's "
              "\\lean{} nor tagged @[blueprint_internal]")

    # ADVISORY (C2-E4c, FORMALIZE.md's calibrated reuse/fold principle):
    # unchanged in spirit from the pre-C2-H2 text census -- a grep-based use
    # count of every cited theorem-kind declaration across the WHOLE
    # NeSyCat/ tree, surfacing zero-further-use folding CANDIDATES. Never a
    # gate violation (see the file-level comment on the old implementation
    # this replaces); the module name (not a relpath) is now the display
    # label, since the source of a cited name is the kernel fold, not a
    # per-file text scan.
    lean_root = os.path.join(repo_root, "NeSyCat")
    corpus_parts = []
    if os.path.isdir(lean_root):
        for dirpath, _dirnames, filenames in os.walk(lean_root):
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    with open(os.path.join(dirpath, fn),
                              encoding="utf-8") as fh:
                        corpus_parts.append(strip_lean_comments(fh.read()))
    corpus = "\n".join(corpus_parts)
    zero_use = []
    for mod, name in cited_theorem_decls:
        bare = name.split('.')[-1]
        pat = re.compile(r'(?<![\w])' + re.escape(bare) + r'(?![\w])')
        if len(pat.findall(corpus)) <= 1:
            zero_use.append(f"{mod}: {bare}")
    print(f"ADVISORY-SUMMARY\t{len(cited_theorem_decls)} cited "
          f"theorem/lemma declarations checked, {len(zero_use)} with "
          "zero further code uses (folding candidates per FORMALIZE.md's "
          "calibrated reuse principle; advisory only, never a gate "
          "violation)")
    for z in zero_use:
        print("ADVISORY\t" + f"census: {z} has zero code uses outside "
              "its own declaration -- a folding candidate, not a "
              "violation; every fold is individually adjudicated")

    return 1 if unclassified else 0


# STRUCTURAL/ARITHMETIC CLASSIFICATION (C3-EXEC item 2, USER DECREE
# 2026-08-10): every cited THEOREM/LEMMA-kind declaration is partitioned by
# whether its own Lean statement (the full type -- every binder plus the
# conclusion, not just the top-level telescope) depends anywhere on an
# algebraic hypothesis or a fixed already-structured carrier, or holds
# genuinely for a bare, unconstrained type. Mechanical, kernel-truth, same
# fold discipline as the CENSUS above: `cmd_emit_classify_lean` prints a
# scratch file that looks each cited name up via `getConstInfo`, keeps only
# theorem-kind ones, and dumps `Expr.getUsedConstants` over the declaration's
# own `.type` (parameters AND conclusion, so an algebraic dependency baked
# into a concrete instantiation -- e.g. `chain_bound`'s `NNReal`/`Real.log`,
# reached only through `PulloutChain`/`Tens`/`dec`, never through an
# instance-implicit binder on its own -- is caught, not just a bare
# `[Semiring S]`-style hypothesis); `cmd_classify_report` reads that dump
# back and buckets each name against the DISCLOSED marker list below: a
# match makes the theorem ARITHMETIC (it requires structure on the carrier
# -- algebraic, order-theoretic, or categorical -- somewhere in its
# statement, hence holds in an implementation only insofar as that
# implementation realizes those axioms); no match makes it STRUCTURAL (its
# Lean statement names no such class and no already-structured concrete
# carrier anywhere, hence it holds verbatim for any VALUE carrier
# whatsoever, exactly as implemented, float tensors included -- this is the
# mechanical confirmation of `thm:batch-exactness`, C3-EXEC item 1; see the
# `Monad`/`LawfulMonad` caveat under the marker list). The
# marker list mixes Mathlib's own algebraic/order class names (`Semiring`,
# `Lattice`, `LinearOrder`, ...) with the library's own algebraic
# vocabulary (`LatCSRng`, `BLat2Mon`, ...) AND its fixed already-structured
# carrier definitions (`BoolW`, `LogS`, `Tens`, `LogTens`, `PulloutChain`,
# `Dist`, `MS`) -- a theorem tied to one of those concrete carriers depends
# on that carrier's arithmetic exactly as much as one guarded by an
# explicit instance hypothesis, even though no instance binder names it.
# WHAT COUNTS AS ALGEBRA ON THE CARRIER (corrected, C3-EXEC-FIX item 1;
# the first cut of this list got it wrong and shipped a false structural
# verdict). CATEGORICAL structure counts: `[MonoidalCategory C]`,
# `[BraidedCategory C]`, `[ComonObj Z]` are axioms ON the carrier exactly
# as `[Semiring S]` is -- an implementation whose tensor is not
# associative/unital on the nose does not satisfy a theorem stated over a
# monoidal category, so `CategoryTheory` (and `Quiver`, the hom-structure
# underneath it) are MARKERS. That single correction moves
# `simQuant_nest` (lem:quantifier-nestable, whose type binds
# `[MonoidalCategory C] [BraidedCategory C] [ComonObj Z]` plus a
# `Nestable q` hypothesis) out of STRUCTURAL, where the first cut wrongly
# left it.
# The marker groups below were enumerated MECHANICALLY, not guessed: the
# used-constant dump of all 59 cited theorem-kind declarations was folded
# to its distinct head components, and every head naming an algebraic
# operation, an algebraic/order class, a categorical structure, or a fixed
# already-structured carrier was taken as a marker (the enumeration is
# reproducible: `emit-classify-lean` + `getUsedConstants`, one grep over
# the dump). The bare operation classes (`Add`, `Mul`, `Zero`, `One`, ...)
# and the low-level order classes (`LE`, `Preorder`, `PartialOrder`, ...)
# are markers on the same principle as the big ones: a statement that
# writes `x * y` or `x <= y` at all has demanded that much structure of
# its carrier. Component-prefix matching keeps them precise -- marker
# `Mul` matches `Mul` and `Mul.*`, never `MulOpposite` or `MulZeroClass`,
# which are separate markers of their own.
# DELIBERATELY NOT MARKERS, each for a stated reason:
#   - `Monad`/`LawfulMonad`: effect scaffolding on the AMBIENT monad, not
#     algebra on the VALUE carrier. A STRUCTURAL verdict therefore means
#     "no constraint on the value carrier", and it still PRESUPPOSES the
#     ambient monad is lawful -- a separate property of an implementation,
#     not something this fold or any theorem here certifies. content.tex's
#     dichotomy table states that caveat in the rendered document; it must
#     never be dropped when quoting the counts.
#   - `Nat`/`Fin`/`List`/`Prod`/`Set`/`Finset`/`Function`/`Eq`: index,
#     shape, and metadata types. `B : Nat` is a batch SIZE and `i : Fin B`
#     a batch INDEX; neither asks anything of the values being batched.
#     Marking `Nat` would make every statement in the document arithmetic
#     by bookkeeping alone and the classification would say nothing.
#   - `Fintype`/`DecidableEq`: finiteness and decidability side conditions
#     (what makes a row computable), not value algebra.
# Disclosed and reproducible, in the same spirit as the CENSUS's own
# suffix/exempt lists above: not a full semantic understanding of algebra,
# a fixed, auditable name list checked by prefix/component match,
# calibrated against every name cited in `content.tex` at authoring time
# (59 theorem-kind names, 3 structural / 56 arithmetic) and open to a
# disclosed extension the moment a genuinely new algebraic vocabulary word
# is cited. The counts are no longer advisory: `% CLASSIFY-SENTINEL:` in
# content.tex records them and the shell section below FAILS the gate on
# any drift, names included (C3-EXEC-FIX item 2).
CLASSIFY_ALGEBRAIC_MARKERS = [
    # bare operation/element classes: naming `x * y`, `x + y`, `0`, `1`
    # already demands that much of the carrier
    "Add", "Mul", "Sub", "Div", "Neg", "Inv", "Zero", "One", "Pow", "SMul",
    "NatCast", "IntCast", "OfNat",
    "HAdd", "HMul", "HSub", "HDiv", "HPow", "HSMul",
    # Mathlib algebraic classes
    "AddZero", "AddZeroClass", "MulZeroClass", "MulOneClass",
    "AddSemigroup", "Semigroup", "CommSemigroup",
    "AddMonoid", "AddCommMonoid", "Monoid", "CommMonoid",
    "AddMonoidWithOne", "AddCommMonoidWithOne", "MonoidWithZero",
    "DivInvMonoid", "AddGroup", "AddCommGroup", "Group", "CommGroup",
    "Distrib", "DistribMulAction", "DistribSMul", "SMulZeroClass",
    "MulAction", "Module", "Algebra",
    "Semiring", "CommSemiring", "NonAssocSemiring", "NonUnitalSemiring",
    "NonUnitalNonAssocSemiring",
    "Ring", "CommRing", "NonUnitalRing", "NonUnitalNonAssocRing",
    "NonUnitalCommRing", "NonUnitalNonAssocCommRing",
    "DivisionRing", "Field", "MulOpposite",
    # Mathlib order classes
    "LE", "LT", "Preorder", "PartialOrder", "SemilatticeInf",
    "SemilatticeSup", "Lattice", "DistribLattice", "CompleteLattice",
    "ConditionallyCompleteLattice", "LinearOrder", "BoundedOrder",
    "OrderBot", "OrderTop", "Bot", "Top", "Max", "Min", "OrderDual",
    "ZeroLEOneClass", "Monotone", "Antitone", "abs",
    # categorical structure ON the carrier (C3-EXEC-FIX item 1)
    "CategoryTheory", "Quiver",
    # fixed already-structured concrete carriers
    "NNReal", "ENNReal", "Real", "Int", "Rat", "NNRat", "Float",
    "Matrix", "TrivSqZeroExt", "unitInterval",
    # the library's own algebraic and categorical vocabulary
    "NeSyCat.LatSRng", "NeSyCat.LatCSRng", "NeSyCat.BLatSRng", "NeSyCat.BLatCSRng",
    "NeSyCat.BLat2Mon", "NeSyCat.BLat2CMon", "NeSyCat.LinBLat2Mon", "NeSyCat.LinBLat2CMon",
    "NeSyCat.DMStructure", "NeSyCat.DMFullCalculus", "NeSyCat.ZeroBot",
    "NeSyCat.OneTop", "NeSyCat.UnitBounds",
    "NeSyCat.TNorm", "NeSyCat.GradSemiring", "NeSyCat.MassPreserving", "NeSyCat.TruthSpace",
    "NeSyCat.Nestable", "NeSyCat.PointedObj", "NeSyCat.SymmetricFamily",
    # the library's own fixed already-structured carriers
    "NeSyCat.BoolW", "NeSyCat.LogS", "NeSyCat.LogSInf", "NeSyCat.Tens", "NeSyCat.LogTens",
    "NeSyCat.PulloutChain", "NeSyCat.Dist", "NeSyCat.MS", "NeSyCat.QRow",
]


def cmd_emit_classify_lean(names):
    print("import NeSyCat")
    print("import Mathlib")
    print()
    print("open Lean Meta")
    print()
    quoted = ", ".join(f"`{nm}" for nm in names)
    print(f"def classifyNames : List Name := [{quoted}]")
    print()
    print("#eval show MetaM Unit from do")
    print("  let env <- getEnv")
    print("  for nm in classifyNames do")
    print("    match env.find? nm with")
    print("    | none => pure ()")
    print("    | some info =>")
    print("      let isThm := match info with | .thmInfo _ => true | _ => false")
    print("      if isThm then")
    print("        let consts := info.type.getUsedConstants")
    print("        let names := consts.toList.map toString")
    print("        IO.println (s!\"CLASS\\t{nm}\\t\" ++ String.intercalate \",\" names)")


def _classify_head_matches(const_name, marker):
    """A used-constant counts as carrying marker `marker` if it IS that
    name, or is a dot-qualified descendant of it (`Semiring.toAddCommMonoid`
    matches marker `Semiring`; `NeSyCat.LatCSRng.toLatSRng` matches marker
    `NeSyCat.LatCSRng`) -- the same component-prefix discipline the CENSUS
    above already uses for auxiliary-suffix matching."""
    return const_name == marker or const_name.startswith(marker + ".")


def cmd_classify_report(classify_out_path):
    structural = []
    arithmetic = []
    with open(classify_out_path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.startswith("CLASS\t"):
                continue
            _, name, consts_raw = line.split("\t", 2)
            consts = [c for c in consts_raw.split(",") if c]
            hit = None
            for c in consts:
                for m in CLASSIFY_ALGEBRAIC_MARKERS:
                    if _classify_head_matches(c, m):
                        hit = m
                        break
                if hit:
                    break
            if hit:
                arithmetic.append((name, hit))
            else:
                structural.append(name)
    total = len(structural) + len(arithmetic)
    print(f"CLASSIFY-SUMMARY\t{total} cited theorem/lemma declarations "
          f"classified: {len(structural)} structural (bare value carrier: "
          f"no algebraic, order, or categorical hypothesis anywhere in the "
          f"statement -- holds exactly for any carrier) / "
          f"{len(arithmetic)} arithmetic (the statement depends somewhere "
          "on such a hypothesis or on a fixed already-structured carrier "
          "-- holds in an implementation only insofar as its arithmetic "
          "does)")
    for n in sorted(structural):
        print("CLASSIFY-STRUCTURAL\t" + n)
    for n, m in sorted(arithmetic):
        print(f"CLASSIFY-ARITHMETIC\t{n} (via {m})")
    return 0


# STRUCTURE-MIRROR (C2-E6, USER DECREE 2026-08-09): the blueprint's
# \section/\subsection tree and the NeSyCat/ folder tree must mirror each
# other exactly, computed and self-updating rather than hand-maintained.
# Every \section/\subsection line gains a trailing `% lean-dir: <path>`
# comment naming its NeSyCat/<path>/ folder (Introduction alone may tag
# `% lean-dir: -` to opt out). Pure text + filesystem, no Lean elaboration
# -- fast enough to also run at commit-msg time (see
# scripts/git-hooks/commit-msg, its .git/hooks/ install, and the plugin
# twin, which duplicate this exact logic since a commit-msg hook cannot
# shell out to this script's own Python heredoc).
STRUCTURE_MIRROR_RE = re.compile(
    r'^\\(section|subsection)\{([^}]*)\}'
    r'(?:\s*%\s*lean-dir:\s*(\S+))?\s*$')


def check_structure_mirror(content_tex_path, nesycat_root):
    """Returns (tree, violations). tree is a list of (kind, title, tag)
    in document order; violations is a list of human-readable strings."""
    violations = []
    declared = set()
    tree = []
    with open(content_tex_path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            m = STRUCTURE_MIRROR_RE.match(line.rstrip("\n"))
            if not m:
                continue
            kind, title, tag = m.groups()
            tree.append((kind, title, tag))
            if tag is None:
                violations.append(
                    f"untagged section: \\{kind}{{{title}}} carries no "
                    "'% lean-dir: <FolderName>' tag")
                continue
            if tag == "-":
                if title != "Introduction":
                    violations.append(
                        f"'% lean-dir: -' opt-out used by \\{kind}{{{title}}}, "
                        "but only the Introduction may opt out")
                continue
            declared.add(tag)
            folder = os.path.join(nesycat_root, tag)
            if not os.path.isdir(folder):
                violations.append(
                    f"tagged-but-missing folder: \\{kind}{{{title}}} tags "
                    f"'{tag}' but NeSyCat/{tag}/ does not exist")

    if os.path.isdir(nesycat_root):
        for dirpath, dirnames, _filenames in os.walk(nesycat_root):
            dirnames[:] = [d for d in dirnames if not d.startswith(".")]
            rel = os.path.relpath(dirpath, nesycat_root)
            if rel == ".":
                continue
            rel = rel.replace(os.sep, "/")
            if rel not in declared:
                violations.append(
                    f"orphan folder: NeSyCat/{rel}/ has no matching "
                    "'% lean-dir:' tag in content.tex")

    return tree, violations


def render_structure_mirror_tree(tree):
    lines = []
    for kind, title, tag in tree:
        indent = "  " if kind == "subsection" else ""
        shown = tag if tag is not None else "UNTAGGED"
        lines.append(f"{indent}{title}  ->  NeSyCat/{shown}"
                      if shown != "-" else f"{indent}{title}  ->  (no Lean home)")
    return lines


def cmd_structure_mirror(content_tex_path, nesycat_root):
    tree, violations = check_structure_mirror(content_tex_path, nesycat_root)
    print(f"STRUCTURE-MIRROR-SUMMARY\t{len(tree)} sections/subsections, "
          f"{len(violations)} violation(s)")
    for t in render_structure_mirror_tree(tree):
        print("TREE\t" + t)
    for v in violations:
        print("VIOL\t" + f"structure-mirror: {v}")
    return 1 if violations else 0


def main():
    if len(sys.argv) < 2:
        print("usage: correspondence.py "
              "<structure|emit-lean|check-kinds|emit-census-lean|"
              "census-classify|structure-mirror> ...",
              file=sys.stderr)
        return 2
    mode = sys.argv[1]
    if mode == "structure":
        return cmd_structure(sys.argv[2])
    if mode == "emit-lean":
        return cmd_emit_lean(sys.argv[2])
    if mode == "check-kinds":
        return cmd_check_kinds(sys.argv[2], sys.argv[3])
    if mode == "emit-axiom-lean":
        cmd_emit_axiom_lean(sys.argv[2:])
        return 0
    if mode == "axiom-check":
        return cmd_axiom_check(sys.argv[2])
    if mode == "emit-census-lean":
        cmd_emit_census_lean()
        return 0
    if mode == "census-classify":
        return cmd_census_classify(sys.argv[2], sys.argv[3], sys.argv[4])
    if mode == "emit-classify-lean":
        cmd_emit_classify_lean(sys.argv[2:])
        return 0
    if mode == "classify-report":
        return cmd_classify_report(sys.argv[2])
    if mode == "structure-mirror":
        return cmd_structure_mirror(sys.argv[2], sys.argv[3])
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

echo "==> kernel-truth axiom audit (C2-H2 item 3)"
if [ "${#DECL_NAMES[@]}" -eq 0 ]; then
  echo "kernel-truth: OK (0 names, vacuous -- no \\lean{...} names to audit)"
else
  AXIOM_LEAN="$SCRATCH_DIR/axioms.lean"
  AXIOM_OUT="$SCRATCH_DIR/axioms.out"

  python3 "$CORR_PY" emit-axiom-lean "${DECL_NAMES[@]}" > "$AXIOM_LEAN"
  if ! lake env lean "$AXIOM_LEAN" > "$AXIOM_OUT" 2>&1; then
    echo "kernel-truth axiom audit: Lean elaboration failed:"
    cat "$AXIOM_OUT"
    fail 1
  fi
  AXIOM_CHECK_OUT="$(python3 "$CORR_PY" axiom-check "$AXIOM_OUT")" || true
  AXIOM_STATUS=0
  printf '%s\n' "$AXIOM_CHECK_OUT" | grep -q "^VIOL${TAB}" && AXIOM_STATUS=1
  printf '%s\n' "$AXIOM_CHECK_OUT" | grep "^AXIOM${TAB}" | sed -E "s/^AXIOM${TAB}/  /"
  if [ "$AXIOM_STATUS" -ne 0 ]; then
    echo "kernel-truth axiom audit violations:"
    printf '%s\n' "$AXIOM_CHECK_OUT" | grep "^VIOL${TAB}" | sed -E "s/^VIOL${TAB}/  - /"
    fail 1
  fi
  echo "kernel-truth: OK (${#DECL_NAMES[@]} names)"
fi

echo "==> completeness census (C2-E4a/A2, KERNEL-TRUTH FOLD, whole NeSyCat namespace)"
python3 "$CORR_PY" emit-census-lean > "$CENSUS_LEAN"
if ! lake env lean "$CENSUS_LEAN" > "$CENSUS_LEAN_OUT" 2>&1; then
  echo "CORRESPONDENCE census: Lean elaboration failed:"
  cat "$CENSUS_LEAN_OUT"
  fail 1
fi
CENSUS_OUT="$(python3 "$CORR_PY" census-classify blueprint/src/content.tex "$CENSUS_LEAN_OUT" "$REPO_ROOT")" || true
CENSUS_STATUS=0
printf '%s\n' "$CENSUS_OUT" | grep -q "^VIOL${TAB}" && CENSUS_STATUS=1
printf '%s\n' "$CENSUS_OUT" | grep "^CENSUS-SUMMARY${TAB}" | sed -E "s/^CENSUS-SUMMARY${TAB}/census: /"
if [ "$CENSUS_STATUS" -ne 0 ]; then
  echo "CORRESPONDENCE census violations:"
  printf '%s\n' "$CENSUS_OUT" | grep "^VIOL${TAB}" | sed -E "s/^VIOL${TAB}/  - /"
  fail 1
fi
# ADVISORY only (C2-E4c calibrated reuse principle): zero-further-use
# cited theorem/lemma folding candidates, never a gate violation.
printf '%s\n' "$CENSUS_OUT" | grep "^ADVISORY-SUMMARY${TAB}" | sed -E "s/^ADVISORY-SUMMARY${TAB}/reuse-advisory: /"
printf '%s\n' "$CENSUS_OUT" | grep "^ADVISORY${TAB}" | sed -E "s/^ADVISORY${TAB}/  - /"

echo "==> structural/arithmetic classification (C3-EXEC item 2, mechanical fold)"
if [ "${#DECL_NAMES[@]}" -eq 0 ]; then
  echo "classification: OK (0 names, vacuous -- no \\lean{...} names to classify)"
else
  CLASSIFY_LEAN="$SCRATCH_DIR/classify.lean"
  CLASSIFY_LEAN_OUT="$SCRATCH_DIR/classify.out"
  python3 "$CORR_PY" emit-classify-lean "${DECL_NAMES[@]}" > "$CLASSIFY_LEAN"
  if ! lake env lean "$CLASSIFY_LEAN" > "$CLASSIFY_LEAN_OUT" 2>&1; then
    echo "classification: Lean elaboration failed:"
    cat "$CLASSIFY_LEAN_OUT"
    fail 1
  fi
  CLASSIFY_OUT="$(python3 "$CORR_PY" classify-report "$CLASSIFY_LEAN_OUT")" || true
  printf '%s\n' "$CLASSIFY_OUT" | grep "^CLASSIFY-SUMMARY${TAB}" | sed -E "s/^CLASSIFY-SUMMARY${TAB}/classification: /"
  printf '%s\n' "$CLASSIFY_OUT" | grep "^CLASSIFY-STRUCTURAL${TAB}" | sed -E "s/^CLASSIFY-STRUCTURAL${TAB}/  structural: /"
  printf '%s\n' "$CLASSIFY_OUT" | grep "^CLASSIFY-ARITHMETIC${TAB}" | sed -E "s/^CLASSIFY-ARITHMETIC${TAB}/  arithmetic: /"

  # SENTINEL ASSERTION (C3-EXEC-FIX item 2). The first cut of this section
  # ended in `|| true` and asserted nothing, so the two counts could drift
  # silently -- and one of them was already wrong. They are now GATED, and
  # gated against the DOCUMENT, not against a number buried in this script:
  # the expectation lives in blueprint/src/content.tex as a single
  # `% CLASSIFY-SENTINEL:` line, immediately above the rendered dichotomy
  # table that quotes the same numbers to the reader. Anything that moves a
  # theorem across the line -- a new citation, a changed hypothesis, an
  # extended marker list -- turns this section RED until a human re-reads
  # the new structural entries' full types ONE BY ONE and updates both the
  # sentinel and the table. The structural NAMES are asserted too, not just
  # the counts: a swap of one structural entry for another keeps the counts
  # and must still stop the build. Format (one line, exact):
  #   % CLASSIFY-SENTINEL: total=N structural=K arithmetic=M names=a,b,c
  # with `names` the sorted, comma-separated structural list. The sort is
  # pinned to `LC_ALL=C` (byte order), not the ambient locale: the two
  # disagree on `_` against an upper-case letter (`batchTransformer` sorts
  # before `batch_layer_exact` in byte order, after it under en_US), and a
  # sentinel that flipped with the caller's locale would be a false RED.
  N_STRUCT="$(printf '%s\n' "$CLASSIFY_OUT" | grep -c "^CLASSIFY-STRUCTURAL${TAB}" || true)"
  N_ARITH="$(printf '%s\n' "$CLASSIFY_OUT" | grep -c "^CLASSIFY-ARITHMETIC${TAB}" || true)"
  N_CLASSIFIED=$((N_STRUCT + N_ARITH))
  STRUCT_NAMES="$(
    printf '%s\n' "$CLASSIFY_OUT" \
      | grep "^CLASSIFY-STRUCTURAL${TAB}" \
      | sed -E "s/^CLASSIFY-STRUCTURAL${TAB}//" \
      | LC_ALL=C sort | tr '\n' ',' | sed -E 's/,$//'
  )" || true
  CLASSIFY_ACTUAL="total=$N_CLASSIFIED structural=$N_STRUCT arithmetic=$N_ARITH names=$STRUCT_NAMES"
  SENTINEL_LINE="$(grep -E '^% CLASSIFY-SENTINEL:' blueprint/src/content.tex || true)"
  if [ -z "$SENTINEL_LINE" ]; then
    echo "classification sentinel: FAILED -- no '% CLASSIFY-SENTINEL:' line in blueprint/src/content.tex"
    echo "  computed: $CLASSIFY_ACTUAL"
    fail 1
  fi
  CLASSIFY_EXPECT="$(printf '%s\n' "$SENTINEL_LINE" | sed -E 's/^% CLASSIFY-SENTINEL:[[:space:]]*//')"
  if [ "$CLASSIFY_EXPECT" != "$CLASSIFY_ACTUAL" ]; then
    echo "classification sentinel: FAILED -- classification drifted from the recorded expectation"
    echo "  expected (content.tex % CLASSIFY-SENTINEL): $CLASSIFY_EXPECT"
    echo "  computed (this run):                        $CLASSIFY_ACTUAL"
    echo "  Re-read each structural entry's FULL type before updating the"
    echo "  sentinel, and update the dichotomy table's counts with it."
    fail 1
  fi
  echo "classification sentinel: OK ($CLASSIFY_ACTUAL)"
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

echo "==> structure-mirror (blueprint section tree <-> NeSyCat/ folder tree)"
MIRROR_OUT="$(python3 "$CORR_PY" structure-mirror blueprint/src/content.tex "$REPO_ROOT/NeSyCat")" || true
MIRROR_STATUS=0
printf '%s\n' "$MIRROR_OUT" | grep -q "^VIOL${TAB}" && MIRROR_STATUS=1
echo "derived tree:"
printf '%s\n' "$MIRROR_OUT" | grep "^TREE${TAB}" | sed -E "s/^TREE${TAB}/  /"
if [ "$MIRROR_STATUS" -ne 0 ]; then
  echo "CORRESPONDENCE structure-mirror violations:"
  printf '%s\n' "$MIRROR_OUT" | grep "^VIOL${TAB}" | sed -E "s/^VIOL${TAB}/  - /"
  fail 1
fi
printf '%s\n' "$MIRROR_OUT" | grep "^STRUCTURE-MIRROR-SUMMARY${TAB}" | sed -E "s/^STRUCTURE-MIRROR-SUMMARY${TAB}/structure-mirror: /"

echo "CORRESPONDENCE: OK ($N_ENVS environments, $N_NAMES names kind-checked)"

echo "BLUEPRINT: GREEN"
