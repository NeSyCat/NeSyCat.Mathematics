# FORMALIZE.md — Rules of Work

This file is the authoritative work-instruction document for any agent
session doing formalization work in this repository. It is the Lean 4
analog of the rules-of-work file described in Urban's "130k Lines of
Formal Topology in Two Weeks" (arXiv:2601.03298): a fast checker, a
sorry/admit tracker, a per-section progress ledger, and git as the
never-lose-work backup system. Follow it exactly. Work as long as
possible without stopping to ask questions.

## Scope rail (STRICT)

- You may create/edit files only under `NeSyCat/` (the library; topic
  folders as needed) and may edit
  `PROGRESS.md` and `blueprint/src/**`.
- `NeSyCat.lean` may ONLY be touched to add new
  `import NeSyCat.<NewFile>` lines when you create a new module.
- NEVER edit: `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`,
  `scripts/`, `references/`, `.github/`, `.foreman/`,
  `.gitignore`.
- NEVER run `lake update`.

## Never lose work

- Never run `git reset --hard`, `git revert`, `git checkout -- <file>`,
  or delete a compiling proof or definition.
- If you restructure a file, salvage every compiling theorem and
  definition — move it, don't drop it.
- Any commit that DECREASES the total line count of `NeSyCat/`
  must explicitly justify the decrease in its commit message. Cite
  Urban's rule 5: an agent once silently threw away 9k lines of working
  formalization. Do not repeat that mistake.

## Checker discipline

- After every meaningful edit, run `scripts/check.sh` (whole project)
  or `scripts/check.sh NeSyCat.Monad.<Module>` (one module, faster).
- Success = exit code 0 and no `error:` lines in the output (the script
  prints `CHECK: GREEN` on success, `CHECK: RED (exit <code>)` on
  failure).
- Commit small and often. Each commit message should have:
  1. a one-line summary,
  2. a short description of what changed,
  3. the sorry-count delta (before/after, from `scripts/sorry-report.sh`).
- Include the `Co-Authored-By:` footer per session convention if one is
  in use.
- When `blueprint/src/**` or any `\lean`/`\leanok` mark changes, run
  `scripts/blueprint.sh` and confirm it prints `CORRESPONDENCE: OK`
  followed by `BLUEPRINT: GREEN` before committing (`scripts/check.sh`
  remains the Lean commit gate). `CORRESPONDENCE: OK` is the
  blueprint<->Lean correspondence gate (structural editorial laws +
  Lean-kind assertions per `\lean{}` name) — a red CORRESPONDENCE
  section blocks exactly like a red decl-check.
- **Blueprint-sync commit law.** A commit that touches a `NeSyCat/**.lean`
  declaration cited by a blueprint `\lean{}` mark must either (1) stage
  the corresponding `blueprint/src/content.tex` tightening alongside it
  (the normal case — see the post-`\leanok` work-loop step below), or
  (2) carry a commit-message line starting `Blueprint-sync: <reason>`
  documenting a justified skip (e.g. a whitespace/comment-only edit or a
  golf pass with no statement change) — the same justified-skip
  convention as the never-lose-work line-count rule above. This is
  mechanically enforced: `scripts/git-hooks/commit-msg`, installed at
  `.git/hooks/commit-msg`, rejects a commit that satisfies neither.
- Every `.lean` file begins with the standard copyright header (copy it
  from `NeSyCat/Monad/LatticeSemiring.lean`; Apache 2.0, see `LICENSE`);
  keep the style/header linter silent.

## sorry policy

`sorry` is legitimate scaffolding. It is allowed in unfinished
branches, ALWAYS with an adjacent `-- TODO:` comment describing what
remains to be proved. Burn sorries down continuously — run
`scripts/sorry-report.sh` before and after each work unit and watch the
total trend downward over time.

HARD BANS (no exceptions):

- `axiom` declarations of any kind.
- Changing a target statement to make it weaker or trivial so it is
  easier to prove.
- `native_decide`.
- Using `set_option` to suppress ERRORS. (Suppressing purely stylistic
  linter warnings via `set_option linter.style... false` is fine;
  suppressing real errors is not.)
- Deleting a hard item instead of finishing it. Leave it as a `sorry`
  with notes instead.

## Faithfulness

**Absolutely lean.** Once an item's Lean form is settled (post-`\leanok`),
the blueprint's own prose for that item is tightened to match it: Lean's
economy and its natural proof language are the standard the informal
text is pulled toward, not the other way around. A blueprint item is
never left more verbose, more hedged, or less precise than the Lean
declaration and proof it now cites — see the post-`\leanok` work-loop
step below.

- Every formal item gets a doc comment of the form:
  `/-- Blueprint <tex-label> (<name>): <informal statement>. -/`, where
  `<tex-label>` is the blueprint `\label` key for that item in
  `blueprint/src/content.tex`.
- Faithfulness has two legs: (1) Lean statement ↔ blueprint statement —
  exact, library items are stated per the blueprint (the canonical
  informal document); (2) blueprint item ↔ its cited source — the
  blueprint is the canonical, authoritative document in its own right,
  not a restatement graded against some other standing target.
  Bibliographic citations (e.g. "[NeSy26, App. A]") are provenance
  credits, not a conformity requirement, so the check on a citation is
  ACCURACY: does the cited source really contain what is credited to it
  — not whether the blueprint's own statement matches the source's
  concrete case. Items are freely stated at their natural mathematical
  generality; a cited source's narrower case then appears as an
  instance/corollary, noted in-item in the library's own voice (no
  "divergence declared relative to the source" framing). When library
  work generalizes or corrects a claim that a live paper (e.g. NeSy26
  itself) still states more narrowly or differently, aligning that
  paper's text is part of closing the item, not optional follow-up —
  such paper edits are user-approved, never made unilaterally. Pinned
  texts used for an authoring or verification pass live at recorded git
  refs (ledger + blueprint preamble), not as standing copies.
- Before adding ANY definition or theorem:
  1. `grep` `NeSyCat/` for duplicates of the same item.
  2. Search Mathlib for existing versions (`exact?`, `apply?`, `rw?`,
     or https://leansearch.net).
- Mathlib may be used freely as BACKGROUND machinery (e.g. `Category`,
  `Functor`, `NatTrans` from `Mathlib.CategoryTheory`). But a library
  item from the canonical library document `blueprint/src/content.tex`
  (provenance: bibliographic citations, e.g. `[NeSy26, App. A]`, with
  pinned texts recorded at their git refs) must be STATED in the plain
  `NeSyCat` namespace and given a REAL proof. A
  bare one-line `exact <Mathlib lemma>` citation of the identical
  statement defeats the campaign's purpose — construct the proof, even
  if it uses Mathlib lemmas as steps.

## Blueprint structural laws

- **Final environment inventory (C2-E4a full Lean-kind sync, USER
  DECREE 2026-08-09, supersedes every earlier version of this list).**
  The blueprint's environments are EXACTLY Lean's own declaration
  kinds — `def`, `class`, `instance`, `abbrev`, `lemma`, `theorem` (+
  `Structure`/`Inductive` added lazily when first needed; `axiom`
  excluded forever by the library's axiom-freedom law) — rendered as
  the LaTeX env names `definition`/`class`/`instance`/`abbreviation`/
  `lemma`/`theorem`/`proof`, heads printed as the WRITTEN-OUT English
  words ("Definition 3", "Class 5", "Instance 2", "Abbreviation 1",
  "Lemma 7", "Theorem 4"), each on its OWN independent counter
  (restarting at 1, incrementing only within its own kind — not a
  shared counter, not per-section). `remark`/`proposition`/
  `corollary`/`example`/`conjecture` are ALL abolished — nothing else
  exists. Retriage: a former proposition/corollary → `lemma`
  (cited-as-infrastructure) or `theorem` (chapter-payoff); a former
  example → an `instance` env (if it witnesses a class) or dissolves
  into plain narrative prose (tables/diagrams allowed, no env, no
  label); a former conjecture → a `theorem` env whose proof body is
  the open marker (below). Re-kinding rule: every item's kind is fixed
  by its PRINCIPAL Lean declaration — a `class`-kind declaration lives
  in `class`; an `instance`-kind declaration lives in `instance`;
  everything else with new mathematical content lives in `definition`
  (internal env name `definition`, no TeX clash with `\def`, head
  "Definition"); a reducible-def name-introduction lives in
  `abbreviation`. `scripts/blueprint.sh`'s CORRESPONDENCE STRUCTURE
  check rejects any surviving dead-kind environment (hard, gate-red);
  the lint hooks advise on one the moment it is typed.
- **The open-theorem convention.** A theorem with no known proof is a
  `theorem` env like any other (never its own environment kind, per
  the conjecture abolition above), paired with a `proof` env whose
  ENTIRE body is the single sentence "Open." — no ad-hoc "-- OPEN"/
  "Status: open" phrasing anywhere, and it never carries `\leanok` on
  either the statement or the proof side (there is nothing formalized
  to mark). `scripts/blueprint.sh` enforces this structurally: an
  "Open."-body proof carrying `\leanok` is a hard violation, and so is
  its paired statement carrying `\leanok`. Current instance:
  `thm:chain-bound` ("How wrong can it get").
- **The bijection law (C2-E4a/A1, USER DECREE 2026-08-09).** The
  LaTeX↔Lean correspondence is one-to-one: every environment that
  carries a `\lean{}` mark at all carries EXACTLY ONE name, its
  principal declaration — never a multi-name list. The map is
  injective envs→decls, NOT surjective: a Lean declaration that is a
  technical companion of the cited principal (a `simp`/`_apply`
  unfolding lemma, a round-trip half of an equivalence, a unit-law or
  left/right-monotonicity twin, a raw/corollary doubling) simply
  becomes an UNMARKED internal — it still exists in Lean, still
  compiles under `scripts/check.sh`, it just is not blueprint-cited.
  Deciding split vs. companion for a formerly multi-name env: if the
  extra names are PEER CLAIMS the statement genuinely bundles (e.g.
  distinct numbered parts, each with its own proof), split the env
  into one per claim, distributing the statement's clauses
  accordingly (purity + anatomy laws make the split well-defined); if
  the extras are companions of one claim, keep the single principal
  name and drop the rest. Bias: fewer envs, more unmarked companions —
  split only genuine peer bundles. `scripts/blueprint.sh` enforces
  this as a hard structural check (a `\lean{}` list of ≥2 names is a
  gate violation, checked before the kind-check step, which then
  checks THAT one name's kind exactly, not "at least one of several").
- **The internal-tag convention (C2-E4a/A2).** Every public Lean
  declaration deliberately left uncited by the bijection law above (a
  demoted companion, or any other pre-existing library-internal
  helper) carries a line comment `-- blueprint: internal (<short
  reason>)` on, or immediately above, its declaration — `private`
  declarations need no tag, since they cannot be cited by anything
  outside their own file regardless. This is what lets a completeness
  census tell "deliberately uncited plumbing" apart from "real
  mathematics nobody wrote an env for": every top-level declaration in
  the NeSyCat namespace is either (a) cited by exactly one env, or (b)
  carries this tag — nothing may be neither.
  `scripts/blueprint.sh`'s CENSUS subsection enforces this over a
  fixed, disclosed file list (`CENSUS_FILES`, currently the
  Truth-value-structures and semiring-monad chapters; extending it to
  the rest of the library, file by file, is each new chapter's own
  ticket's job) via a pragmatic text-based name matcher (not yet a
  full `lake env lean` environment fold) — an unclassified declaration
  is a hard gate violation. Audit fruit — a genuinely uncited,
  genuinely real piece of mathematics the census turns up (not
  plumbing) — gets its own env of the right kind, statement mirroring
  the declaration, `\leanok` statement-side, proof env where
  theorem-kind (example: `def:psum`, the probabilistic sum, found this
  way and given a `definition` env).
- **The three-shape witness doctrine.** A worked instance dissolved
  out of the old `example` kind (per the retriage rule above) takes
  one of three shapes, all via NAMED Lean declarations (never Lean's
  anonymous `example` keyword, which cannot be cited or kind-checked):
  *inhabitation* (an `instance`/`def`-kind witness that a concrete
  carrier satisfies a class — cite the `instance`); *separation* (a
  negative theorem with an explicit witness, e.g. a counterexample —
  cite the `theorem`); *computation* (an equation lemma evaluating a
  construction at concrete data — cite the `theorem`). Whichever shape
  applies, the env is `instance` only for the inhabitation case;
  separation and computation stay plain narrative prose (with a
  `\lean{}`-marked `theorem`/`lemma` if the fact is itself citable
  infrastructure, or no env at all if it is purely illustrative).
- **Remarks are abolished.** The document reads as a STORY: formal
  environments (`definition`, `class`, `instance`, `abbreviation`,
  `lemma`/`theorem` + `proof`) floating in continuous narrative prose.
  Anything with no Lean counterpart — provenance credits, notational
  conventions, dictionary glosses, contrasts, forward pointers, worked
  narrative examples — is plain untagged text immediately before or
  after the formal environment it concerns, never its own
  `\begin{remark}`/`\begin{example}`. Condensation of this discourse
  prose is licensed (shorter is better) as long as no mathematical
  claim is dropped or altered and provenance is never silently deleted
  — it moves. Honesty records (errata, scope/faithfulness disclosures)
  MUST survive as prose, condensed but never deleted.
  `\uses`/`\lean`/`\label`/`\leanok` always stay inside the environment
  they mark (leanblueprint needs `\uses` inside the env for the
  dependency graph).
- **Total Lean-mirror purity.** Every environment with a Lean
  counterpart — `lemma`/`theorem` (statement), `definition`, `class`,
  `instance`, `abbreviation`, and `proof` — contains ONLY the
  mathematical content its cited Lean declaration/proof contains:
  structure fields, laws, hypotheses, conclusion, carrier, or (for
  `proof`) the informal mirror of the Lean proof's own steps.
  Provenance tags (bracketed source citations), dictionary glosses,
  contrast commentary ("unlike a ... no distributivity is assumed"),
  and forward/backward pointers are OUT — they move to plain prose
  immediately before or after the env, condensed and deduped across a
  run of items sharing the same citation where that reads better as a
  story, never dropped. An open theorem gets the same commentary
  treatment for uniformity, governed otherwise by statement-
  minimality. **Pinned exemption:** `def:domain-signature-notation`
  ("Writing convention for typed symbols", Domain layer) is the one
  `definition` environment with no Lean counterpart, by explicit user
  decision predating and surviving this law for this specific item —
  the sweep, the lint advisory, and the kind-check gate all exempt it
  by label, and it is never dissolved into prose. Enforced
  advisory-side by the lint hooks' commentary/provenance marker scan
  (bracketed `[NeSy26`/`[Girard`/... tags, or phrases like "Distilled
  from", "unlike a", "transported along", "see Remark", "the source");
  the hard structural gate lives in `scripts/blueprint.sh`'s
  CORRESPONDENCE section (env/kind agreement, the bijection law, and
  the dead-kind checks above).
- **Statement/proof anatomy.** A `lemma`/`theorem` statement env
  contains exactly what the Lean statement contains: for an
  existential or negative claim ("does not distribute", "is not
  idempotent"), that is the `∃`/`¬`-form itself, with NO witness
  values and no worked computation. Witness choices, numeric
  instantiations, and the arithmetic that verifies them belong in the
  `proof` env, matching the Lean proof's own `refine ⟨...⟩`/`norm_num`
  shape. "Concretely, at $p=q=r=\tfrac12$, ..." inside a statement is
  proof content in the wrong box — it always moves down into the
  `\begin{proof}`.
- **Definition atomicity.** Every `definition`/`class` environment
  introduces exactly one named structure. A family of variant
  refinements (commutative / bounded / bounded-commutative;
  C-variants of a class) each get their own env, `\uses`-linked to the
  atom(s) they refine — never bundled into one env with the base
  structure.
- **No worked instances in definitions.** A `definition`/`class`
  environment states the structure only: no worked instances,
  running-instance itemizations, or anti-examples. That content moves
  to an `instance` env (per the three-shape witness doctrine above) or
  plain prose placed after the definition(s)/class(es) it
  instantiates, `\uses`-linked back to them.

## Work strategy

- Prioritize named definitions/theorems/constructions over exercises;
  exercises come second.
- A partial proof with `sorry` branches beats abandoning the item
  entirely.
- Don't endlessly hunt for easy wins, and don't get stuck more than 2
  hours on a single item — leave a `sorry` with notes explaining what
  you tried and move on to the next item.

## Progress ledger

Keep `PROGRESS.md` current. One status line per section, using exactly
these six statuses:

`not-started -> stubs -> stated -> partial -> proved -> complete(+exercises)`

## Resume protocol (start of EVERY session)

Before editing anything:

1. Read `FORMALIZE.md` (this file) in full.
2. Read `PROGRESS.md` to see current status per section.
3. Read `blueprint/src/content.tex` for per-item status (`\lean`/
   `\leanok` marks).
4. Run `scripts/sorry-report.sh` to see the current sorry/violation
   count.
5. Run `git log --oneline -20` to see recent history.

Only after all five steps should you start editing.

## Work loop

1. Pick the highest-priority unfinished item per `PROGRESS.md`.
2. Implement it in the relevant `NeSyCat/` module (topic folders as
   needed; the blueprint item's `\label` names the target).
3. Run `scripts/check.sh` (module-scoped, then full project before
   committing).
4. Once the item is `\leanok` (fully proved, no `sorry`): tighten the
   blueprint text against the formalized form — the "absolutely lean"
   motto above — trimming hedges, matching the Lean statement's exact
   hypotheses/conclusion shape, and preferring the proof's own natural
   argument over a looser gloss written before the proof existed. Run
   `scripts/blueprint.sh` and confirm `CORRESPONDENCE: OK`.
5. Commit (small, with the message format above; stage the tightened
   `blueprint/src/content.tex` alongside the Lean change, or add a
   `Blueprint-sync:` line if step 4 found nothing to tighten — see the
   Blueprint-sync commit law above).
6. Update `PROGRESS.md`.
7. Repeat. Work as long as possible without stopping to ask questions.

## Tooling

Two tool layers are available. Neither replaces this file; both serve
it.

- **lean-lsp-mcp** (project-scoped MCP, tools prefixed `lean_*`).
  During proof work, prefer `lean_goal` (goal state at a position) and
  `lean_diagnostic_messages` over full rebuilds — they're cheap,
  incremental, and don't wait on `lake build`. Use `lean_local_search` /
  LeanSearch / Loogle for lemma discovery before writing a proof from
  scratch (faithfulness rule still applies). `scripts/check.sh` remains
  the ONLY commit gate — MCP diagnostics are a fast inner-loop signal,
  never a substitute for a green full check before committing.

- **lean4 plugin** (user-scope, `cameronfreer/lean4-skills`). Per-item
  inner loop may use `/lean4:prove`-style cycles for the goal-state
  grind on a single item. HARD RULE — the disprove guard: if an item
  resists two serious proof attempts, run a `/lean4:disprove`-style
  counterexample search on the STATEMENT before grinding further. If a
  counterexample surfaces, the formalization is unfaithful — re-derive
  from the blueprint item and its cited source, fix it, and note the
  correction in the commit message. Axiom audit
  before marking any section `proved`/`complete`: only `propext`,
  `Classical.choice`,
  `Quot.sound` are acceptable (matches the no-`axiom` hard ban above).
  Optional `/lean4:golf` AFTER a proof is green and committed — never
  before committing (never-lose-work).

- **Precedence.** On any conflict between this file and a skill/tool
  suggestion, FORMALIZE.md wins: the scope rail, the sorry policy, and
  the commit law above are not negotiable inputs to a tool's workflow.
