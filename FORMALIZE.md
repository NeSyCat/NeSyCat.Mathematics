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

- **Final environment inventory.** The blueprint's only environment
  kinds are: `definition`, `abbreviation`, `lemma`, `theorem`,
  `example`, `conjecture`, `proof` — nothing else. `remark` is
  abolished (see below); `proposition` and `corollary` are abolished
  (C2-E3/A1 kind-sync decree — full LaTeX↔Lean kind synchronization:
  Lean has no `proposition`/`corollary` keyword and treats `lemma` as a
  synonym of `theorem`, so the blueprint's theorem-family narrows to
  exactly `lemma`/`theorem`). Retriage rule for a claim that used to be
  a proposition or corollary: cited-as-infrastructure by later items →
  `lemma`; a section/chapter-payoff statement in its own right →
  `theorem`. `scripts/blueprint.sh`'s CORRESPONDENCE STRUCTURE check
  rejects any surviving `remark`/`proposition`/`corollary` environment
  (hard, gate-red); the lint hooks advise on one the moment it is
  typed.
- **Remarks are abolished.** The document reads as a STORY: formal
  environments (`definition`, `abbreviation`, `lemma`/`theorem` +
  `proof`, `example`, `conjecture`) floating in continuous narrative
  prose. Anything with no Lean counterpart — provenance credits,
  notational conventions, dictionary glosses, contrasts, forward
  pointers — is plain untagged text immediately before or after the
  formal environment it concerns, never its own `\begin{remark}`.
  Condensation of this discourse prose is licensed (shorter is
  better) as long as no mathematical claim is dropped or altered and
  provenance is never silently deleted — it moves. Honesty records
  (errata, scope/faithfulness disclosures) MUST survive as prose,
  condensed but never deleted. `\uses`/`\lean`/`\label`/`\leanok`
  always stay inside the environment they mark (leanblueprint needs
  `\uses` inside the env for the dependency graph).
- **Total Lean-mirror purity.** Every environment with a Lean
  counterpart — `lemma`/`theorem` (statement), `definition`,
  `abbreviation`, an `example` carrying a `\lean{}` mark, and `proof`
  — contains ONLY the mathematical content its cited Lean
  declaration/proof contains: structure fields, laws, hypotheses,
  conclusion, carrier, or (for `proof`) the informal mirror of the
  Lean proof's own steps. Provenance tags (bracketed source
  citations), dictionary glosses, contrast commentary ("unlike a
  ... no distributivity is assumed"), and forward/backward pointers
  are OUT — they move to plain prose immediately before or after the
  env, condensed and deduped across a run of items sharing the same
  citation where that reads better as a story, never dropped.
  Conjectures (no Lean yet) get the same commentary treatment for
  uniformity, governed otherwise by statement-minimality. **Pinned
  exemption:** `def:domain-signature-notation` ("Writing convention
  for typed symbols", Domain layer) is the one definition environment
  with no Lean counterpart, by explicit user decision predating and
  surviving this law for this specific item — the sweep and the lint
  advisory exempt it by label, and it is never dissolved into prose.
  Enforced advisory-side by the lint hooks' commentary/provenance
  marker scan (bracketed `[NeSy26`/`[Girard`/... tags, or phrases like
  "Distilled from", "unlike a", "transported along", "see Remark",
  "the source"); the hard structural gate lives in
  `scripts/blueprint.sh`'s CORRESPONDENCE section (env/kind agreement)
  together with the zero-remark/zero-proposition/corollary checks
  above.
- **Statement/proof anatomy.** A `lemma`/`theorem` statement env
  contains exactly what the Lean statement contains: for an
  existential or negative claim ("does not distribute", "is not
  idempotent"), that is the `∃`/`¬`-form itself, with NO witness
  values and no worked computation. Witness choices, numeric
  instantiations, and the arithmetic that verifies them belong in the
  `proof` env, matching the Lean proof's own `refine ⟨...⟩`/`norm_num`
  shape. "Concretely, at $p=q=r=\tfrac12$, ..." inside a statement is
  proof content in the wrong box — it always moves down into the
  `\begin{proof}`. (`example` environments are exempt: showing a
  concrete instance is their entire point.)
- **Definition atomicity.** Every `definition` environment introduces
  exactly one named structure. A family of variant refinements
  (commutative / bounded / bounded-commutative; C-variants of a class)
  each get their own `definition` environment, `\uses`-linked to the
  atom(s) they refine — never bundled into one env with the base
  structure.
- **No examples in definitions.** A `definition` environment states the
  structure only: no worked instances, running-instance itemizations, or
  anti-examples. That content moves to a `\begin{example}` environment
  placed after the definition(s) it instantiates, `\uses`-linked back to
  them.

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
