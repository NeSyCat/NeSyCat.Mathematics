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
  `scripts/blueprint.sh` and confirm it prints `BLUEPRINT: GREEN`
  before committing (`scripts/check.sh` remains the Lean commit gate).
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

- Every formal item gets a doc comment of the form:
  `/-- Blueprint <tex-label> (<name>): <informal statement>. -/`, where
  `<tex-label>` is the blueprint `\label` key for that item in
  `blueprint/src/content.tex`.
- Faithfulness has two legs: (1) Lean statement ↔ blueprint statement —
  exact, library items are stated per the blueprint (the canonical
  informal document); (2) blueprint item ↔ its cited source — each
  blueprint item cites its source bibliographically (e.g.
  "[NeSy26, App. A]"); divergences are declared in-item; pinned texts
  used for an authoring or verification pass live at recorded git refs
  (ledger + blueprint preamble), not as standing copies. Items may be
  stated at natural generality beyond a single cited source's concrete
  case; a paper's case then appears as an instance/corollary, and any
  such divergence is declared, not silent.
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
4. Commit (small, with the message format above).
5. Update `PROGRESS.md`.
6. Repeat. Work as long as possible without stopping to ask questions.

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
