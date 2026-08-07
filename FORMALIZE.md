# FORMALIZE.md — Rules of Work

This file is the authoritative work-instruction document for any agent
session doing formalization work in this repository. It is the Lean 4
analog of the rules-of-work file described in Urban's "130k Lines of
Formal Topology in Two Weeks" (arXiv:2601.03298): a fast checker, a
sorry/admit tracker, a per-section progress ledger, and git as the
never-lose-work backup system. Follow it exactly. Work as long as
possible without stopping to ask questions.

## Scope rail (STRICT)

- You may create/edit files only under `NeSyCat/Pilot/` and may edit
  `PROGRESS.md`.
- `NeSyCat.lean` may ONLY be touched to add new
  `import NeSyCat.Pilot.<NewFile>` lines when you create a new module.
- NEVER edit: `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`,
  `scripts/`, `target/`, `references/`, `.github/`, `.foreman/`,
  `.gitignore`.
- NEVER run `lake update`.

## Never lose work

- Never run `git reset --hard`, `git revert`, `git checkout -- <file>`,
  or delete a compiling proof or definition.
- If you restructure a file, salvage every compiling theorem and
  definition — move it, don't drop it.
- Any commit that DECREASES the total line count of `NeSyCat/Pilot/`
  must explicitly justify the decrease in its commit message. Cite
  Urban's rule 5: an agent once silently threw away 9k lines of working
  formalization. Do not repeat that mistake.

## Checker discipline

- After every meaningful edit, run `scripts/check.sh` (whole project)
  or `scripts/check.sh NeSyCat.Pilot.<Module>` (one module, faster).
- Success = exit code 0 and no `error:` lines in the output (the script
  prints `CHECK: GREEN` on success, `CHECK: RED (exit <code>)` on
  failure).
- Commit small and often. Each commit message should have:
  1. a one-line summary,
  2. a short description of what changed,
  3. the sorry-count delta (before/after, from `scripts/sorry-report.sh`).
- Include the `Co-Authored-By:` footer per session convention if one is
  in use.

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
  `/-- Leinster <number> (<name>): <informal statement>. -/`
- Before adding ANY definition or theorem:
  1. `grep` `NeSyCat/Pilot/` for duplicates of the same item.
  2. Search Mathlib for existing versions (`exact?`, `apply?`, `rw?`,
     or https://leansearch.net).
- Mathlib may be used freely as BACKGROUND machinery (e.g. `Category`,
  `Functor`, `NatTrans` from `Mathlib.CategoryTheory`). But a target
  item from `target/pilot.md` must be STATED in the `NeSyCat.Pilot`
  namespace and given a REAL proof. A bare one-line `exact <Mathlib
  lemma>` citation of the identical statement defeats the pilot's
  purpose — construct the proof, even if it uses Mathlib lemmas as
  steps.

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
3. Run `scripts/sorry-report.sh` to see the current sorry/violation
   count.
4. Run `git log --oneline -20` to see recent history.

Only after all four steps should you start editing.

## Work loop

1. Pick the highest-priority unfinished item per `PROGRESS.md`.
2. Implement it in the relevant `NeSyCat/Pilot/Sec1_*.lean` file.
3. Run `scripts/check.sh` (module-scoped, then full project before
   committing).
4. Commit (small, with the message format above).
5. Update `PROGRESS.md`.
6. Repeat. Work as long as possible without stopping to ask questions.
