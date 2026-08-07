---
name: grind
description: Run a campaign work session per FORMALIZE.md (resume protocol, work loop, checker discipline). Use for any request to continue/do formalization work in this repo.
argument-hint: [§section | status]
---

# /grind

This skill runs a campaign work session against this repo's Urban-style
harness. It does not summarize or paraphrase the rules — it tells you
where to read them, because the authoritative rules live in
`${CLAUDE_PROJECT_DIR}/FORMALIZE.md` and must be followed exactly, in
full, every session.

Supporting files are **not** auto-discovered by the harness. You must
explicitly read them yourself:

- `${CLAUDE_PROJECT_DIR}/FORMALIZE.md` — the rules of work (scope rail,
  never-lose-work, checker discipline, sorry policy, faithfulness,
  work strategy, progress ledger, resume protocol, work loop).
- `${CLAUDE_PROJECT_DIR}/PROGRESS.md` — per-section status ledger.
- `${CLAUDE_PROJECT_DIR}/blueprint/src/content.tex` — the canonical
  library document: item list, `\label` keys, bibliographic provenance
  citations (sources git-ref pinned where recorded), and anything
  marked `SKIP:`.

## If the argument is `status`

Do a read-only status check, then stop — do not enter the work loop:

1. Read `${CLAUDE_PROJECT_DIR}/PROGRESS.md`.
2. Run `${CLAUDE_PROJECT_DIR}/scripts/sorry-report.sh`.
3. Run `git log --oneline -10`.
4. Summarize: per-section status, current sorry/violation counts, and
   the last few commits. Do not edit anything.

## Otherwise: run a full work session

1. **Resume protocol** (FORMALIZE.md, "Resume protocol" section) —
   before editing anything:
   - Read `FORMALIZE.md` in full.
   - Read `PROGRESS.md`.
   - Run `scripts/sorry-report.sh`.
   - Run `git log --oneline -20`.
2. **Work loop** (FORMALIZE.md, "Work loop" section) — pick the
   highest-priority unfinished item per `PROGRESS.md`, implement it,
   run `scripts/check.sh` (module-scoped, then whole-project before
   committing), commit small with the required message format
   (summary, description, sorry-count delta, `Co-Authored-By:` footer
   if in use), update `PROGRESS.md`, repeat.
3. Obey every rule in FORMALIZE.md while doing so: the scope rail, the
   never-lose-work rules, the sorry policy and its hard bans, and the
   faithfulness requirements (dedupe against `NeSyCat/`, search
   Mathlib, state target items in the plain `NeSyCat` namespace with a
   real proof; legacy pilot work: `NeSyCat/Pilot/`).

### Optional focus argument: `§section`

If invoked as `/grind §1.2` (or any specific section reference),
treat that as Urban's "special rule for today": narrow the work loop to
that section only. Work it until it is finished (per its item list in
`blueprint/src/content.tex`) or you are genuinely blocked (2+ hours
stuck on one item per the work-strategy rule) — do not wander into
other sections.
All other FORMALIZE.md rules still apply unchanged; the focus argument
only changes item selection in step 2 of the work loop, nothing else.

Work as long as possible without stopping to ask questions, per
FORMALIZE.md's own instruction.
