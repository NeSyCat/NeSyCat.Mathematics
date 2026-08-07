---
name: grind
description: Run a campaign work session per the host repo's rules-of-work file (resume protocol, work loop, checker discipline). Use for any request to continue/do formalization work in a repo that carries this harness's contract.
argument-hint: [§section | status]
---

# /grind

This skill runs a campaign work session against a Lean 4 + Mathlib
autoformalization harness, Urban-style (arXiv:2601.03298): a fast
checker, a sorry/admit tracker, a per-section progress ledger, and git
as the never-lose-work backup system.

It does not summarize or paraphrase the rules — it tells you where to
read them, because this skill is generalized by convention over
configuration: the authoritative rules live in the HOST REPO, not in
this plugin.

## Host-repo contract

Before doing anything else, verify the host repo provides all of the
following:

- `FORMALIZE.md` (or an equivalently-named rules-of-work file) at the
  repo root — the authoritative work instructions: scope rail,
  never-lose-work rules, checker discipline, sorry policy and hard
  bans, faithfulness requirements, work strategy, progress ledger
  format, resume protocol, work loop.
- `PROGRESS.md` at the repo root — the per-section status ledger.
- The informal layer being formalized (item numbers, kinds, faithful
  statements, anything marked `SKIP:`): either a target document under
  `target/` (a pinned LaTeX source), or — preferred — a leanblueprint
  `blueprint/` as the canonical library document, with sources cited
  bibliographically and pinned by git ref only when an authoring or
  verification pass needs the text, checked via a
  `scripts/blueprint.sh`-style build+decl gate.
- `scripts/check.sh` — the fast build/checker script. Exit 0 with no
  `error:` lines is success.
- `scripts/sorry-report.sh` — the sorry/axiom-violation tracker.

**If any of these is missing, fail gracefully and explicitly**: state
which piece(s) of the contract are absent, do not guess at
replacements, do not edit any files, and stop. Do not invent a
FORMALIZE.md-equivalent from scratch — that decision belongs to the
repo's maintainers.

## If the argument is `status`

Do a read-only status check, then stop — do not enter the work loop:

1. Read the host repo's `PROGRESS.md`.
2. Run `scripts/sorry-report.sh`.
3. Run `git log --oneline -10`.
4. Summarize: per-section status, current sorry/violation counts, and
   the last few commits. Do not edit anything.

## Otherwise: run a full work session

1. **Resume protocol** — before editing anything:
   - Read the host repo's rules-of-work file in full.
   - Read `PROGRESS.md`.
   - Run `scripts/sorry-report.sh`.
   - Run `git log --oneline -20`.
2. **Work loop** — pick the highest-priority unfinished item per
   `PROGRESS.md`, implement it, run `scripts/check.sh` (module-scoped
   if the host script supports it, then whole-project before
   committing), commit small with the message format the rules-of-work
   file specifies (summary, description, sorry-count delta,
   `Co-Authored-By:` footer if in use), update `PROGRESS.md`, repeat.
3. Obey every rule in the host repo's rules-of-work file while doing
   so: its scope rail, its never-lose-work rules, its sorry policy and
   hard bans, and its faithfulness requirements take precedence over
   any suggestion this skill or any other tool makes.

### Optional focus argument: `§section`

If invoked as `/grind §1.2` (or any specific section reference), treat
that as Urban's "special rule for today": narrow the work loop to that
section only. Work it until it is finished (per the host repo's item
list) or you are genuinely blocked per the host repo's own
work-strategy rule — do not wander into other sections. All other
host-repo rules still apply unchanged; the focus argument only changes
item selection in step 2 of the work loop, nothing else.

Work as long as possible without stopping to ask questions, per the
host repo's own instruction (if it says so — defer to it).
