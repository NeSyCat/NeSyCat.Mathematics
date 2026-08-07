# CLAUDE.md

This repository is an Urban-style autoformalization harness for Lean 4
+ Mathlib, targeting Leinster's *Basic Category Theory*, Chapter 1.

If you are doing formalization work here: read `FORMALIZE.md` first,
treat it as your authoritative work instructions, follow it exactly,
and work as long as possible without stopping to ask questions.

- `target/pilot.md` — what to formalize (the informal target document).
- `PROGRESS.md` — per-section status ledger.
- `scripts/check.sh` — the fast checker; run after every meaningful edit.
- `scripts/sorry-report.sh` — the sorry/axiom tracker; run before and
  after each work unit.

Builds require the elan toolchain on `PATH`:
`export PATH="$HOME/.elan/bin:$PATH"`.

## Deep integration

This repo wires FORMALIZE.md's rules into the Claude Code harness
mechanically, not just as documentation:

- `/formalize [§section | status]` — the skill that runs a work session.
  Bare `/formalize` executes the resume protocol then the work loop;
  `/formalize status` is a read-only progress check; a section argument
  like `/formalize §1.2` narrows the work loop to that section only.
- Grind mode — unattended looping via `scripts/grind-mode.sh N` (arm for
  N iterations, 1-50), `scripts/grind-mode.sh off` (disarm),
  `scripts/grind-mode.sh` (status). Backed by the `Stop` hook
  (`.claude/hooks/grind-stop.sh`), which re-blocks each stop attempt to
  re-prompt continued work until the counter is exhausted.
- Hooks (`.claude/hooks/`): `guard-scope.sh` (`PreToolUse` on Edit|Write)
  denies/asks on edits to protected paths per the scope rail;
  `lint-lean.sh` (`PostToolUse` on Edit|Write) blocks on hard-ban
  violations (`axiom`, `native_decide`) and reminds on a bare `sorry`
  missing its `-- TODO:`; `session-start.sh` (`SessionStart`) surfaces
  `PROGRESS.md`, the sorry-report summary, recent git log, and grind-mode
  status at session start.
- Subagents (`.claude/agents/`): `lean-prover` is the formalization
  grinder; `lean-checker` is a read-only blind verifier that never edits.
- Permissions (`.claude/settings.json`) pre-approve `scripts/check.sh`,
  `lake build`, `scripts/sorry-report.sh`, and read-only/commit git
  operations, and hard-deny `git push`, `git reset`/`revert`/`checkout`/
  `restore`, `lake update`, and `rm -rf`.
