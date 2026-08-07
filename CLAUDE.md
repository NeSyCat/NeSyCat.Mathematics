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
