# NeSyCat Lean4 Harness

A packaged, marketplace-format plugin distilled from this repository's
own `.claude/` configuration: the CAMPAIGN layer for a Lean 4 + Mathlib
autoformalization effort — a durable rules-of-work file, a
per-section progress ledger, host-enforced law via hooks, and an
unattended grind loop. It complements, and never duplicates,
[`cameronfreer/lean4-skills`](https://github.com/cameronfreer/lean4-skills)'s
`lean4` plugin, which is the INNER-LOOP craft: goal-state prove
cycles, counterexample search, axiom audits, one item at a time. The
two compose: this plugin drives the campaign; `lean4:prove`,
`lean4:disprove`, `lean4:golf`, and friends do the per-item work inside
it.

## What it is

- `skills/grind/` — the `/grind` skill: resume protocol, work loop,
  checker discipline, status mode, optional `§section` focus.
- `agents/lean-prover.md` — a delegated formalization grinder.
- `agents/lean-checker.md` — a read-only blind verifier that never
  edits.
- `hooks/hooks.json` + four hook scripts — `guard-scope` (PreToolUse
  scope-rail enforcement), `lint-lean` (PostToolUse hard-ban / sorry
  policy check), `session-start` (status digest at session start),
  `grind-stop` (Stop-hook re-prompt loop for unattended grind mode).

## Host-repo contract

This plugin is generalized by convention over configuration. It has no
NeSyCat-specific paths. A host repo that wants to use it must provide:

- `FORMALIZE.md` (or equivalently-named rules-of-work file) at the
  repo root.
- `PROGRESS.md` at the repo root — the per-section status ledger.
- A target document under `target/` — the informal source being
  formalized.
- `scripts/check.sh` — the fast build/checker script (exit 0, no
  `error:` lines, on success).
- `scripts/sorry-report.sh` — the sorry/axiom-violation tracker.

If any piece is missing, the skill and agents fail gracefully and
explicitly: they name what's absent, edit nothing, and stop, rather
than inventing a substitute.

## Install

From a checkout of this repository:

```
/plugin install ./plugin/nesycat-lean4-harness
```

Or, once published to a marketplace, via the marketplace flow
(`/plugin marketplace add ...` then `/plugin install
nesycat-lean4-harness@<marketplace>`).

**Warning:** a repository that already carries these hooks directly
under its own `.claude/` (as this repository does) must NOT also
install this plugin — the `PreToolUse`/`PostToolUse`/`SessionStart`/
`Stop` hooks would run twice, doubling every guard check and grind-mode
re-prompt. This plugin is packaged for OTHER repositories that want the
same harness; it is not installed or activated in this repository.

## Credits

- Urban, *"130k Lines of Formal Topology in Two Weeks"*
  (arXiv:2601.03298) — the rules-of-work / fast-checker / never-lose-work
  methodology this harness mechanizes.
- [`cameronfreer/lean4-skills`](https://github.com/cameronfreer/lean4-skills)
  — the complementary inner-loop pack (`lean4:prove`, `lean4:disprove`,
  `lean4:golf`, `lean4:checkpoint`, and more).

## License

Inherits the repository license (currently unset).
