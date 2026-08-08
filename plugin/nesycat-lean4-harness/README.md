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
- `skills/campaign/` — the `/campaign` skill: plan-first orchestrator
  doctrine for multi-item campaigns, composed on top of the
  `fable-foreman` contract (haiku scouts, sonnet grinders, opus/fable
  escalation, blind verification).
- `skills/boot/` — the `/boot` skill: preflight the whole stack,
  render a status dashboard and campaign snapshot, then ask what to
  prove next. The recommended way to start a session in a host repo.
- `agents/lean-prover.md` — a delegated formalization grinder.
- `agents/lean-checker.md` — a read-only blind verifier that never
  edits.
- `hooks/hooks.json` + hook scripts — `guard-scope` (PreToolUse
  scope-rail enforcement), `lint-lean` (PostToolUse hard-ban / sorry
  policy check, plus advisory blueprint-label and feedback-loop
  reminders when the host repo carries a leanblueprint), `lint-blueprint`
  (PostToolUse editorial-law smells on edited `blueprint/src/*.tex`:
  markless abbreviation, promotion-candidate remark, `\uses{rem:...}`,
  proofless theorem-family environment — advisory only), `session-start`
  (status digest at session start), `grind-stop` (Stop-hook re-prompt
  loop for unattended grind mode).
- `hooks/commit-msg` — a git `commit-msg` hook (NOT registered in
  `hooks.json`; it is a git hook, not a Claude Code tool hook). For a
  host repo carrying a leanblueprint, it is the absolute blocker for the
  blueprint<->Lean feedback loop: a commit that touches a Lean
  declaration cited by a `\lean{}` mark must either stage
  `blueprint/src/content.tex` alongside it or carry a commit-message
  line starting `Blueprint-sync: <reason>`. Host repos install it with
  `cp hooks/commit-msg .git/hooks/commit-msg && chmod +x
  .git/hooks/commit-msg` — plugins cannot install git hooks
  automatically.

## Host-repo contract

This plugin is generalized by convention over configuration. It has no
NeSyCat-specific paths. A host repo that wants to use it must provide:

- `FORMALIZE.md` (or equivalently-named rules-of-work file) at the
  repo root.
- `PROGRESS.md` at the repo root — the per-section status ledger.
- The informal layer being formalized: either a target document under
  `target/` (a pinned LaTeX source), or — preferred — a leanblueprint
  `blueprint/` as the canonical library document, with sources cited
  bibliographically and pinned by git ref only when an authoring or
  verification pass needs the text, checked via a
  `scripts/blueprint.sh`-style build+decl gate.
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

## The stack

Four layers compose to run a formalization campaign, each doing one
job:

- **This plugin** (`nesycat-lean4-harness`) — campaign law and boot:
  `/grind` (single work session), `/campaign` (orchestration
  doctrine), `/boot` (preflight + dashboard + mission menu), the
  scope-rail and sorry-policy hooks, and the `lean-prover` /
  `lean-checker` agents.
- **`fable-foreman`** (Claude Code plugin) — the orchestration
  contract `/campaign` composes with: job-site probing, ticket
  writing, blind verification, escalation precedence. Required for
  full `/campaign` behavior; `/campaign` degrades gracefully to an
  inline equivalent if it isn't installed.
- **[`cameronfreer/lean4-skills`](https://github.com/cameronfreer/lean4-skills)**
  — inner-loop craft: `/lean4:prove`, `/lean4:disprove`,
  `/lean4:golf`, `/lean4:checkpoint`, one item at a time.
- **[`oOo0oOo/lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp)**
  — LSP senses: `lean_goal`, `lean_diagnostic_messages`,
  `lean_local_search`, and friends for fast incremental feedback
  without a full rebuild.

Host repos are recommended to add a thin, project-named alias skill
for `/boot` (e.g. this harness's own source repository wires
`/nesycat-math` as a one-line alias) so contributors get a memorable,
on-brand entry point.

## Credits

- Urban, *"130k Lines of Formal Topology in Two Weeks"*
  (arXiv:2601.03298) — the rules-of-work / fast-checker / never-lose-work
  methodology this harness mechanizes.
- [`cameronfreer/lean4-skills`](https://github.com/cameronfreer/lean4-skills)
  — the complementary inner-loop pack (`lean4:prove`, `lean4:disprove`,
  `lean4:golf`, `lean4:checkpoint`, and more).

## License

Inherits the repository license (currently unset).
