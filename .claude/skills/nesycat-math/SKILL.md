---
name: nesycat-math
description: Boot the NeSyCat.Mathematics formalization stack: verify every component, show the status dashboard and campaign snapshot, then ask what to prove next. The standard way to start any session in this repo.
---

# /nesycat-math

Boot entry point for this repo. Runs a full preflight, renders a
status dashboard and library snapshot, then hands off to a mission
choice. Read `${CLAUDE_PROJECT_DIR}/FORMALIZE.md`,
`${CLAUDE_PROJECT_DIR}/PROGRESS.md`, and
`${CLAUDE_PROJECT_DIR}/blueprint/src/content.tex` (the canonical
library document; sources are cited bibliographically therein) as part
of this boot — they are not auto-discovered. This skill hands off to
`campaign` (multi-item orchestration) and `grind` (a single hands-on
work session).

## PHASE 1 — PREFLIGHT

Run every item below. **A failure of one item never aborts the
others** — collect all results and report them together in Phase 2.

- Toolchain: `export PATH="$HOME/.elan/bin:$PATH"; elan --version &&
  lean --version && lake --version`.
- Build/checker: `${CLAUDE_PROJECT_DIR}/scripts/check.sh` — expect
  `CHECK: GREEN`.
- Sorry tracker: `${CLAUDE_PROJECT_DIR}/scripts/sorry-report.sh` —
  capture the `Summary` block (total sorry count, violation count).
- Harness integrity: confirm `FORMALIZE.md`, `PROGRESS.md` exist;
  confirm every file under `scripts/*.sh` and `.claude/hooks/*` is
  executable; validate `python3 -m json.tool .claude/settings.json` and
  `python3 -m json.tool .mcp.json` both parse.
- Blueprint: `~/.venvs/leanblueprint/bin/leanblueprint --version` works;
  `dot -V` works; `scripts/blueprint.sh` is executable and prints
  `CORRESPONDENCE: OK` followed by `BLUEPRINT: GREEN` (the
  blueprint<->Lean correspondence gate, ticket H1).
- Feedback-loop hook: `.git/hooks/commit-msg` exists and is byte-identical
  to `scripts/git-hooks/commit-msg` (`diff .git/hooks/commit-msg
  scripts/git-hooks/commit-msg`). If missing or stale, instruct:
  `cp scripts/git-hooks/commit-msg .git/hooks/commit-msg && chmod +x
  .git/hooks/commit-msg` — this is the absolute blocker that enforces the
  `Blueprint-sync:` commit-message law, and a Lean-only commit will
  silently skip the feedback loop without it.
- Git: `git status --short`, `git log --oneline -5`, current branch —
  note any uncommitted changes as a warning, not a failure.
- Grind mode: `scripts/grind-mode.sh` with no arguments — report
  armed/disarmed.
- MCP: confirm `.mcp.json` contains `lean-lsp`; then check whether the
  `lean_*` tools are actually connected in this session (e.g.
  `ToolSearch` for `"lean_goal"`). If configured but not connected,
  report "configured; approve/connect at session start" rather than
  treating it as a failure.
- Plugins: `ls ~/.claude/plugins/marketplaces/lean4-skills` succeeds;
  the `fable-foreman` skill is visible in this session's skill list;
  `/grind` and `/campaign` are present under `.claude/skills/`.

## PHASE 2 — DASHBOARD

Render a `component | state | note` table covering: toolchain, build,
sorries/violations, harness files, blueprint, hooks, MCP (lean-lsp),
lean4 plugin, fable-foreman, `/grind`, `/campaign`, grind mode, git.

Follow the table with **one short paragraph** on how the stack
composes: the foreman plans and routes → `/campaign` doctrine →
`/grind` + `lean-prover` do the work → lean4 plugin skills craft
individual proofs → lean-lsp senses goal states → `lean-checker`
verifies.

Then render the **LIBRARY SNAPSHOT**: per-item status read from
`blueprint/src/content.tex`'s `\lean`/`\leanok` marks (plus
`PROGRESS.md`), and the next 2–3 candidate items not yet formalized.

If **any** preflight item came back red, surface it prominently
**before** the mission menu and offer to fix it first.

## PHASE 3 — MISSION

Use the `AskUserQuestion` tool with exactly these options:

- **"Continue campaign (Recommended)"** — route to `/campaign` for a
  not-yet-started section, or `/grind` for items already in progress.
- **"Prove a specific theorem"** — user names it; apply the
  plan-first mandate from `/campaign` if it looks major.
- **"Arm grind mode"** — ask for N, run `scripts/grind-mode.sh N`,
  then start `/grind`.
- **"Status only"** — stop after the dashboard; do not dispatch
  anything.
