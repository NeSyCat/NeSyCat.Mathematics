---
name: boot
description: Boot a host repo's Lean 4 formalization stack under this harness's contract: verify every component, show the status dashboard and campaign snapshot, then ask what to prove next. The standard way to start a session in a repo carrying this harness.
---

# /boot

Boot entry point for a repo carrying this harness's contract. Runs a
full preflight, renders a status dashboard and campaign snapshot, then
hands off to a mission choice. This skill hands off to `campaign`
(multi-item orchestration) and `grind` (a single hands-on work
session).

**Recommendation for host repos**: add a thin, project-named alias
skill (e.g. a `/<project>-math` skill whose body is one line pointing
at `/boot`) so contributors get a memorable, on-brand entry point —
this is how the harness's own source repository wires it.

## Host-repo contract

Before running anything, verify the host repo provides:

- A rules-of-work file (`FORMALIZE.md` or equivalently named) at the
  repo root.
- `PROGRESS.md` at the repo root — the per-section status ledger.
- The informal layer being formalized: either a target document under
  `target/` (a pinned LaTeX source), or — preferred — a leanblueprint
  `blueprint/` as the canonical library document, with sources cited
  bibliographically and pinned by git ref only when an authoring or
  verification pass needs the text, checked via a
  `scripts/blueprint.sh`-style build+decl gate.
- `scripts/check.sh` — the fast build/checker script.
- `scripts/sorry-report.sh` — the sorry/axiom-violation tracker.

**If any piece is missing, fail gracefully and explicitly**: list
exactly which piece(s) of the contract are absent, do not invent a
substitute, do not edit any files, and stop before Phase 1. Do not
proceed to a partial dashboard against a repo missing its contract.

## PHASE 1 — PREFLIGHT

Run every item below. **A failure of one item never aborts the
others** — collect all results and report them together in Phase 2.

- Toolchain: `export PATH="$HOME/.elan/bin:$PATH"; elan --version &&
  lean --version && lake --version`.
- Build/checker: `scripts/check.sh` — expect its documented success
  signal (exit 0, no `error:` lines).
- Sorry tracker: `scripts/sorry-report.sh` — capture its summary
  block (total sorry count, violation count).
- Harness integrity: confirm the rules-of-work file, `PROGRESS.md`,
  and the target document under `target/` exist; confirm every file
  under `scripts/*.sh` and any host `.claude/hooks/*` is executable;
  validate `python3 -m json.tool .claude/settings.json` and
  `python3 -m json.tool .mcp.json` both parse, if present.
- Correspondence gate: if the host repo carries a leanblueprint
  `blueprint/src/content.tex`, confirm `scripts/blueprint.sh` prints a
  `CORRESPONDENCE: OK` line (structural editorial-law checks plus a
  Lean-kind assertion per `\lean{}` name) before its final success
  signal — not just the build/decl-check portion.
- Feedback-loop hook: if the host repo ships a
  `scripts/git-hooks/commit-msg` (or this plugin's `hooks/commit-msg`),
  confirm `.git/hooks/commit-msg` exists and is byte-identical to it.
  If missing or stale, instruct: copy it into `.git/hooks/commit-msg`
  and `chmod +x` it — without this, a Lean-only commit can silently
  skip the blueprint-tightening feedback loop.
- Git: `git status --short`, `git log --oneline -5`, current branch —
  note any uncommitted changes as a warning, not a failure.
- Grind mode: `scripts/grind-mode.sh` with no arguments, if the host
  repo provides it — report armed/disarmed.
- MCP: confirm `.mcp.json` contains `lean-lsp`, if present; then check
  whether the `lean_*` tools are actually connected in this session
  (e.g. `ToolSearch` for `"lean_goal"`). If configured but not
  connected, report "configured; approve/connect at session start"
  rather than treating it as a failure.
- Plugins: `ls ~/.claude/plugins/marketplaces/lean4-skills` succeeds;
  the `fable-foreman` skill is visible in this session's skill list;
  `/grind` and `/campaign` skills are present (from this plugin, or a
  host-repo equivalent).

## PHASE 2 — DASHBOARD

Render a `component | state | note` table covering: toolchain, build,
sorries/violations, harness files, hooks, MCP (lean-lsp), lean4
plugin, fable-foreman, `/grind`, `/campaign`, grind mode, git.

Follow the table with **one short paragraph** on how the stack
composes: the foreman plans and routes → `/campaign` doctrine →
`/grind` + the grinder agent do the work → lean4 plugin skills craft
individual proofs → lean-lsp senses goal states → the checker agent
verifies.

Then render the **CAMPAIGN SNAPSHOT**: per-section status pulled from
`PROGRESS.md`, and the next 2–3 candidate items from the target
document under `target/` not yet formalized.

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
