---
name: campaign
description: Plan-first foreman orchestration for formalization campaigns: mandatory planning for new sections/major theorems, then routed dispatch (haiku scouts, sonnet grinders, opus/fable escalation) with blind verification. For orchestrating multi-item proof campaigns — for a single hands-on work session use /grind instead.
---

# /campaign

Orchestrator-facing doctrine for running a multi-item formalization
campaign against this repo's Urban-style harness. It composes with,
and never replaces, the `fable-foreman` orchestration contract.

## 1. LAYER RULE

This skill runs in the **ORCHESTRATOR session only**. Never invoke it
inside a worker/subagent — a `lean-prover` grinder or `lean-checker`
verifier session must never load `/campaign`. Workers never spawn
workers.

## 2. FOREMAN COMPOSITION

If the `fable-foreman` skill is available in this session, invoke it
**FIRST** and follow its full contract: the job-site probe, the
ledger, 7-section tickets with an explicit WRITE SET, the status
vocabulary (`DONE` / `DONE_WITH_CONCERNS` / `NEEDS_CONTEXT` /
`BLOCKED`), verdict-first blind verification, and the precedence
table governing retries and escalation. This skill only **adds**
formalization doctrine on top — it never substitutes for that
contract.

If `fable-foreman` is **not** available in the session, apply the same
contract inline: seat `lean-prover` (`.claude/agents/lean-prover.md`)
as the grinder, seat `lean-checker` (`.claude/agents/lean-checker.md`)
as the blind verifier, and still write tickets, track a ledger, and
verify verdict-first before accepting any batch.

## 3. PLAN-FIRST MANDATE (non-negotiable)

Before dispatching work on any of:

- (a) any not-yet-started section (per `PROGRESS.md`),
- (b) any single theorem estimated at more than 100 proof lines, or
- (c) any item with encoding ambiguity,

**enter plan mode** and produce a plan covering:

- the informal statement(s) reviewed against both the blueprint item
  in `blueprint/src/content.tex` (the canonical library document) and
  its bibliographically cited source (git-ref pinned where recorded);
- encoding choices — Mathlib background to lean on, namespace,
  statement shape, composition-order conventions;
- item order and dependency structure within the batch;
- an escalation budget per item (how many sonnet attempts before
  opus/fable);
- acceptance criteria for the blind verifier.

**Present the plan for user approval before any dispatch.** Do not
skip this step because an item "looks easy" — the estimate itself is
what triggers planning.

## 4. ROUTING TABLE

| Seat            | Role                                                                                          |
|-----------------|-------------------------------------------------------------------------------------------------|
| `haiku`         | Read-only scouting: target-vs-`PROGRESS.md` gap inventory, duplicate greps, sorry census, dependency mapping. Never edits. |
| `sonnet`        | Default proving seat: stating items, standard proofs, exercises. Dispatch as `lean-prover`.    |
| `opus` or `fable` | Escalation seat: a proof that survived two serious sonnet attempts, encoding adjudication, or statement-faithfulness disputes. |
| `lean-checker`  | Blind verification of every accepted batch. Reports verdict-first: `PASS` / `FAIL` / `PASS_WITH_NOTES`. |

Use these aliases stably across a campaign — do not invent new seat
names mid-campaign.

## 5. DISCIPLINE

- Batch grinder tickets 2–4 related items each — never a lone
  one-item ticket when related items exist in the same section.
- Batch verifier findings into **ONE** fix ticket per batch, not one
  ticket per finding.
- Never a third identical retry on the same item — two serious
  attempts, then escalate per the routing table.
- Escalations are one-way: once an item moves to opus/fable, it does
  not go back down to sonnet within the same campaign.
- Verify from a **committed clean tree** — never verify against
  uncommitted or dirty worker output.
- Orchestrator confirms workers applied the disprove guard and the
  axiom audit (`FORMALIZE.md`, "Tooling" section) by checking their
  report evidence, not by trusting the claim.

## Supporting files (read these — not auto-discovered)

- `${CLAUDE_PROJECT_DIR}/FORMALIZE.md` — the rules of work this
  campaign doctrine sits on top of.
- `${CLAUDE_PROJECT_DIR}/PROGRESS.md` — per-section status ledger;
  drives plan-first triggers (a) and item selection.
- `${CLAUDE_PROJECT_DIR}/blueprint/src/content.tex` — the canonical
  library document (labels, `\lean`/`\leanok` status, bibliographic
  provenance citations, sources git-ref pinned where recorded) — the
  source of truth for encoding review alongside the blueprint item.
