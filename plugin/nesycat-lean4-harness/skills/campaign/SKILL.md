---
name: campaign
description: Plan-first foreman orchestration for formalization campaigns: mandatory planning for new sections/major theorems, then routed dispatch (haiku scouts, sonnet grinders, opus/fable escalation) with blind verification. For orchestrating multi-item proof campaigns — for a single hands-on work session use /grind instead.
---

# /campaign

Orchestrator-facing doctrine for running a multi-item formalization
campaign against a host repo carrying this harness's contract. It
composes with, and never replaces, the `fable-foreman` orchestration
contract.

## Host-repo contract

This skill is generalized by convention over configuration — the
authoritative rules live in the host repo, not in this plugin. Before
doing anything else, verify the host repo provides:

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

If any of these is missing, fail gracefully and explicitly: name
what's absent, edit nothing, and stop — do not invent a substitute.

## 1. LAYER RULE

This skill runs in the **ORCHESTRATOR session only**. Never invoke it
inside a worker/subagent — a grinder or verifier session must never
load `/campaign`. Workers never spawn workers.

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
contract inline: seat this plugin's `lean-prover` agent as the
grinder, seat `lean-checker` as the blind verifier, and still write
tickets, track a ledger, and verify verdict-first before accepting any
batch.

## 3. PLAN-FIRST MANDATE (non-negotiable)

Before dispatching work on any of:

- (a) any not-yet-started section (per the host repo's `PROGRESS.md`),
- (b) any single theorem estimated at more than 100 proof lines, or
- (c) any item with encoding ambiguity,

**enter plan mode** and produce a plan covering:

- the informal statement(s) reviewed against both the host repo's
  target document under `target/` and the source book/paper it draws
  from;
- encoding choices — background library machinery to lean on,
  namespace, statement shape, composition-order conventions;
- item order and dependency structure within the batch;
- an escalation budget per item (how many standard-seat attempts
  before escalation);
- acceptance criteria for the blind verifier.

**Present the plan for user approval before any dispatch.** Do not
skip this step because an item "looks easy" — the estimate itself is
what triggers planning.

## 4. ROUTING TABLE

| Seat            | Role                                                                                          |
|-----------------|-------------------------------------------------------------------------------------------------|
| `haiku`         | Read-only scouting: target-vs-`PROGRESS.md` gap inventory, duplicate greps, sorry census, dependency mapping. Never edits. |
| `sonnet`        | Default proving seat: stating items, standard proofs, exercises. Dispatch as this plugin's `lean-prover` agent. |
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
  axiom audit (the host repo's rules-of-work file, "Tooling" section
  or equivalent) by checking their report evidence, not by trusting
  the claim.
