# PROGRESS.md — Pilot Progress Ledger

Tracks the formalization status of each section of the pilot target
(Leinster, *Basic Category Theory*, Chapter 1 — see `target/pilot.md`).
Updated at the end of every work unit per `FORMALIZE.md`.

## Status legend

| Status                | Meaning                                                            |
|------------------------|---------------------------------------------------------------------|
| `not-started`          | No file/content exists for this section yet.                       |
| `stubs`                | File exists; item names/statements sketched, mostly `sorry`.       |
| `stated`               | All in-scope items from `target/pilot.md` are stated (typechecking statements), proofs not yet attempted. |
| `partial`              | Some items proved, some still `sorry`.                             |
| `proved`               | All in-scope Definitions/Lemmas/Theorems for the section are proved (exercises may remain). |
| `complete(+exercises)` | Section fully proved including its exercises.                      |

## Sections

| Section | Topic                     | Lean file                                    | Status      |
|---------|----------------------------|-----------------------------------------------|-------------|
| §1.1    | Categories                 | `NeSyCat/Pilot/Sec1_1_Categories.lean`        | not-started |
| §1.1 ex | Categories — exercises     | `NeSyCat/Pilot/Sec1_1_Categories.lean`        | not-started |
| §1.2    | Functors                   | `NeSyCat/Pilot/Sec1_2_Functors.lean`          | not-started |
| §1.2 ex | Functors — exercises       | `NeSyCat/Pilot/Sec1_2_Functors.lean`          | not-started |
| §1.3    | Natural transformations    | `NeSyCat/Pilot/Sec1_3_NatTrans.lean`          | not-started |
| §1.3 ex | Natural transformations — exercises | `NeSyCat/Pilot/Sec1_3_NatTrans.lean`  | not-started |

## Notes

- `NeSyCat/Pilot/Smoke.lean` is scaffold-only (toolchain smoke test). It
  is not a pilot item and does not appear in this table; it must not be
  edited except by explicit maintenance instruction.
- See `target/pilot.md` for the full itemized list (numbers, kinds, and
  faithful statements) each Lean file is expected to cover, including
  items marked `SKIP:` that are intentionally not being formalized.
- See `FORMALIZE.md` for the resume protocol and work loop.
