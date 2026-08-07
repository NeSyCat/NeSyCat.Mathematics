# PROGRESS.md — Campaign Progress Ledger

Tracks the formalization status of each cluster of the
NeSyCat library (canonical document `blueprint/src/content.tex`,
sources cited bibliographically therein — see `CLAUDE.md`). Updated at
the end of every work unit per `FORMALIZE.md`.

## Status legend

| Status                | Meaning                                                            |
|------------------------|---------------------------------------------------------------------|
| `not-started`          | No file/content exists for this section yet.                       |
| `stubs`                | File exists; item names/statements sketched, mostly `sorry`.       |
| `stated`               | All in-scope items from the canonical library document are stated (typechecking statements), proofs not yet attempted. |
| `partial`              | Some items proved, some still `sorry`.                             |
| `proved`               | All in-scope Definitions/Lemmas/Theorems for the section are proved (exercises may remain). |
| `complete(+exercises)` | Section fully proved including its exercises.                      |

## §1.x Leinster pilot — ARCHIVED

ARCHIVED — pilot complete at a22830f (descoped by design; 1.1.3-1.1.7 +
1.1.13 proved). Kept in-tree untouched as a completed smoke test; not
part of the active campaign.

| Section | Topic                     | Lean file                                    | Status      |
|---------|----------------------------|-----------------------------------------------|-------------|
| §1.1    | Categories                 | `NeSyCat/Pilot/Sec1_1_Categories.lean`        | partial (1.1.3, 1.1.4, 1.1.5, 1.1.6, 1.1.7 done; 1.1.8/1.1.9/1.1.11 not yet started) |
| §1.1 ex | Categories — exercises     | `NeSyCat/Pilot/Sec1_1_Categories.lean`        | partial (1.1.13 done; 1.1.14 not yet started; 1.1.12/1.1.15 SKIP per pilot target document preserved in git history) |
| §1.2    | Functors                   | `NeSyCat/Pilot/Sec1_2_Functors.lean`          | not-started |
| §1.2 ex | Functors — exercises       | `NeSyCat/Pilot/Sec1_2_Functors.lean`          | not-started |
| §1.3    | Natural transformations    | `NeSyCat/Pilot/Sec1_3_NatTrans.lean`          | not-started |
| §1.3 ex | Natural transformations — exercises | `NeSyCat/Pilot/Sec1_3_NatTrans.lean`  | not-started |

## NeSyCat library

Active library work, canonical document `blueprint/src/content.tex`
(provenance: bibliographic citations, e.g. `[NeSy26, App. A]`, with
pinned texts recorded at their git refs), Lean home `NeSyCat/` (topic
folders as content emerges).

| Cluster                                                                    | Status      |
|-----------------------------------------------------------------------------|-------------|
| Semiring-monad infrastructure (`M_S`, `D` as mass-one submonad)              | partial (def:lattice-semiring stated, Boolean+mass instances done, log instance pending C1-T3; lem:prob-not-semiring proved; def:semiring-monad + thm:semiring-monad-laws proved in `NeSyCat/Monad/SemiringMonad.lean` (`MS`, `ret`, `bind`, `ret_bind`/`bind_ret`/`bind_assoc`, `Tens`); rem:semiring-monad-algebras split out as a stretch target, not proved; def:dist-monad and lem:log-iso not yet started) |
| Truth spaces `M(Bool)`                                                      | not-started |
| Lifted connectives (mass+log, derived `p+q−pq`)                             | not-started |
| Pointwise/linear-laws/copying-laws lemmas + three-layers theorem            | not-started |
| Batch monad + transformer + pointwise evaluation                           | not-started |
| dec/enc/Z suite + tilt lemma + mass preservation + pull-out theorem + normalizer corollaries | not-started |
| Examples (failure numbers, MNIST commute)                                  | not-started |

OPEN: chain version of the tilt bound.

Fine-grained per-item status (labels, `\lean`/`\leanok` marks) lives in
`blueprint/src/content.tex`, not in this table.

## Notes

- `NeSyCat/Pilot/Smoke.lean` is scaffold-only (toolchain smoke test). It
  is not a pilot item and does not appear in the archived table above;
  it must not be edited except by explicit maintenance instruction.
- See the pilot target document (preserved in git history, since
  `a18f13c`) for the archived pilot's full itemized list (numbers,
  kinds, and faithful statements), including items marked `SKIP:` that
  were intentionally not formalized.
- See `FORMALIZE.md` for the resume protocol and work loop.
