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

## NeSyCat library

Active library work, canonical document `blueprint/src/content.tex`
(provenance: bibliographic citations, e.g. `[NeSy26, App. A]`, with
pinned texts recorded at their git refs), Lean home `NeSyCat/` (topic
folders as content emerges).

| Cluster                                                                    | Status      |
|-----------------------------------------------------------------------------|-------------|
| Semiring-monad infrastructure (`M_S`, `D` as mass-one submonad)              | proved (C1-T3: chapter-1 cluster complete — every in-scope Definition/Lemma/Theorem of §"Semiring weight monads" is now `\leanok`, except `rem:semiring-monad-algebras`, which remains an unproved stretch target outside this cluster's scope (no Lean formalization of `MS S`'s algebras is claimed). `def:lattice-semiring` (`LatSRng`/`LatCSRng`/`BLatSRng`/`BLatCSRng` in `NeSyCat/Monad/LatticeSemiring.lean`) now has all three running instances: Boolean (`BLatCSRng`, bounded), mass (`LatCSRng`, unbounded), and NEW log (`instLatCSRngLogS : LatCSRng LogS` in `NeSyCat/Monad/LogIso.lean`, monotonicity transported along the order isomorphism `logEquiv`). `lem:prob-not-semiring` proved. `def:semiring-monad`/`thm:semiring-monad-laws`/`thm:semiring-monad-commutative` proved in `NeSyCat/Monad/SemiringMonad.lean` (`MS`, `ret`, `bind`, `bind_apply`, the three monad laws needing no `⊗`-commutativity, and `dstL`/`dstR`/`dst_comm_iff`/`dst_comm` showing the monad's own commutativity is exactly `S`'s). NEW `def:dist-monad` proved (`NeSyCat/Monad/Dist.lean`: `Dist X` the mass-one subtype of `MS ℝ≥0 X`, `ret_mass_one`/`bind_mass_one` the blueprint's Fubini closure computation, `Dist.pure`/`Dist.bind` the restricted monad structure — not Mathlib's `PMF`, noted). NEW `lem:log-iso` proved (`NeSyCat/Monad/LogIso.lean`: `LogS := WithBot ℝ`, `logEquiv : ℝ≥0 ≃ LogS` transporting a `CommSemiring` structure bridged to the explicit `lse`/`logMul` formulas, `logRingEquiv : ℝ≥0 ≃+* LogS`, and the monad isomorphism `logTensEquiv X : MS ℝ≥0 X ≃ MS LogS X` via `toLogTens_ret`/`toLogTens_bind`; `LogTens` abbrevs `MS LogS`). |
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

- See `FORMALIZE.md` for the resume protocol and work loop.
