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
| Truth-value structures (tower)                                              | partial (C2-T1: the `BLat2Mon` tower's foundational items are `\leanok` and sorry-free in `NeSyCat/Truth/BLat2Mon.lean` + `NeSyCat/Truth/BoolInstance.lean` — `def:blat2mon` (`BLat2Mon`/`BLat2CMon`, explicit-field classes over `[Lattice α] [BoundedOrder α]`, not `Monoid` instances, since one carrier bears two independent monoids), `def:lin-blat2mon` (`LinBLat2Mon`/`LinBLat2CMon`, the 8 linear-distribution laws), `def:dm-structure` (`DMStructure` mixin), `def:unit-bounds` (`ZeroBot`/`OneTop` `Prop`-mixins, plus NEW `UnitBounds` trivial-alias class naming their conjunction), `lem:lin-monotone` (4 argument-versions: `andC_le_andC_left/right`, `parr_le_parr_left/right`), `lem:lin-lax-duals` (`andC_inf_le`, `inf_andC_le`, `le_parr_sup`, `le_sup_parr`), and `lem:bool-truth-structure` (full `BoolW` instance stack `instBLat2Mon → instLinBLat2CMon`/`instDMStructure`/`instZeroBot`/`instOneTop` plus the collapse lemmas `parr_eq_sup`/`andC_eq_inf` — of the 9 declarations in `lem:bool-truth-structure`'s `\lean` list, 4 (`instZeroBot`, `instOneTop`, `parr_eq_sup`, `andC_eq_inf`) close by a single `rfl` each, the other 5 (the `BLat2Mon`/`BLat2CMon`/`LinBLat2Mon`/`LinBLat2CMon`/`DMStructure` instances) by field-wise `decide` on the finite carrier). NEW `NeSyCat/Notation.lean`: scoped `⅋`/`&` infix notation (tested empirically against `∧`/`&&`/structure literals, no conflict) and the macros.sty twin-registry block; the pinned `¬` overload for `DMStructure.dneg` was tried and reverted — it reproducibly poisons elaboration (a same-looking-but-mismatched-type error on ordinary uses, isolated down to the bare overload with no nesting or interaction with `&`/`⅋`), so `DMStructure.dneg` stays the plain working name, flagged for LEAD/user adjudication. NEW (C2-T2) `NeSyCat/Truth/Chain.lean`: `thm:chain-lin` (four binary chain lemmas `chain_andC_sup`/`chain_sup_andC`/`chain_parr_inf`/`chain_inf_parr` taking one-sided monotonicity as plain hypotheses on a `[LinearOrder α] [BoundedOrder α] [BLat2Mon α]`, and `LinBLat2Mon.ofChain` assembling the full structure from those plus `[UnitBounds α]` for the nullary laws — the instance-diamond wrinkle between `BLat2Mon`'s free `[Lattice α]` and `LinearOrder.toLattice` is benign since the two are `rfl`-defeq on every carrier used here, confirmed both abstractly and concretely at `unitInterval`), `lem:dualabsorb-decomposition` (`done_eq_top_iff_andC_le_inf`/`done_eq_top_iff_sup_andC_absorb` and their `dzero`/`parr` duals — both routed through the unit equation as a pivot, since neither outer form implies the other pointwise without it), and `lem:mix` (`andC_le_inf`, `sup_le_parr`, `mix_chain`, and the named MIX corollary `andC_le_parr`). NEW (C2-T2) `NeSyCat/Truth/UnitInterval.lean`: `lem:unit-interval-truth-structure`, the full instance stack on Mathlib's `unitInterval` (`instBLat2Mon` with `parr p q := σ(σp * σq)` PINNED as the definition, `instBLat2CMon`, `instZeroBot`/`instOneTop`/`instUnitBounds`, `instLinBLat2Mon` built via `LinBLat2Mon.ofChain` — exercising `thm:chain-lin` exactly as the blueprint's own proof does — `instLinBLat2CMon`, `instDMStructure` with `dneg := unitInterval.symm`, and the readout lemma `coe_parr` recovering the blueprint's `p+q-pq` display formula as a coercion fact, not the definition). NOT in scope for C2-T1/C2-T2 and still unformalized: `lem:dm-lattice-laws`, `lem:dm-dual-law`, `lem:dm-unit-swap`, `prop:dm-presentations`, `lem:dm-maps-units`, `thm:no-dm-mass`, `thm:no-dm-log`, `thm:square-not-lin` (per the campaign plan, routed to T5).) |
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
