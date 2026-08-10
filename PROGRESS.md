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
| Semiring-monad infrastructure (`M_S`, `D` as mass-one submonad)              | proved (C1-T3: chapter-1 cluster complete — every in-scope Definition/Lemma/Theorem of §"Semiring weight monads" is now `\leanok`, except `rem:semiring-monad-algebras`, which remains an unproved stretch target outside this cluster's scope (no Lean formalization of `MS S`'s algebras is claimed). `def:lattice-semiring`/`def:comm-lattice-semiring`/`def:bounded-lattice-semiring`/`def:bounded-comm-lattice-semiring` (`LatSRng`/`LatCSRng`/`BLatSRng`/`BLatCSRng` in `NeSyCat/CategoricalLayer/SemiringMonads/LatticeSemiring.lean`) now has all three running instances (`ex:lattice-semiring-rows`): Boolean (`BLatCSRng`, bounded), mass (`LatCSRng`, unbounded), and NEW log (`instLatCSRngLogS : LatCSRng LogS` in `NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean`, monotonicity transported along the order isomorphism `logEquiv`). `lem:prob-not-semiring` proved. `def:semiring-monad`/`thm:semiring-monad-laws`/`thm:semiring-monad-commutative` proved in `NeSyCat/CategoricalLayer/SemiringMonads/SemiringMonad.lean` (`MS`, `ret`, `bind`, `bind_apply`, the three monad laws needing no `⊗`-commutativity, and `dstL`/`dstR`/`dst_comm_iff`/`dst_comm` showing the monad's own commutativity is exactly `S`'s). NEW `def:dist-monad` proved (`NeSyCat/CategoricalLayer/SemiringMonads/Dist.lean`: `Dist X` the mass-one subtype of `MS ℝ≥0 X`, `ret_mass_one`/`bind_mass_one` the blueprint's Fubini closure computation, `Dist.pure`/`Dist.bind` the restricted monad structure — not Mathlib's `PMF`, noted). NEW `lem:log-iso` proved (`NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean`: `LogS := WithBot ℝ`, `logEquiv : ℝ≥0 ≃ LogS` transporting a `CommSemiring` structure bridged to the explicit `lse`/`logMul` formulas, `logRingEquiv : ℝ≥0 ≃+* LogS`, and the monad isomorphism `logTensEquiv X : MS ℝ≥0 X ≃ MS LogS X` via `toLogTens_ret`/`toLogTens_bind`; `LogTens` abbrevs `MS LogS`). |
| Truth-value structures (tower)                                              | proved (C2-T1: the `BLat2Mon` tower's foundational items are `\leanok` and sorry-free in `NeSyCat/LogicalLayer/TruthStructures/BLat2Mon.lean` + `NeSyCat/LogicalLayer/TruthStructures/BoolInstance.lean` — `def:blat2mon`/`def:blat2cmon` (`BLat2Mon`/`BLat2CMon`, explicit-field classes over `[Lattice α] [BoundedOrder α]`, not `Monoid` instances, since one carrier bears two independent monoids), `def:lin-blat2mon`/`def:lin-blat2cmon` (`LinBLat2Mon`/`LinBLat2CMon`, the 8 linear-distribution laws), `def:dm-structure` (`DMStructure` mixin), `def:zero-bot`/`def:one-top` (`ZeroBot`/`OneTop` `Prop`-mixins) plus `def:unit-bounds` (NEW `UnitBounds` trivial-alias class naming their conjunction), `lem:lin-monotone` (4 argument-versions: `otimes_le_otimes_left/right`, `oplus_le_oplus_left/right`), `lem:lin-lax-duals` (`otimes_inf_le`, `inf_otimes_le`, `le_oplus_sup`, `le_sup_oplus`), and `lem:bool-truth-structure` (full `BoolW` instance stack `instBLat2Mon → instLinBLat2CMon`/`instDMStructure`/`instZeroBot`/`instOneTop` plus the collapse lemmas `oplus_eq_sup`/`otimes_eq_inf` — of the 9 declarations in `lem:bool-truth-structure`'s `\lean` list, 4 (`instZeroBot`, `instOneTop`, `oplus_eq_sup`, `otimes_eq_inf`) close by a single `rfl` each, the other 5 (the `BLat2Mon`/`BLat2CMon`/`LinBLat2Mon`/`LinBLat2CMon`/`DMStructure` instances) by field-wise `decide` on the finite carrier). NEW `NeSyCat/Notation.lean`: scoped `⅋`/`&` infix notation (tested empirically against `∧`/`&&`/structure literals, no conflict) and the macros.sty twin-registry block; the pinned `¬` overload for `DMStructure.dneg` was tried and reverted — it reproducibly poisons elaboration (a same-looking-but-mismatched-type error on ordinary uses, isolated down to the bare overload with no nesting or interaction with `&`/`⅋`), so `DMStructure.dneg` stays the plain working name, flagged for LEAD/user adjudication. NEW (C2-T2, incl. the C2-T2b rider) `NeSyCat/LogicalLayer/TruthStructures/Chain.lean`: `thm:chain-lin` — part (i) lives in four RAW lemmas `chain_binop_sup_right/sup_left/inf_right/inf_left` over bare `[LinearOrder α]` with an explicit operation and a monotonicity hypothesis (no bounds, no monoid laws — the blueprint's "not necessarily bounded" clause is genuinely captured; they instantiate at `ℝ≥0`/`LogS`), with the four `BLat2Mon`-context lemmas `chain_otimes_sup`/`chain_sup_otimes`/`chain_oplus_inf`/`chain_inf_oplus` as one-line corollaries, and `LinBLat2Mon.ofChain` assembling the full structure from those plus `[UnitBounds α]` for the nullary laws — the instance-diamond wrinkle between `BLat2Mon`'s free `[Lattice α]` and `LinearOrder.toLattice` is benign since the two are `rfl`-defeq on every carrier used here, confirmed both abstractly and concretely at `unitInterval`), `lem:dualabsorb-decomposition` (`done_eq_top_iff_otimes_le_inf`/`done_eq_top_iff_sup_otimes_absorb` and their `dzero`/`oplus` duals — both routed through the unit equation as a pivot, since neither outer form implies the other pointwise without it), and `lem:mix` (`otimes_le_inf`, `sup_le_oplus`, `mix_chain`, and the named MIX corollary `otimes_le_oplus`). NEW (C2-T2) `NeSyCat/LogicalLayer/TruthStructures/UnitInterval.lean`: `lem:unit-interval-truth-structure`, the full instance stack on Mathlib's `unitInterval` (`instBLat2Mon` with `oplus p q := σ(σp * σq)` PINNED as the definition, `instBLat2CMon`, `instZeroBot`/`instOneTop`/`instUnitBounds`, `instLinBLat2Mon` built via `LinBLat2Mon.ofChain` — exercising `thm:chain-lin` exactly as the blueprint's own proof does — `instLinBLat2CMon`, `instDMStructure` with `dneg := unitInterval.symm`, and the readout lemma `coe_oplus` recovering the blueprint's `p+q-pq` display formula as a coercion fact, not the definition). NEW (C2-T5) `NeSyCat/LogicalLayer/TruthStructures/DeMorgan.lean`: the De Morgan calculus at class level (`[DMStructure α]`) — `lem:dm-lattice-laws` (`dneg_inf`/`dneg_sup`/`dneg_bot`/`dneg_top`, direct antisymmetry pairs from `dneg_antitone`/`dneg_dneg`, searched against building an explicit `OrderIso` and found no shorter — disclosed route choice), `lem:dm-dual-law` (`dneg_oplus`, the blueprint's own axiom-(iii)-at-the-swapped-args computation), `lem:dm-unit-swap` (`dneg_done`/`dneg_dzero`, via the private two-sided-unit-is-`dzero` helper `oplus_unit_eq_dzero`), `prop:dm-presentations` (`DMFullCalculus`/`dm_presentations`, encoded as `List.TFAE [Antitone n, lattice-DM-law, DMFullCalculus n]` via Mathlib's `tfae_have`/`tfae_finish` — the three-implication-cycle fallback was not needed — with the (a)⇒(c) leg built via `letI : DMStructure α := ⟨n, hinv, hanti, hand⟩` citing the class-level family lemmas verbatim, no proof duplication), and `lem:dm-maps-units` (`dneg_maps_units`, the raw existential form, witness `dneg q`, no Mathlib `IsUnit` since `BLat2Mon` isn't `Monoid`-bundled). NEW (C2-T5) `NeSyCat/LogicalLayer/TruthStructures/Impossibility.lean`: `thm:no-dm-mass`/`thm:no-dm-log` (`no_antitone_involution_nnreal`/`no_antitone_involution_logS`, stated as the PINNED core order fact — "no involutive antitone map on `ℝ≥0`/`LogS`" — rather than a `¬ DMStructure` statement, since `DMStructure` needs `[BoundedOrder α]` and neither carrier has one; the doc comments explain the subsumption of the blueprint's "hence no DM structure" clause) and `thm:square-not-lin` (the full witness cluster on raw ops over `ℝ≥0ᵒᵈ × ℝ≥0`, deliberately NOT a `BLat2Mon` instance — the carrier is unbounded, so the class does not even apply, part of the theorem's own content: `otimesSq`/`oplusSq`/`swapSq` the two-slot formulas mod `toDual`/`ofDual`, `swapSq_swapSq`/`swapSq_antitone`/`swapSq_dm` the DM-structure package, `otimesSq_comm`/`otimesSq_assoc`/`oplusSq_comm`/`oplusSq_assoc` plus the four unit equations the monoid package, `otimesSq_not_monotone_right` the core non-monotonicity witness `p=(1,0)`, `r=(5,0)`, `q=(0,10)` — the `⅋`-dual witness is disclosed as not separately formalized, optional per the ticket and forced anyway by `swapSq_dm`'s exchange mechanism — `monotone_of_distrib_sup` the raw distributivity-implies-monotonicity twin of `lem:lin-monotone`, `otimesSq_not_lin` the concluding refutation by contraposition, and `otimesSqENN_not_monotone_right` the ENNReal persistence witness at `ℝ≥0∞ᵒᵈ × ℝ≥0∞` with the identical numerals). This COMPLETES §"Truth-value structures"'s formalizable slate: every in-scope Definition/Lemma/Theorem/Proposition in the section is now `\leanok` (the four remaining `\label`s in the section are `\begin{remark}` environments, out of scope by the campaign's own convention). Blueprint marks landed with `scripts/blueprint.sh` at 189 kind-checked names, well inside the raised `maxRecDepth` headroom from C2-T4's fix.) |
| Truth spaces `M(Bool)`                                                      | proved (C2-T3: `NeSyCat/LogicalLayer/TruthSpaces/TruthSpace.lean` — `abbr:truth-space` (formerly labeled `def:truth-space`; `TruthSpace S := MS S BoolW`, the `Idmon` clause read directly off `BoolW`), `def:lifted-connective` PINNED via the `n`-ary strength `dstN` (`Fin.cons`/`Fin.tail` structural recursion) with `lift` DEFINED as `bind (dstN w) (Ret ∘ op)` — the blueprint's own iterated-bind definition recovered as arity lemmas `lift_zero`/`lift_one`/`lift_two` — and `lem:lifted-connective-strength` (formerly labeled `cor:lifted-connective-strength`, before the corollary kind was abolished) closing near-`rfl` (`lift_eq_dstN_bind`), `def:two-slot`/`def:dist-readout` (formerly one bundled `lem:truth-space-instances`, later split by the A1 bijection-law pass) via `twoSlot : MS S BoolW ≃ S × S` (`w ↦ (w 0, w 1)`, two-point `Finsupp` support) instantiated at `S := ℝ≥0`/`LogS` for the `Tmon`/`LTmon` rows and `distReadout : Dist BoolW ≃ unitInterval` (single-stage, routing through the mass-one constraint) for the `Dmon` row. Named lifted ops `otimesM`/`oplusM`/`negM` (binary/unary `lift` wrappers); `negM`'s underlying Boolean-negation operand is a `BoolW`-native `ite` (`negOp`, pointwise `= !·` via `negOp_eq_not`) rather than `Bool.not` directly — composing `!` through `lift₁`'s routing machinery reproducibly desynchronized `Decidable`-instance elaboration several layers down, an empirically-isolated and disclosed encoding choice, not a weakening.) |
| Lifted connectives (mass+log, derived `p+q−pq`)                             | proved (C2-T3: `NeSyCat/LogicalLayer/TruthSpaces/Lifted.lean` — the general two-slot routing engine (`lift₂_apply`/`twoSlot_lift₂`, `lift₁_apply`/`twoSlot_lift₁`) proved ONCE at general `[Semiring S]` via `bind_apply_boolW` + `Finsupp.single_apply`, then `\&`/`⅋`/`¬`/units coordinate formulas (`twoSlot_otimesM`/`twoSlot_oplusM`/`twoSlot_negM`/`twoSlot_ret_zero`/`twoSlot_ret_one`) ALSO proved once generically and merely cited at `S := ℝ≥0` (`lem:lifted-mass`) and `S := LogS` (`lem:lifted-log`, phrased via `lem:log-iso`'s `logS_add_eq_lse`/`logS_mul_eq_logMul` bridging lemmas into the blueprint's `lse`/`+` display) — no sum manipulation duplicated per carrier. `def:order-family` PINNED as `orderedTwoSlot : MS S BoolW ≃ Sᵒᵈ × S` (`twoSlot` composed with `OrderDual.toDual`, `OrderDual` supplying the whole order family for free) with meet/join/bounds transported through it as plain functions (`orderMeet`/`orderJoin`/`orderBot`/`orderTop`, never new `Lattice`/`BoundedOrder` instances on `MS S BoolW` — the instance-pollution hard rail); the blueprint's mass/log bounds clauses (`⊥=(∞,0)` etc., needing an adjoined `∞`) are honestly NOT formalized, `ℝ≥0`/`LogS` being unbounded above. `lem:lifted-prob-readout` stated as readout homomorphy: `Dist`-restricted `otimesD`/`oplusD`/`negD` (mass-one closure by the exact Fubini technique of `NeSyCat/CategoricalLayer/SemiringMonads/Dist.lean`'s `bind_mass_one`, reused not reproved) commute with `distReadout` onto T2's stipulated `unitInterval` family (`distReadout_otimesD`/`distReadout_oplusD`/`distReadout_negD`, the latter via `unitInterval.coe_oplus`) — the "derived, not stipulated" content in homomorphism form.) |
| Pointwise/linear-laws/copying-laws lemmas + three-layers theorem            | proved (C2-T4; the marks-blocking kind-check maxRecDepth ceiling was closed by the LEAD one-line generator fix and the held-back marks landed, both in commit 1ca5ee5 — all four items are `\leanok` statement+proof at HEAD, CORRESPONDENCE OK at 163 names: `NeSyCat/LogicalLayer/ThreeLayers/ThreeLayers.lean` — `lem:pointwise` via `instLatSRngProd`/`instLatCSRngProd`/`instBLatSRngProd`/`instBLatCSRngProd` (Prod, `Mathlib`'s `Prod.instSemiring`/`Prod.instLattice`/`Prod.instBoundedOrder` plus the four monotonicity fields componentwise) and `instLatSRngPi`/`instLatCSRngPi` (Pi, ARBITRARY index type `ι`, generalizing the blueprint's "(finite) power" clause a fortiori — the chapter-1 Lean-more-general precedent), plus the `S^𝔹 ≅ S × S` transport as equational lemmas on values (`twoSlot_add`, real content since `MS S BoolW` genuinely has `+`; `pointwiseMul`/`pointwiseOne`/`pointwiseMeet`/`pointwiseJoin`/`pointwiseBot`/`pointwiseTop` as plain (non-instance) `def`s pulling `S × S`'s own ops back through `twoSlot`, mirroring `orderMeet`/`orderJoin`'s pattern but un-dualized — Finsupp has no canonical pointwise-mul instance, so no instance is registered on `MS S BoolW`, the hard rail honored). `lem:linear-lift` over `[CommSemiring S]`: `otimesM_assoc`/`otimesM_comm`/`ret_one_otimesM`/`otimesM_ret_one`, `oplusM_assoc`/`oplusM_comm`/`ret_zero_oplusM`/`oplusM_ret_zero`, `negM_negM`/`negM_ret_zero`/`negM_oplusM`/`negM_otimesM` — all by `twoSlot` transport (`twoSlot.injective` + `lem:lifted-mass`'s routing formulas, the blueprint's own sanctioned proof route), assoc needing no commutativity (`ring`-provable from the semiring axioms alone), comm being exactly where `S`'s `mul_comm` enters (the concrete shadow of `thm:semiring-monad-commutative`'s `dstL = dstR ↔ S` commutative). `lem:copying-fails`: `fairCoin` (`distReadout.symm` of `½`), `otimesD_fairCoin_ne` (`¼ ≠ ½` via `distReadout_otimesD`), and `exists_otimes_ne_self` (the general `∃ p ∈ (0,1), p \& p ≠ p` witness, matching the blueprint's own `∃`-statement shape). `thm:three-layers` witness cluster: (i) `latCSRngBoolWSq`/`latCSRngNNRealSq`/`latCSRngLogSSq` (resolution witnesses at the three named squares, citing `prob_not_semiring` for the excluded row); (ii) needs no additional Lean (covered by `lem:linear-lift`/`lem:copying-fails`'s own marks); (iii) `order_iff_inf_eq_left` (`u ≤ v ↔ u ⊓ v = u`), the `𝔹`-coincidence citing `BoolW.oplus_eq_sup`/`BoolW.otimes_eq_inf` (NOT a claim that `MS BoolW BoolW`'s `otimesM`/`oplusM` pointwise-agree with `orderMeet`/`orderJoin` — checked by hand and found false, the disprove-guard catching a wrong reading before it was written), units-vs-bounds citing `unitInterval.instUnitBounds` (positive) and `not_isBot_orderedTwoSlot_ret_zero` (negative, the `⅋`-unit's `orderedTwoSlot` image at `S := ℝ≥0` is not a bottom). All sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`), `scripts/check.sh` GREEN. (Historical, RESOLVED at 1ca5ee5: the kind-check's flat do-block hit Lean's default `maxRecDepth` past ~123 names; the LEAD one-line generator fix — `set_option maxRecDepth 8000` — closed it, and this cluster's marks landed in the same commit.) ) |
| Categorical signatures and CD semantics (`Σ_α`, CD category, `𝓘_α`)        | stated (C3-B1: `def:categorical-signature`/`def:cd-category`/`def:categorical-interpretation` all `\leanok` in `NeSyCat/CategoricalLayer/Signatures/Signatures.lean` — `CatSignature` (three bare name fields `catSymbol`/`actorSymbol`/`monadSymbol`, `Mon := {Id, ○}`'s companion code `MonSym`, `@[blueprint_internal]`), `CDCategory` (route (a) of the LEAD encoding pin: `[Category C] [MonoidalCategory C] [SymmetricCategory C]` plus a chosen `ComonObj X`/`IsCommComonObj X` on every object, `copy_tensor`/`del_tensor` stating that the chosen comonoid on `X ⊠ Y` agrees with the one Mathlib's own `ComonObj (A ⊗ B)` instance induces from `X`'s and `Y`'s — no law beyond what the environment states), and `CatInterpretation` (`cd : CDCategory`, an actor category `A`, the actegory action `act : A → cd.C → cd.C` as a bare object map with NO functoriality/coherence fields — the environment states none, and `def:domain-interpretation` only ever applies it to objects — and `monad : CategoryTheory.Monad cd.C`; `CatInterpretation.interpretMon`, `@[blueprint_internal]`, is the companion definitional clause for "`Id` is always interpreted by the identity functor"). All three definitions only, no theorem proofs in this batch; the three running interpretations (Set/Tens/Identity, Set/Tens/Dist, Tens/Tens/LogVec) are prose examples, not envs, and are not formalized. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 environments unchanged, kind-check 56 -> 59 names, kernel-truth OK 59, census 317/56/261/0 -> 333/59/274/0 -- the 16 new scanned declarations are the 3 cited structures plus `MonSym`/`CatInterpretation.interpretMon` and 11 `deriving`-synthesized `DecidableEq`/`Repr` byproducts, all `@[blueprint_internal]`, matching the `BoolW` precedent for post-hoc-tagged derived instances -- 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) |
| Logical signatures (`Σ_β`, `𝓘_β`)                                          | stated (C3-B2: `def:logical-signature`/`def:logical-interpretation` both `\leanok` in `NeSyCat/LogicalLayer/LogicalSignatures/LogicalSignatures.lean` — `LogSignature` (`tauSymbol : String`, `Conn`/`connArity`/`connMonad`, `Quan`/`quanMonad`, reusing B1's `MonSym` for `Mon`) and `LogInterpretation` (`Ω : I.cd.C`, `connMor : ∀ c, (I(M)Ω)^⊠(arity c) ⟶ I(M)Ω`, `quanMor : ∀ Q n, (I(M)Ω)^⊠n ⟶ I(M)Ω`, both via the new shared `tensorList`/`interpretPow` companions, `@[blueprint_internal]`). **Comparison-symbol gap, disclosed not resolved**: the environment's prose names a "comparison symbol" `≺ : Mτⁿ → MBool` alongside the plain connective `* : Mτⁿ → Mτ`, but `def:logical-signature`'s own "consists of" sentence gives `Conn` only arity + monad symbol data — no field distinguishing which members are Bool-targeted — and `def:logical-interpretation` confirms the reading by interpreting every connective uniformly via `connMor`, with no separate Bool-valued clause anywhere. `LogSignature`/`LogInterpretation` are encoded with exactly the stated data; no `ConnTarget`/Bool-codomain field was added (a deviation from the night-campaign LEAD sketch's own suggestion, disclosed here — see `.foreman/scratch/C3-B2-report.md`). Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0.) |
| Domain layer (`Σ_γ`, writing convention, `𝓘_γ`)                            | stated (C3-B2: `def:domain-signature`/`def:domain-signature-notation`/`def:domain-interpretation` all `\leanok` in `NeSyCat/DomainLayer/DomainLayer.lean` — `DomSignature` (`Dom`/`Spc`/`Fun`/`Rel`/`Var`/`Par` Type-valued symbol sets, `fdom`/`fcod`/`fpar`/`rari`/`rpar`/`varOver`/`parOver` matching the environment's `dom`/`cod`/`par`/`ari`/`par`/`ovr`/`ovr` functions verbatim) and `DomInterpretation` (`domObj : Dom → I.cd.C`, `spcObj : Spc → I.A`, `funMor`/`relMor` valued in the actegory action `I.act`, via the new `interpretMS`/`interpretSpc` companions for `𝓘(M₁S₁,…,MₙSₙ)`/`𝓘(Θ₁,…,Θₖ)`; `DomInterpretation.interpretVar`/`interpretPar`, `@[blueprint_internal]`, are the companion definitional clauses for `𝓘(x) := id`/`𝓘(θ) := id`). **`def:domain-signature-notation` no-Lean exemption retired**: attempted the honest display-function counterpart the FORMALIZE.md pin itself invites, `DomSignature.TypedSymbol.display` (a `String`-valued display over a `fun_`/`rel`/`var`/`par` sum type, `ToString` instances on the abstract symbol Types plus a `monName : String` parameter standing in for the signature's own `○` name) — it lands cleanly (pure `String`/`List` code, no monoidal-category involvement), so the environment now carries `\lean`/`\leanok` marks; kind-check accordingly reads 64 names (not 63). The `FORMALIZE.md` pin text describing this as a standing no-Lean exemption is now stale and needs a follow-up documentation edit — out of this ticket's write set (`NeSyCat/**`, `content.tex` marks, `PROGRESS.md` only), flagged here for a follow-up ticket. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN for both clusters together (structure 88 environments unchanged, kind-check 59 -> 64 names, kernel-truth OK 64, census 333/59/274/0 -> 347/64/283/0 -- the 14 new scanned declarations are the 5 cited names plus 9 `@[blueprint_internal]` companions (`tensorList`, `interpretPow`, `displayMonDom`, `interpretMS`, `interpretSpc`, `DomInterpretation.interpretVar`, `DomInterpretation.interpretPar`, `DomSignature.TypedSymbol`, `DomSignature.TypedSymbol.ctorElimType`) -- 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) |
| Grammatical layer (`Σ_δ`, contexts, wire adapters, feed-forward)            | stated (C3-B3: `def:context`/`def:grammatical-signature`/`def:wire-adapters`/`def:feed-forward` all `\leanok` — `NeSyCat/GrammaticalLayer/Context.lean` (`Context sigG := {l : List sigG.Var // l.Nodup}`, the Elephant-style Nodup-list presentation); `NeSyCat/GrammaticalLayer/Grammar.lean` (`GramSignature sigG sigB : Type × Type := (Tm sigG sigB, Fm sigG sigB)`, the cited principal bundling the grammar's two syntactic categories as the pair of Types itself — `Tm`/`Fm` mutual inductives, raw untyped syntax per the CODES + INTERPRETATION pin, the six grammar rules as six constructors, substitution an explicit `Fm.subst` constructor; `Tm.inn`/`Fm.on` structural free-variable computation, `Tm.out := Tm.inn` disclosed — the document states no separate formula for a functional term's output beyond the one law `inn(ξ)=out(ξ)` for variable terms, and its own Kleisli-interpretation typing table reads a functional term's codomain off `Σγ.fcod f` directly; `Tm.WellFormed`/`Fm.WellFormed` extrinsic Prop predicates carrying all three pinned WF conditions — arity match, `x ∈ [φ]` for `subst`, and context distinctness/`xs.Nodup` for `quant` — decided separately from the untyped grammar); `NeSyCat/GrammaticalLayer/WireAdapters.lean` (`adapter` the cited principal for `def:wire-adapters`, the four-row marker table as one `match`-defined morphism via `adapterTargetMon`/`adapterCod` companions, `isBoundWire`/`bindSet` the bind-set `J` companion; `feedForward` the cited principal for `def:feed-forward`, the Do-form composite via the recursive wire-sequencing engine `StrongCatInterpretation.bindWires`, `Fmor ≫ adaptedTensor ≫ bindWires ≫ 𝓜g`, plus the point-free reformulation `feedForwardPointFree` and the proof obligation `feedForward_eq_pointFree` — Do-form and point-free agree by the monad's right-unit law collapsing `bind(g≫η)` back to `𝓜g`). **STRENGTH TRAP resolved**: `def:categorical-interpretation`'s `CatInterpretation.monad` bundles only "a monad" (no strength); the section opener's "Kleisli category of a STRONG monad" (content.tex l.654) is scene-setting prose, not itself an environment. `def:feed-forward` is the first environment in the document to write down a strength morphism (`σ^{(j)}`, in its point-free form) — `def:wire-adapters`' own per-wire table needs no strength (built from `CatInterpretation.monad`'s unit `η` alone). Strength lands as `StrongCatInterpretation`, a companion wrapper structure of `CatInterpretation` defined in `NeSyCat/GrammaticalLayer/WireAdapters.lean` (NOT a field added to `CatInterpretation` itself, `NeSyCat/CategoricalLayer/Signatures/Signatures.lean` being out of this ticket's write set — flagged as a natural fold candidate for a future ticket), with `leftStrength`/`dst` derived via the CD category's symmetry and the monad's multiplication, mirroring `SemiringMonad.lean`'s own concrete `dstL`/`dstR`/`dst` pattern abstractly. At the fully abstract CD-category level this layer is stated at, threading multiple tensor-factor wires through a Kleisli-style bind is only meaningful via strength — both the recursive Do-form (`bindWires`) and the point-free reformulation use it, disclosed as a genuine reading (not an artifact) of the STRENGTH TRAP: sequencing a Kleisli Do-block over several tensor factors abstractly requires strength regardless of which of the two formulas is "primary". Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 environments unchanged, kind-check 64 -> 68 names — the four new cited names, kernel-truth OK 68, census 347/64/283/0 -> 387/68/319/0 — the 40 new scanned declarations are the 4 cited names plus 36 `@[blueprint_internal]` companions/byproducts (`Tm`, `Fm`, `Tm.inn`, `Tm.out`, `Fm.on`, `Tm.WellFormed`, `Fm.WellFormed`, `adapterTargetMon`, `adapterCod`, `isBoundWire`, `bindSet`, `sourceTensor`, `targetTensor`, `adaptedTensorCod`, `adaptedTensor`, `StrongCatInterpretation`, `StrongCatInterpretation.leftStrength`, `StrongCatInterpretation.dst`, `StrongCatInterpretation.bind`, `StrongCatInterpretation.bindWires`, `StrongCatInterpretation.feedForwardPointFree`, `StrongCatInterpretation.feedForward_eq_pointFree`, plus the mutual-inductive/equation-lemma byproducts `Tm.brecOn.go`/`.eq`, `Tm.brecOn_1.go`/`.eq`, `Tm.brecOn_2.go`/`.eq`, `Fm.brecOn.go`/`.eq`, `Tm.ctorElimType`, `Fm.ctorElimType`, `Tm.inn.eq_def`, `Fm.on.eq_def`, `Tm.WellFormed.eq_def`, `Fm.WellFormed.eq_def`) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes). One deviation disclosed: `def:wire-adapters`/`def:feed-forward` are encoded generically over an explicit wire list `List (MonSym × MonSym × Dom)` and a bare object map `dObj : Dom → I.cd.C` (matching `interpretMS`'s own established genericity pattern in `DomainLayer.lean`), rather than literally through two `DomSignature.Fun`/`Rel` symbols `f`,`g` and their `fdom`/`fcod` lists — the per-wire/per-position mathematical content is identical either way, — genericity is the document's own intended level, though `def:kleisli-interpretation` (B4) does NOT literally call `feedForward`: it rebuilds its own `⨟`-composites (the term/relation-symbol clause, and — after C3-B4-FIX's BOTH-MARKERS repair — the `Id`-marked connective/quantifier clauses) directly from `StrongCatInterpretation.dst`/`strength`/`bind`, per-use, rather than by instantiating the generic `feedForward` machinery; see the C3-B4-FIX ledger entry below for the corrected description.) (C3-B4: `def:kleisli-interpretation` `\leanok` in `NeSyCat/GrammaticalLayer/Kleisli.lean` — the env's one cited principal is `Fm.sem` (`⟦φ⟧ : 𝓘([φ]) → 𝓜Ω`), `Tm.sem` (`⟦ξ⟧ : 𝓘(inn ξ) → 𝓜𝓘(kcod ξ)`) its `@[blueprint_internal]` mutually-recursive term-side half; both by structural recursion over all six grammar rules. Six cases: variable term `⟦x⟧ := η`; functional term `⟦f(ξ⃗)⟧ := ⟦ξ⃗⟧ ⨟_∘ 𝓘(f)` via `TmList.sem` (tensor-then-bind over the argument list, no `copy` needed since `Tm.inn`'s flatten already gives each occurrence its own slot) composed with the new `KleisliInterpretation.funMorK`; atomic formula `⟦R(ξ⃗)⟧` identically via `relMorK`; compound formula `⟦*(φ⃗)⟧ := ⟦φ⃗⟧ ⨟ 𝓘(*)` via `FmList.sem` (left uncollapsed, feeding `LogInterpretation.connMor` directly) composed with `connMor`; quantified formula `⟦Qx⃗(φ)⟧` via the product-state enumeration `listCard`/`listPt` (folded from `KleisliInterpretation.varCard`/`varPt` through `finProdFinEquiv`'s lexicographic decomposition), the `n`-ary self-copy `comulN` (from the CD category's chosen comonoid) of the remaining context, per-state insertion via the new context-merge primitive `ctxMerge` (structural on the context list, sliding each variable past the recursively-built rest via symmetry — reused for both the quantifier's multi-position and the substitution's single-position insertion), `tensorFin`'s indexed tensor of the resulting per-state semantics feeding `LogInterpretation.quanMor`; substituted formula `⟦φ[x:=ξ]⟧ := ⟦ξ⟧^{(p)} ⨟_∘ ⟦φ⟧` via `ctxAppendIso`/`SI.strength` threading the term's semantics into `x`'s slot, `ctxMerge`+`SI.bind` joining it into `body`'s own semantics. **Three disclosed deviations** (documented in-file, `Kleisli.lean`'s module doc and each companion's doc comment): (1) `def:domain-interpretation`'s `funMor`/`relMor` thread the actegory action `I.act(𝓘(Θ⃗))(-)` against a symbol's parameter space, but this grammar's six rules supply no syntax for passing parameters to a functional/atomic-formula node and this environment's own typing table elides `I.act` entirely (matching `def:wire-adapters`' own parameter-subscript elision) — `KleisliInterpretation` (new companion structure, `@[blueprint_internal]`, mirroring the STRENGTH TRAP precedent's `StrongCatInterpretation`) supplies `funMorK`/`relMorK` directly at the parameter-free instance the table needs, plus the quantifier clause's finite-enumeration data (`varCard`/`varPt`); (2) `Tm.KTyped`/`Fm.KTyped` (new extrinsic Prop side conditions, `@[blueprint_internal]`, threaded as explicit hypotheses to `Tm.sem`/`Fm.sem`, per the Prop-elimination doctrine) state the value-type match between a function/relation symbol's declared slots and its arguments' own `Tm.kcod` — a condition `Tm.WellFormed`/`Fm.WellFormed` (arity-only) do not state; the same predicate restricts a compound/quantified formula's connective/quantifier to its `○`-marked instance (`connMonad c = Id`/`quanMonad Q = Id` is not encoded — the case every one of the four running quantifier families and their connectives actually are); (3) the substituted-formula clause further restricts to a variable occurring exactly once in `body.on` (`Fm.KTyped`'s subst case) — the document's "single-position insertion" reading; the general "copy the computation's value into every occurrence of `x`" reading (the dice-or-die example) needs an `n`-ary copy of the term's own value this ticket does not build. **`lem:quantifier-nestable`: explicit remainder, not landed.** Two real attempts: (i) traced the document's own length-induction proof sketch against this file's concrete quantifier-clause encoding (`listCard`/`listPt`/`ctxMerge`/`comulN`/`tensorFin`) and confirmed the base case `l=1` is definitional (the simultaneous and iterated readings are literally the same expression, nothing to prove) but the inductive step needs `Nestable`/`Symmetric` formalized as Props on `LogInterpretation.quanMor` (block-grouping and permutation-invariance respectively) plus a substantial reindexing argument connecting `finProdFinEquiv`'s lexicographic product-state decomposition to "peel the first variable, recurse on the rest" — a second, independent piece of categorical infrastructure on the scale of the insertion machinery itself; (ii) confirmed no shortcut through the existing companions (`ctxMerge`'s generality doesn't reduce the reindexing burden, and `Tm`/`Fm`'s `KTyped`-hypothesis threading pattern doesn't shrink a length-induction over an arbitrary-order variable list). Per the hard sorry ban, no `theorem` statement for `lem:quantifier-nestable` was added to Lean or `\lean`/`\leanok`-marked in `content.tex` — landing an unproved statement is not an option; the lemma stays fully open, reported here as the ticket's disclosed remainder for a future ticket. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 environments unchanged, kind-check 68 -> 69 names — the one new cited name `Fm.sem`, kernel-truth OK 69, census 387/68/319/0 -> 406/69/337/0 — the 19 new scanned declarations are the 1 cited name plus 18 `@[blueprint_internal]` companions/byproducts (`Tm.kcod`, `ctxObj`, `KleisliInterpretation`, `ctxMerge`, `listCard`, `listPt`, `ctxAppendIso`, `kcodAppendIso`, `comulN`, `tensorFin`, `Tm.KTyped`, `TmList.sem`, `Tm.sem`, `Fm.KTyped`, `FmList.sem`, `Tm.KTyped.eq_def`, `Fm.KTyped.eq_def`, `Fm.KTyped.congr_simp`) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) |
| Grammatical layer — C3-B4-FIX (verification-driven repair of the Kleisli interpretation) | proved (blind verifier confirmed `def:kleisli-interpretation`'s overall encoding faithful except five gaps, all now repaired in `NeSyCat/GrammaticalLayer/{Grammar,Kleisli}.lean`: (1) CONTEXT FIDELITY — `Fm.on` now returns the genuinely deduplicated context (`firstDedup`, an order-preserving first-occurrence dedup, `Grammar.lean`, plus its `mem_firstDedup`/`firstDedup_nodup` companions) for the `.rel`/`.conn` clauses, matching `def:context`'s distinct-list reading; `Fm.sem`'s `.rel`/`.conn` clauses now prepend the new `ctxCopy` companion (`Kleisli.lean`: `ctxProjFilter`/`filter_eq_singleton_of_nodup_mem`/`projTo` build the single-variable projection, `ctxCopy` itself comultiplies the whole deduplicated context once per target-list position and projects), routing one copy of each shared variable to every raw occurrence — exactly the document's own `copy : I([φ⃗]) -> I([φ_1]) ⊠ ... ⊠ I([φ_n])`; (2) POSITIONAL SUBSTITUTION — `Fm.on`'s `.subst` clause now splices `t.inn` at `x`'s own position in `body.on` (via `List.takeWhile`/`List.dropWhile`, plus the new `list_split_pre_post` reassembly lemma needing only `x ∈ body.on`) rather than appending it at the list's end, matching the document's `[φ]_{[x]↦inn(ξ)} = [y_1,...,y_{p-1}] + inn(ξ) + [y_{p+1},...,y_m]` reading; `Fm.sem`'s `.subst` clause rebuilt to match, threading the term's (unitor-squeezed) value through `SI.leftStrength`/`SI.strength` into the reassembled position, joined via `SI.bind`; (3) BOTH MARKERS — `Fm.KTyped`'s `connMonad c = ○`/`quanMonad Q = ○` restrictions dropped; `Fm.sem`'s `.conn`/`.quant` clauses now dispatch on `sigB.connMonad c`/`sigB.quanMonad Q` directly, composing `FmList.sem`'s tensor of monadic factors straight into `connMor`/`quanMor` at the `○`-marked instance, or first collapsing it via the new `dstFoldN` (`n`-ary `StrongCatInterpretation.dst`-fold, `Kleisli.lean`) before applying the plain `Id`-marked morphism inside the monad — the `def:wire-adapters` `○`/`Id` bind-set row, rebuilt directly from `dst` rather than by invoking `feedForward`; (4) the substitution clause's `Fm.KTyped` conjunct is now literally the document's own `x ∈ body.on` (the exactly-once filter condition dropped — with `body.on` a genuine context whenever it is itself dedup'd/filtered, mere membership already forces uniqueness, and `Fm.sem`'s new positional construction only ever needs `x`'s first occurrence regardless); (5) `Kleisli.lean`'s module doc rewritten to record the file's own remaining deviations in place (no `feedForward` reuse — this file rebuilds `⨟`-composites directly from `SI.dst`/`strength`/`bind`; the `funMorK`/`relMorK` parameter-free bridging, no-coherence debt; the `varCard`/`varPt` finite-enumeration-completeness encoding), and the PROGRESS.md C3-B3 entry's false `feedForward`-reuse claim corrected in place. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 environments unchanged, kind-check 69 names unchanged — no cited name renamed, `content.tex` untouched, kernel-truth OK 69, census 406/69/337/0 -> 415/69/346/0 — the 9 new scanned declarations are all `@[blueprint_internal]` companions/byproducts (`firstDedup`, `mem_firstDedup`, `firstDedup_nodup`, `list_split_pre_post` in `Grammar.lean`; `ctxProjFilter`, `filter_eq_singleton_of_nodup_mem`, `projTo`, `ctxCopy`, `dstFoldN` in `Kleisli.lean`) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes, `content.tex` unchanged so nothing to rebuild against). |
| Batch monad + transformer + pointwise evaluation                           | partial (C3-B6(+B10): `def:batch-monad`/`thm:batch-transformer` `\leanok` in `NeSyCat/StatisticalLayer/Batching/{BatchMonad,BatchTransformer}.lean`; `thm:pointwise-eval` PART 1 ONLY `\leanok`, part 2 split out honestly. `Bmon B X := Fin B → X` (PLAIN FUNCTIONS, disclosed encoding pin: `Fin B`-indexed reader monad, hand-rolled `Bmon.ret`/`Bmon.bind` mirroring `SemiringMonad.lean`'s own `ret`/`bind` style — no `Monad`/`LawfulMonad` instance for `MS S` exists to route through Lean's `ReaderT (Fin B) Id` here). `thm:batch-transformer` switches encodings once an inner effect monad `M` enters: `BmonT B M X := ReaderT (Fin B) M X` (Lean/Mathlib's own `ReaderT`, disclosed), reusing Lean core's `LawfulMonad (ReaderT ρ m)` instance (`Init/Control/Lawful/Instances.lean`, given `[Monad M] [LawfulMonad M]`) as BACKGROUND machinery for "the composite is again a monad" clause, and proving the two canonical lifts by hand: `liftM` (the `MonadLift`-shaped embedding, definitionally Lean core's own `ReaderT` `MonadLift` instance) and `liftBmon` (a `MonadFunctor`-SHAPED lift along `M`'s unit, DISCLOSED as not literally an instance of Lean core's `MonadFunctor` class — that class's `monadMap` signature is a same-monad endo-map `{β} → m β → m β`, not a monad-changing map `Id ⟶ M`, so `liftBmon`/`liftBmon_ret`/`liftBmon_bind` are hand-proved, the bind clause reducing to `M`'s own left-unit law `pure_bind`). Bundled principal `batchTransformer` cites `liftM_ret`/`liftM_bind`/`liftBmon_ret`/`liftBmon_bind` (all `@[blueprint_internal]` companions), matching `semiring_monad_laws`'s own bundling precedent. `thm:pointwise-eval` SPLIT (bijection-law peer-claim split, two genuine claims the original env bundled): PART 1 keeps the `thm:pointwise-eval` label (`ev_i` is a monad morphism, unconditional — `NeSyCat.ev_isMonadMorphism`, `\leanok` both sides, two `rfl`s from `ReaderT`'s own diagonal-bind unfolding); PART 2 is the NEW env `thm:pointwise-eval-kleisli` (commutation with the Kleisli interpretation of `def:kleisli-interpretation` under the batch-naturality hypothesis) — carries NO `\lean`/`\leanok` mark on either statement or proof, left for a rider ticket: it needs a generic account of the Kleisli interpretation over an ARBITRARY strong monad `M` (to instantiate at both `M` and `Bmon M`), which `NeSyCat/GrammaticalLayer/Kleisli.lean` does not provide (built only for the library's own concrete interpretations) — the real dependency, not literally `lem:quantifier-nestable`/B4b (a different open item) though the spec named that as the blocking rider. B10 stray `lem:bind-matrix-mult` `\leanok`: retagged the PRE-EXISTING `NeSyCat.bind_apply` (`SemiringMonad.lean`, formerly an undisclosed `@[blueprint_internal]` companion of `def:semiring-monad`'s `bind`) as this lemma's own cited principal — its formula `bind f k y = f.sum fun x w => w * k x y` already IS the blueprint's matrix-multiplication identity, immediate unfolding, no new Lean needed. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 -> 89 environments — the one new `thm:pointwise-eval-kleisli` env, kind-check 69 -> 73 names — `NeSyCat.Bmon.bind`/`NeSyCat.batchTransformer`/`NeSyCat.ev_isMonadMorphism`/`NeSyCat.bind_apply`, kernel-truth OK 73, census 415/69/346/0 -> 428/73/355/0 — the 13 new scanned declarations are the 3 newly-cited names (`bind_apply` was already scanned, now flips internal -> cited) plus 10 `@[blueprint_internal]` companions/byproducts (`Bmon`, `Bmon.ret`, `BmonT`, `liftM`, `liftBmon`, `liftM_ret`, `liftM_bind`, `liftBmon_ret`, `liftBmon_bind`, `ev`) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) |
| dec/enc/Z suite + tilt lemma + mass preservation + pull-out theorem + normalizer corollaries | partial (C3-B7: `def:dec-enc-mass`/`lem:pure-maps`/`lem:tensor`/`lem:units`/`lem:strengths` all `\leanok` in `NeSyCat/StatisticalLayer/BridgesNormalization/DecEncMass.lean`. Throughout, a `Tmon X`-value is realized as `LogTens X = MS LogS X` (`lem:log-iso`), reusing `ofLogTens`/`toLogTens`/`dstL` directly rather than re-deriving exp/log analysis: `Z` is `(ofLogTens a).sum (fun _ w => w)` (`Dist`'s own mass-sum pattern); `dec` scales `ofLogTens a` by `(Z a)⁻¹` and lands in the full mass carrier `Tens X`, not the mass-one subtype (disclosed scope note: the all-`-∞`/zero-mass log-vector has no mass-one softmax, `0/0=0` convention); `enc` is `toLogTens ∘ Subtype.val` on `Dist X`. `pure_maps`'s `\Tmon(h)`/`\Dmon(h)` are `Finsupp.mapDomain h` at the log/mass carriers respectively (the fiber-sum argument is `Finsupp.sum_mapDomain_index` against a hand-derived additivity of `logEquiv.symm`); `tensor`'s `⊗` is the PRE-EXISTING `NeSyCat.dstL` (`SemiringMonad.lean`) specialized to `S = LogS`, whose `dstL_apply` together with `logS_mul_eq_logMul`/`logMul_coe_coe` already gives the `a_x+b_y` pairing formula for free — new companion lemmas `ofLogTens_dstL`/`toLogTens_dstL`/`dstL_sum_mul`/`ret_sum_one`/`bind_sum_eq` supply the mass-multiplicativity and decode-commutation. `strengths` generalizes the blueprint's `m`-ary, slot-`j` insertion to a three-factor reduction `strength bkg a aft := (Ret(bkg) ⊗ a) ⊗ Ret(aft)` (`bkg : B`, `aft : A` standing for the pure coordinates before/after the effectful slot; every concrete `m,j` instantiates `B`/`A` as products of the omitted coordinates) — the blueprint's own statement was tightened to this proven form per the absolutely-lean work-loop step. Zero `sorry`; axiom-audited (`propext`/`Classical.choice`/`Quot.sound` only) on all four theorems. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 89 environments unchanged — no new envs, only marks — kind-check 73 -> 78, the five newly-cited names, census 452 scanned/78 cited/374 internal/0 unclassified, registry sync 9, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes). C3-B8: `lem:tilt`/`def:mass-preserving`/`lem:mass-preserving-closure`/`thm:pullout` all `\leanok` in NEW `NeSyCat/StatisticalLayer/BridgesNormalization/Tilt.lean`. `tilt` is introduced inline inside `lem:tilt`'s own displayed equation (no separate `definition` env, matching the document), realized as the companion cluster `reweight`/`tiltMass`/`tilt` (`@[blueprint_internal]`); the cited principal `tilt_bind` carries the blueprint's own positivity hypothesis in its signature for exact statement fidelity, but is proved by an UNCONDITIONAL internal lemma `tilt_bind'` that needs no such hypothesis — the ambient `0⁻¹ = 0` convention `dec`/`tilt` already share makes a zero-mass continuation `k(x)` contribute exactly `0` on both sides of the identity, verified both abstractly (a `by_cases Z(k(x))` split collapses cleanly either way) and against a concrete non-mass-preserving `k` by hand before writing; the hypothesis is disclosed as unused, not silently dropped from the statement. `MassPreserving k := ∃ c, ∀ x, Z(k x) = c` (`def:mass-preserving`). `mass_preserving_closure` bundles the six clauses (pure maps via `Z_ret`, units, strengths via `strengths`' own mass clause, Kleisli composition via new `Z_bind_of_forall_const`, `⊗` via `Z_dstL`, and precomposition with a pure reindexing arrow) into one `∧`-conjunction theorem, the bijection law's single cited name. `thm:pullout`'s point-free chain `Φ = L ⨟ B_1 ⨟ ⋯ ⨟ B_r` is realized as a NEW inductive family `PulloutChain` (fixed at `Type`, not `Type*`, after a universe-polymorphism failure with per-constructor `Type*` binders — disclosed, harmless here since every concrete instantiation is an ordinary `Type 0` type): `base` (the leaf tensor `L`), `pureMap` (`\Tmon(h)`, `Finsupp.mapDomain`), `unitIns`/`strengthStep` (a unit/general-leaf tensor insertion via `dstL`, both realizing `lem:tensor` directly — `unitIns` is exactly the special case `strengthStep` at a `\Ret_\Tmon` leaf, disclosed as a deliberate simplification of `lem:strengths`' own 3-part slot-insertion formula, itself built from the same `dstL` two-factor pairing), and `bindStep`; `toTmon`/`toDmon`/`AllMassPreserving` read the chain in `Tmon`/`Dmon` and collect the per-bind mass-preservation hypothesis, and `pullout` proves `dec ∘ toTmon = toDmon` by structural induction on the chain (the blueprint's own "induction on `r`"), the bind case via a new internal corollary `dec_bind_of_massPreserving` built from `tilt_bind'` plus a `tilt`-at-constant-weight-is-identity lemma (`tilt_const_dec`). Two attempts were not needed: the capstone landed on the first full pass once `tilt_bind'`'s unconditional route was found. DISCLOSED judgment call: `thm:pullout`'s own statement and proof also carry a second clause ("if some `k_i` is not mass preserving, the two sides differ in general, and Lemma tilt gives the exact discrepancy") that this ticket's Lean proof does not independently establish (no formalized "tilt-failure example" witness exists yet, that illustrative example living in the not-yet-formalized §Examples); both are marked `\leanok` on the reading that this clause is citation-backed by the already-`\leanok` `lem:tilt` (which literally computes the general, non-identity `tilt` formula this clause refers to) rather than an independent unproven existential claim — flagged here for LEAD/verifier adjudication rather than silently assumed. `thm:chain-bound` (OPEN, "How wrong can it get") untouched, per the open-theorem convention. Two micro-riders landed in the same section: "Every other coordinate of `Tmon X`" -> "Every other value of `Tmon X`" (`def:dec-enc-mass`'s scope disclosure), and the "`0/0=0`" phrase corrected to name the actual Lean convention ("the inverse of `0` is `0`, so `dec` is there the zero function"). Zero `sorry`; axiom-audited (`propext`/`Classical.choice`/`Quot.sound` only) on `tilt_bind`/`mass_preserving_closure`/`pullout`. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 89 environments unchanged — no new envs, only marks — kind-check 78 -> 82, the four newly-cited names, census 479 scanned/82 cited/397 internal/0 unclassified — the 27 new scanned declarations are the 4 cited names plus 23 `@[blueprint_internal]` companions/byproducts, including the `PulloutChain.ctorElimType`/`brecOn.go`/`brecOn.eq` compiler byproducts post-hoc tagged via `attribute [blueprint_internal] ...`, matching the `Tm`/`Fm` precedent in `Grammar.lean` — registry sync 9, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes). def:normalizer/lem:normalizer-props/lem:normalized-heads (B9) remain not-started.) |
| Examples (failure numbers, MNIST commute)                                  | not-started |

OPEN: chain version of the tilt bound.

Fine-grained per-item status (labels, `\lean`/`\leanok` marks) lives in
`blueprint/src/content.tex`, not in this table.

## Notes

- **C2-E10 (sequential composition decree, USER DECREE 2026-08-09):**
  every `\circ` composite in `blueprint/src/content.tex` becomes
  `f \seq g` ("first `f`, then `g`"), order flipped at every site,
  worked site by site (never a regex replace): 33 lines carrying
  `\circ` at spec time (40 raw tokens; several lines chain 2-3
  composites, e.g. `thm:pullout`'s point-free chain and the naturality
  square at `lem:pure-maps`), all 33 flipped, meaning independently
  re-derivable at each site from argument types (a naturality square,
  the `dec`/`enc` unit laws, the tilt/pull-out chain, the lifted-
  connective strength identity). Full before/after per-site list in
  `.foreman/scratch/C2-E10-content-diff.txt`. The Introduction's
  conventions sentence rewritten: "We compose maps sequentially:
  `$f \seq g$` means first `$f$`, then `$g$`. We never write `$\circ$`."
  Scope guard held throughout: function application (`f(x)`,
  `\Ret(m(b))`) never touched, only sites already spelling `\circ`.
  Zero non-composition `\circ` found in `content.tex` (no exemption
  needed there); `NeSyCat.Logics/new.tex`'s appendix DOES have one —
  Uustalu's own `-^\circ` notation, quoted verbatim describing his
  paper's own triple, disclosed and exempted by a `%` comment at the
  site rather than converted (converting it would misattribute our
  operator to his paper). Macro plumbing (item 3): already
  single-sourced — `blueprint/src/macros/common.tex` `\input`s
  `NeSyCat.Logics/macros.sty` wholesale (pre-existing infrastructure,
  no local copy), which already carries `\seq`/`\fatsemi`; verified
  the glyph renders on both paths — print (xelatex, `\XeTeXversion`
  defined) loads real `stmaryrd`, giving a genuine `\fatsemi` glyph;
  web (plasTeX, no `\XeTeXversion`) falls through to macros.sty's own
  `\providecommand{\fatsemi}{;}` MathJax-safe fallback — both builds
  rebuilt clean, 23-page PDF unchanged in page count.
  `NeSyCat.Logics/new.tex` sweep (item 4, EDIT ONLY, never
  committed/staged there — confirmed clean `git status`, nothing
  staged): 18 lines carrying `\circ`, 17 flipped (its appendix
  "Monads and their Commutators" and the two grammar-in-context
  tables; the main body already used `\seq` throughout, pre-existing),
  1 exempted (Uustalu citation, above). DISCLOSED: `new.tex` and
  `nesy2026-paper.tex` already carried substantial (1000+-line)
  uncommitted local modifications, unrelated to this ticket
  (`\otimes`->`\boxtimes`, new tikz diagrams, a new `note` env, etc.),
  present before this ticket started; left untouched, layered my flips
  on top. `nesy2026-paper.tex`: 11 `\circ` sites found, explicitly OUT
  of scope per the ticket (not zero-risk to touch blind) — counted,
  reported, left alone. Enforcement (item 5): `lint-blueprint.py`
  (both copies, byte-identical) gained a `circ_scan`/`CIRC_RE`
  advisory on every `\circ` in `content.tex`, exempting only the
  Introduction's own naming sentence (matched by its fixed preceding
  phrase, not by location) — RED-tested through the hook entry point
  (both copies fire identically on an injected `$g \circ f$`), GREEN
  on the final document. FORMALIZE.md's notation-law patch is
  PREPARED, not applied, at
  `.foreman/scratch/C2-E10-FORMALIZE-patch.md` (batch-apply-at-morning-
  close convention, per the user decision after E8 — not a permission-
  system block this time, since the guard-scope protected set no
  longer lists `FORMALIZE.md`). Rider 5b: the KLay two-row note
  (`content.tex`, real->mass/log->log, `\citet{maeneKLay2025}`)
  extended with one sentence at code-verified strength: the released
  KLay implementation (`klay@dc32107`) also ships an MPE (max-times)
  module and a Gödel (max-min) module restricting to the Boolean row
  on `{0,1}`, verified directly against
  `~/Repos/NeSyCat/Competitors/klay`'s `src/klay/jax/semiring/godel.py`
  (`max_layer`/`min_layer`) and `__init__.py`'s `get_semiring` (`'mpe'`
  case, `max_layer`/`prod_layer`) before writing; paper fact stays
  cited to the paper, implementation fact cited to the pinned repo in
  a `%` comment, never rendered. Rider 5c: both undisclosed E8 edits
  (V-E8 findings 2a/2b) restored verbatim from 5903fd0 — (a) the two
  Generality-bullet sentences ("...library's own voice, at its natural
  generality." / "A narrower case from elsewhere appears in-item, as
  an instance or corollary."), consistent with FORMALIZE.md's own
  Faithfulness section (no conflict found, no `DONE_WITH_CONCERNS`
  needed); (b) the LL-dictionary table's top/bottom `\hline` pair and
  the three `none`/`none` unit cells (`content.tex` around the
  `def:dm-structure`/`lem:log-iso` rows). Census-exemption narrowing
  rider: already landed at C2-E8 (`CENSUS_EXEMPT_DECLS = {"
  blueprintInternalAttr"}`, sentinel 317/56/261/0) — verified intact,
  unchanged, no further narrowing needed or done. Lean side (item 6):
  untouched, confirmed — no `NeSyCat/**.lean` edits, registry sync
  unaffected (9 twins, unchanged). REGRESSION FOUND AND FIXED: the
  `\seq` glyph is visibly wider than `\circ` in a cramped subscript
  (`\tilt_{k \seq Z}`), pushing `lem:tilt`'s display equation from the
  established 1-hbox/1.2pt baseline to a 6.00839pt overfull hbox;
  split that one `\[...\]` into a two-line `gather*` (content
  unchanged, matching the same pattern C2-E3 already used twice
  elsewhere in this document) — rebuilt clean, 0 overfull hboxes (an
  improvement over the 1.2pt baseline). Gates: `scripts/check.sh`
  GREEN, sorry-report 0/0, `scripts/blueprint.sh` GREEN with every
  sentinel unchanged from baseline (structure 88 environments/56
  kind-checked names, kernel-truth OK 56, census 317/56/261/0,
  registry sync 9 twins, structure-mirror 15/0), both `lint-
  blueprint.py` copies silent on the final document, pdf+web rebuilt
  (23 pages, 0 overfull hboxes).

- **C2-E9 (dependency-graph kind-shape fix, 2026-08-09):** web-only,
  no `.tex` content or Lean touched. `plastexdepgraph`'s
  `Packages/depgraph.py` boxes only the `definition` env kind and
  ellipses everything else, including `class` and `abbreviation` —
  both definition-like (no proof obligations under the anatomy law) —
  which its own hardcoded legend mislabels "theorems and lemmas". New
  local plastex package `blueprint/src/nesycatshapes.py`, loaded via
  `\usepackage{nesycatshapes}` in `web.tex` AFTER
  `\usepackage[...]{blueprint}`, sets
  `document.userdata['dep_graph']['shapes'] = {'definition': 'box',
  'class': 'box', 'abbreviation': 'box'}` (`instance`/`lemma`/`theorem`
  fall through to the ellipse default — `instance` DELIBERATELY stays
  an ellipse: it discharges real proof obligations, so the theorem
  shape is truthful there) and registers a postParse-200 callback
  (after leanblueprint's own `make_legend`, postParse-150) rewriting
  the two shape-legend rows in place, leaving leanblueprint's
  appended color rows untouched. Verified in the rebuilt
  `dep_graph_document.html`: `def:bounded-comm-lattice-semiring` (a
  `class` node) and `abbr:log-tensor-monad`/`abbr:truth-space`
  (`abbreviation` nodes) are `shape=box`; `inst:logS-latcsrng`/
  `inst:massS-latcsrng`/`inst:boolw-latcsrng` (`instance` nodes) stay
  `shape=ellipse`; the legend now reads "Boxes — definitions, classes,
  abbreviations" / "Ellipses — lemmas, theorems, instances". Trace
  gap found and disclosed: contra the ticket's two-way local-vs-plugin
  dichotomy, a bare `.py` dropped into `blueprint/src/` does NOT
  resolve on its own (`plasTeX/Context.py`'s `loadPythonPackage`
  searches `config['general']['packages-dirs']` first, and that
  option's default is empty — confirmed empirically: the drop-in
  silently no-ops with "WARNING: No Python version of
  nesycatshapes.sty was found"). Used the one-line, still-local fix
  (`packages-dirs=.` added to `plastex.cfg`'s `[general]` section,
  commented in place) rather than the heavier plugins=-line/
  installable-plugin fallback. `print.tex` never `\usepackage`s
  `blueprint`, `dep_graph`, or `nesycatshapes` (print and web are
  fully separate LaTeX entry points), and `leanblueprint pdf` reported
  "Nothing to do for print.tex" (`print.pdf` unchanged) — the print
  build is structurally unaffected, not merely visually unchanged.
  Mirrored `nesycatshapes.py` byte-identical into a NEW
  `plugin/nesycat-lean4-harness/blueprint-scaffold/` (no such
  "blueprint scaffold twin" location existed before this ticket — the
  plugin was previously hooks/skills/agents only, deliberately
  host-agnostic; this directory holds portable, non-NeSyCat-specific
  companions a host repo's own `blueprint/src/` can copy in, with an
  install README). `scripts/blueprint.sh` GREEN, all sentinels
  unchanged from baseline: structure 88 environments/56 kind-checked
  names, census 317 scanned/56 cited/261 internal/0 unclassified,
  registry sync 9 twins, structure-mirror 15 sections/0 violations.
- **C2-E8 (Run 6, CONNECTIVE FLOW + VISIBLE ATTRIBUTION, USER DECREE
  2026-08-09):** two style laws, calibrated against the
  ⊗-commutativity passage (the E7 flat-prose master specimen), that
  revise C2-E5's book register and C2-E7's density law rather than
  reopen them. **Law 1 (connective flow)**: joined a run of 4+
  consecutive rendered-prose sentences opening with "The"/"This"/"It"
  at 4 locations (Introduction's five-layers paragraph, the semiring
  weight monad subsection opener, the Truth-value-structures section
  opener, the log-normalizer scope-disclosure paragraph) with genuine
  connectives (sequential "next"/"then" for the layer stack, "so" for
  a real cause-effect pair, "but" for a real contrast); applied the
  spec's LEAD-approved ⊗-commutativity specimen verbatim
  (LaTeX-fit only). **Law 2 (visible attribution)**: walked every
  `%`-comment citation block E5 created; restored book-style prose
  attribution + a new `\citep`/`\citet` bibliography (natbib
  author-year, matching the user's own papers) for genuinely external
  results — Girard's linear logic (4 sites: vocabulary, the four
  linear distributions, linear negation, the MIX rule) and the
  Coumans–Jacobs $S$-semimodules fact (the ticket's own canonical
  instance, landed via the Law-1 specimen); classified every other
  `%` block as apparatus (git refs/sha256/errata, explicitly still
  banned) or as document-history self-citation (blanket "this
  section is due to NeSy26/NeSyCat Theory v2" statements — NOT the
  same thing as crediting an external author, so left as comments,
  disclosed as the one genuinely judgment-call classification in the
  ticket report). **Two mid-run LEAD riders**, both verified against
  a vendored paper before writing anything (never invented): a
  one-sentence KLay connection note (after the three running-instance
  envs) crediting `\citet{maeneKLay2025}`'s real/log modules as this
  library's mass/log rows — checked directly against
  `references/papers/klay-arithmetic-circuits-2410.11415`'s source;
  the paper implements no Gödel/max-min module, so no Boolean-row
  correspondence is claimed (a drafted clause to that effect was
  declined, disclosed in the report); and a natbib citation-mechanism
  switch (bare `\cite` → `\citep`/`\citet`, author-year, camelCase
  authorTitleYear keys) with a discovered, disclosed toolchain split:
  natbib's `\citep`/`\citet` render correctly under print.tex's
  xelatex+latexmk (verified in the built PDF: "Maene et al. (2025)",
  "(Girard, 1987)", etc., no undefined-citation warnings), but render
  BLANK under web.tex's plasTeX (its `natbib.py` needs an
  already-resolved `.aux` from a real BibTeX/LaTeX pass, which this
  single-pass web build never produces — reproduced directly as an
  empty `<span class="cite"></span>` before the fix); web.tex's
  `\citep`/`\citet` fall back to plain-LaTeX `\cite` instead (plasTeX's
  un-overridden Base bibliography module renders `\bibitem`'s own
  optional "[Author(Year)]" label directly, no aux needed) — disclosed
  fallback, not a silent degrade, verified in the rebuilt web/index.html
  (zero blank citation spans). New `lint-blueprint.py` (both copies,
  byte-identical) advisory, `flow_scan`/`FLOW_OPENER_RE`: 4+ consecutive
  rendered-prose sentences opening with "The"/"This"/"It" in one
  paragraph — deliberately narrower than a first "The/This/That/It/We"
  draft, since the wider set false-positives against the very
  ⊗-commutativity specimen Law 1 calibrates against (disclosed at the
  regex's definition); also exempted `\bibitem[...]`'s own optional
  argument from the pre-existing bracket-citation advisory (it
  incidentally matches "[Girard"/"[Coumans" as literal text, but is
  required LaTeX syntax, not prose apparatus). Two riders: (a)
  `content.tex`'s `def:bounded-comm-lattice-semiring`-adjacent sentence
  ("The three running instances are of this last kind.", withheld by
  C2-H2 as mathematically false) replaced with "The three running
  instances are all commutative; only the Boolean row is also bounded."
  — matches the instance envs and the later corrected section, applied.
  (b) `blueprint/src/macros/common.tex`'s stale registry-comment
  inventory (flagged but out of scope for C2-H2) synced to
  `NeSyCat/Notation.lean`'s actual current surface: `\parr` marked
  RETIRED (no Lean twin, ever) rather than "planned"; `\AndC` marked
  RETIRED rather than describing a shipped glyph that was deleted at
  C2-E4b; `\dzero`/`\done` corrected from "scoped notation" claims to
  "live field, no notation glyph shipped"; `\negc`'s note extended to
  record that the primitive involution `DMStructure.dneg` is live now
  as a plain name (the `¬` overload was tried and reverted); a stale
  `Remark~rem:connective-conventions` reference (remarks are abolished)
  dropped. `scripts/blueprint.sh`'s CENSUS section's `BlueprintAttr`
  exemption narrowed from the WHOLE module to exactly the one
  declaration `registerTagAttribute` creates
  (`blueprintInternalAttr`) — verified via a direct scratch dump that
  the module's other constant, `initialize`'s auto-generated private
  `initFn` helper, is already caught by stage (i)'s
  `Lean.Name.isBlackListed`, needing no exemption of its own;
  RED-tested with a scratch decl added to (then reverted from) the
  real `NeSyCat/BlueprintAttr.lean` (net zero diff after revert):
  census correctly flagged it (318 scanned, 1 unclassified,
  `CORRESPONDENCE census violations: ... c2e8_red_test_scratch is
  neither cited ... nor tagged`); sentinel unchanged after the
  narrowing (317/56/261/0). **One concern, disclosed rather than
  guessed through**: the `FORMALIZE.md` law-text additions (both laws
  under "Blueprint structural laws", plus the "Local reference texts"
  Tooling note) could not be committed — `.claude/hooks/guard-scope.py`
  hard-denies Edit/Write on `FORMALIZE.md` while `.claude/grind-mode`
  is armed (confirmed armed throughout this ticket, a real permission-
  system state, not routed around); the exact patch text is prepared
  verbatim at `.foreman/scratch/C2-E8-FORMALIZE-patch.md` for
  application once grind mode clears. Gates: `scripts/check.sh` GREEN
  (no Lean files touched besides the reverted RED-test scratch decl),
  `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` BLUEPRINT:
  GREEN and numerically unchanged (88 environments, 56 kind-checked
  names, kernel-truth OK, census 317/56/261/0, registry sync OK at 9
  twins, structure-mirror 15/0), pdf+web rebuilt (23-page PDF, one
  residual overfull hbox at 1.2pt unchanged from baseline; the
  bibliography section legitimately added pages), both lint-blueprint
  copies silent on the final document.

- **C2-H2 (Run 6, HARDENING SLATE):** a reference-manual audit riders
  ticket, mostly mechanical/infrastructure, one genuine experiment, one
  disclosed scope conflict. (1) **Env-fold census replaces the regex
  census** (`scripts/blueprint.sh`): the CENSUS section no longer scans
  a fixed 12-file `CENSUS_FILES` list with a source-text regex; it now
  generates a Lean scratch file that folds `(← getEnv).constants`,
  filtered by MODULE prefix `NeSyCat.` (not a name guess), over a
  disclosed five-stage internal/auxiliary filter (`Lean.Name.
  isBlackListed`; an extra suffix list -- `.injEq`/`.sizeOf_spec`/
  `.sizeOf_eq`/`.brecOn`/`.binductionOn`/`.below`/`.ibelow`/`.ctorIdx`;
  constructors; structure/class field projections via
  `getProjectionFnInfo?`; auto-generated multi-`extends` parent
  combinators via `getStructureParentInfo`) — see `scripts/blueprint.sh`'s
  own top-of-file comment for the full disclosure. Scope is now the
  WHOLE `NeSyCat` namespace, not the old 12-file subset. **Sentinels
  changed**: 303 declarations / 48 cited / 255 internal / 0 unclassified
  (old, scoped) → 317 declarations / 56 cited / 261 internal / 0
  unclassified (new, whole-namespace); `structure`/`kind-check` stayed
  at 88 environments / 56 names (unchanged, as required — the census
  count moving is the scope-widening working as intended, not a
  regression). The fold surfaced 16 previously-invisible declarations
  in `NeSyCat/CategoricalLayer/SemiringMonads/LatticeSemiring.lean`
  (never in the old `CENSUS_FILES` scope): 9 exactly matching the
  ticket's predicted "regex-invisible specimens" (7 anonymous
  `BoolW` instances — `Lattice`/`BoundedOrder`/`Zero`/`One`/`Add`/`Mul`/
  `CommSemiring` — plus 2 `(priority := ...)` instances,
  `LatCSRng.toCommSemiring`/`BLatCSRng.toLatCSRng`) and 7 more from the
  scope widening itself (`BoolW` the carrier def, the `deriving`-
  synthesized `instDecidableEqBoolW`/`instFintypeBoolW`,
  `bot_eq_zero`/`top_eq_one`, and the redundant-monotonicity corollaries
  `add_le_add_right_of_left`/`mul_le_mul_right_of_left`); all 16 tagged
  `@[blueprint_internal]` (companions of the already-cited
  `instBLatCSRng`/class declarations, not new mathematics). (2) **The
  `@[blueprint_internal]` attribute replaces the `-- blueprint: internal
  (...)` comment tag**: a new root module `NeSyCat/BlueprintAttr.lean`
  (a `Lean.TagAttribute`, the same machinery Mathlib uses for e.g.
  `@[variable_alias]`) imported by every file that tags; all 255
  pre-existing comment tags migrated mechanically (reason text kept as
  an ordinary comment, attribute added to the declaration), plus the 16
  new item-1 finds. RED-tested (transcript in the ticket report): a
  scratch decl neither cited nor tagged turns the census gate RED with
  an exact violation line; reverted. (3) **Kernel-truth axiom audit**:
  a new `scripts/blueprint.sh` gate section, `kernel-truth: OK (56
  names)`, folding `Lean.collectAxioms` (the same machinery `#print
  axioms` calls) over every cited name and requiring the result be a
  subset of `{propext, Classical.choice, Quot.sound}` — catches
  TRANSITIVE `sorryAx` that `scripts/sorry-report.sh`'s source-text
  regex cannot see. RED-tested with a scratch `sorry`-backed decl
  (transcript in the report); reverted. (4) **The `⊕`/`⊗`
  `(priority := high)` retry FAILED AGAIN** (`NeSyCat/Notation.lean`):
  identical error to the original C2-E4a attempt, confirmed even at the
  maximum possible `Nat` priority value; a sanity probe confirms the
  notation mechanism itself is sound (a non-conflicting token elaborates
  immediately) — the failure is specific to contesting Lean core's
  global `Sum` notation for the `⊕` token from a `scoped` declaration.
  `⊗` alone stays clean (as before, `TensorProduct`'s own `⊗` is itself
  `scoped`). Reverted together, matching the C2-E4b precedent of not
  shipping an asymmetric glyph pair; `DMStructure.dneg` stays a plain
  name (unmet precondition — see `NeSyCat/Notation.lean`'s new "The
  `(priority := high)` retry was tried and reverted again" section for
  the full transcript). This closes the `⊕`/`⊗` notation question
  permanently. (5) **Commit-msg feedback-loop hardening**: the plugin
  twin's staged-Lean-file detection matched a bare `*.lean` pathspec
  with no root-scoping, counting this repo's own vendored
  `references/lean-docs/` tree (496 files) as "Lean source changed" and
  diluting the check; its structure-mirror auto-discovery had the same
  contamination via directory-count ambiguity. Fixed by auto-discovering
  the Lean source root (excluding VCS/build/tooling/`references`) and
  scoping both laws to it — for this repo the discovered root is
  exactly `NeSyCat`, matching the repo hook's own hardcoded scope
  (confirmed identical output on real staged content). The repo hook
  itself needed no root-scoping fix (already hardcoded to `NeSyCat/`),
  but its namespace-tail matching had an independent, smaller bug (only
  stripped the outermost `NeSyCat.` prefix, missing a doubly-nested cited
  name like `NeSyCat.BoolW.instBLatCSRng`) — ported the plugin twin's
  more robust last-dot-component matching to fix it; both hooks now
  produce byte-identical output. Also fixed, along the way: macOS bash
  3.2 mis-parses a quoted-delimiter heredoc nested inside `$( )` once its
  body contains an apostrophe followed later by a `)` (this file's own
  prose comments triggered it) — worked around via a temp-file
  indirection. (6) **common.tex sweep: NOT EXECUTED, scope conflict
  disclosed.** No `common.tex` exists in the sibling `NeSyCat.Logics`
  repo (the only file there with `% Lean:` tags is `macros.sty`, and it
  is current — `\dzero`/`\done` already cite `NeSyCat.BLat2Mon.dzero`/
  `.done`, `\AndC`'s tag is already deleted alongside the retired macro).
  The stale `% Lean:`-style "pointer comment" inventory the ticket
  describes verbatim (`\parr`, `\AndC` still listed live, `\dzero`/
  `\done` still claiming a shipped notation glyph) instead lives in
  THIS repo's own `blueprint/src/macros/common.tex` — outside this
  ticket's write set (only `blueprint/src/content.tex`'s two prose
  riders were authorized). Left untouched pending re-scoping; see the
  ticket report for the full evidence trail. (7) **Emit-lean for-loop**:
  the kind-check generator's flat N-statement `do` block (needing
  `set_option maxRecDepth 8000`, raised at C2-T4 past the ~123-name
  ceiling) is re-emitted as a `for` loop over an explicit `List Name`
  literal — O(1) elaboration depth regardless of name count — and the
  `maxRecDepth` option is dropped entirely. (8) **Prose riders**: the
  `lem:copying-fails`-adjacent flattening (content.tex, "the substituted
  formula copies the value... the repeated term runs the computation
  again") applied verbatim. The `def:bounded-comm-lattice-semiring`-
  adjacent rider ("The three running instances are of this last kind.")
  was NOT applied: the LEAD-supplied replacement ("...are commutative
  lattice-semirings that also carry bounds") contradicts the document's
  own later, already-corrected instance-rows section ("In this form only
  the Boolean row is bounded ... mass/log [are not]"), so both the
  original sentence and the proposed replacement misstate which running
  instances are bounded; left as-is per the ticket's own fit-check
  escape hatch. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh`
  0/0, `scripts/blueprint.sh` BLUEPRINT: GREEN (kernel-truth OK, census
  0 unclassified, registry sync OK at 9 twins — unchanged, since item 4
  reverted — structure-mirror 15/0, CORRESPONDENCE 88 environments/56
  names — unchanged), pdf+web rebuilt (1 residual overfull hbox at
  1.2pt, unchanged from baseline), lint hooks silent on both twins.

- **C2-E7 (Run 6, THE FLAT-PROSE TRANSFUSION, USER DECREE 2026-08-09):**
  a density pass over every rendered narrative paragraph and env-body
  prose connective tissue in `content.tex`, on top of C2-E5's register
  sweep. (1) **Seven LEAD-approved rewrites applied verbatim** at their
  pinned locations (house-style/LaTeX fitting only): the
  batch-naturality passage near `thm:pointwise-eval` (compression-
  stacking, memory item 9); the dm-completions outlook passage near
  `thm:no-dm-mass`/`thm:no-dm-log` (altitude/nominalization, item 10);
  the copying-fails significance-pronouncement passage after
  `lem:copying-fails` (item 11); the lattice-semiring
  naming/generality passage after `def:bounded-comm-lattice-semiring`
  (program-shaped prose, item 12); the instance-rows completion
  passage after the three running-instance boxes (essay voice, item
  13); the `⊗`-commutativity composite passage after
  `thm:semiring-monad-commutative` (all five classes at once, the
  master standard); and the Truth-value-structures section-opener
  clause (classes 10/13). (2) **Sweep, not pattern-hunt**: roughly 35
  further narrative paragraphs and dense proof/statement sentences
  rewritten to the same flat standard across the Introduction, both
  Categorical-layer subsections, all three Logical-layer subsections,
  the Domain/Grammatical layers, and both Statistical-layer
  subsections -- every fact preserved, no label/`\uses`/`\lean` moved.
  (3) **Enforcement**: both `lint-blueprint.py` copies gained two
  crude density advisories (`density_scan`, whole-document
  paragraph-granularity, math-mode and citation-paren excluded) -- a
  rendered-prose sentence over 55 words, and one with more than two
  real parenthetical groups; tuned against the swept document to zero
  false positives (documented tuning: MATH placeholders excluded from
  the word count; `(Class~\ref{...})`-shaped citation parens and bare
  `(i)`/`(ii)` markers excluded from the parenthetical count); RED-
  tested against a synthetic two-violation fixture end-to-end through
  the hook entry point, silent on the final `content.tex`.
  `FORMALIZE.md`'s book register law gained a new plain-language
  density law (one-claim-per-sentence clause, the five-class
  catalogue, the tuning disclosure). (4) **Gates**: `scripts/check.sh`
  GREEN (8684 jobs, no Lean files touched), `scripts/sorry-report.sh`
  0/0, `scripts/blueprint.sh` GREEN and numerically unchanged from
  baseline (88 environments, 56 kind-checked names, census 48
  cited/255 internal/0 unclassified, registry sync OK at 9 twins,
  structure-mirror 15 sections/0 violations), pdf+web rebuild clean,
  overfull count unchanged at 1 hbox, 1.2pt.

- **C2-E4b (Run 6, outward notation propagation, 2026-08-09):**
  the E4b half of the notation-propagation spec: macros.sty surgery,
  Lean glyph-notation removal, both papers, the hash pin, bold units,
  and one naked-claim lemma promotion.
  (1) **`NeSyCat.Logics/macros.sty`** (edited, not committed, per
  standing convention): the LL-dictionary `\parr` cell's macro is
  retired and replaced by a new `\llparr` (self-contained dual-render:
  reuses a real `\parr` glyph if a package already defines one, e.g.
  the papers' own `cmll`, else falls back to the bare Unicode `⅋`, safe
  for the web/MathJax build); `\parr`/`\AndC` themselves are DELETED
  (grepped first across the blueprint and both papers: zero remaining
  callers, confirming the C2-E3/A8 sweep's completeness). `\dzero`/
  `\done` keep their macro calls but now render BOLD (`\ifdefined\symbf`
  for `unicode-math` engines, `\mathbf` otherwise; verified both
  engines produce actual bold glyphs -- print.tex's pdf shows Unicode
  bold-digit codepoints `𝟎`/`𝟏`, the web build shows `\mathbf{0}`/
  `\mathbf{1}`). `% Lean:` twins updated to match: `\AndC`'s twin
  retired from `NeSyCat/Notation.lean`'s registry (both sides in the
  same step); `\dzero`/`\done`'s twins reworded to point at the live
  `BLat2Mon.dzero`/`done` fields (no glyph claim); `\llparr` carries no
  `% Lean:` tag (a foreign-notation display device, never gaining a
  Lean counterpart). (2) **`NeSyCat/Notation.lean`**: the scoped `⅋`/`&`
  infix notation (never shipped as anything but scoped, unused in any
  statement or proof per an exhaustive grep) is REMOVED entirely per
  user adjudication -- plain field names (`oplus`/`otimes`) are the
  Lean surface, matching the `dneg` precedent; a new module-doc section
  records the retirement rationale alongside the file's two existing
  "tried and reverted" transcripts. Doc-comment mentions across
  `BLat2Mon.lean`, `DeMorgan.lean`, `Impossibility.lean`,
  `BoolInstance.lean`, `TruthSpace.lean`, `Lifted.lean`, and
  `ThreeLayers.lean` that named the glyphs AS IF they were live Lean
  notation (`` `⅋`-unit ``, `` `w \& v` `` formulas, etc.) are swept to
  the plain names (`` `oplus`-unit ``, `` otimes w v ``); citations of
  Girard's own Linear Logic vocabulary (`` linear logic's `⅋` ``) are
  left untouched, since those describe LL's symbol, not ours. Stale
  dotted-unit glyph mentions (`0̇`/`1̇`) swept to plain prose ("bold
  `0`"/"bold `1`") to match the macros.sty re-render. (3) **Both
  papers** (`NeSyCat.Logics`, edited, not committed): `new.tex` already
  `\usepackage{../../macros}` (shared-macros adoption, pre-existing) --
  its "2MonBLat connectives" table (`tab:layer-connectives`, beyond the
  authoritative lines 1--396) swapped its LL-dictionary `\parr` cells to
  `\llparr`; separately, ALL `\otimes`/`\oplus` occurrences that denote
  the categorical/object-level tensor (the CD-category and actegory
  apparatus of the "Categorical Layer"/"Logical Layer" (which is really
  about categorical interpretation)/"Domain Layer"/"Grammatical Layer"
  sections, lines 100-471, matching `content.tex`'s own already-swapped
  "From here on, `\otimes` (rendered `\boxtimes`)" convention verbatim;
  and the "Categorical 2Mon-BLat" section's `def:cat-2mon-blat`/
  `def:cat-a2mon-blat` material and its own connectives table's
  "Categorical" column, lines 811-945) were swapped to `\boxtimes`/
  `\boxplus`, DISCLOSED judgment call: the paper's `def:2mon-blat`
  (value-level, sort `\tau`) and its one monotonicity citation stay
  `\otimes`/`\oplus`, matching the value-level/object-level split
  `content.tex` already made. One occurrence (a Zadeh fuzzy-powerset
  "sup-`\otimes`" composition mention, unrelated external-paper
  notation, not ours either layer) was left untouched, disclosed as
  out of scope rather than guessed at. `new.tex` recompiled clean via
  its own `pdflatex`+`latexmk` route (exit 0, 24 pages, zero errors,
  two pre-existing unrelated font-shape warnings). `nesy2026-paper.tex`
  needed NO content changes (grepped: zero `\parr`/`\AndC`/bare `⅋`
  connective misuse, zero `\dzero`/`\done` calls -- its own extensive
  `\otimes`/`\oplus` usage is entirely semiring-monad/lifted-connective
  value-level material, i.e. the same "pre-boundary" layer `content.tex`
  itself never boxes); its compile could NOT be verified in this
  environment (`latexmk` fails on a pre-existing, unrelated TeXLive
  `latexminted` 0.5.0 / Python 3.14 `argparse` incompatibility --
  confirmed pre-existing: the file already carried ~986 lines of
  unrelated uncommitted WIP diff before this ticket touched it, and
  this ticket made zero edits to it). (4) **Hash pin**: `new.tex`'s
  sha256 changed after the sweep (content unchanged, notation only);
  the `content.tex` `%`-comment pin (moved there by C2-E5) updated from
  prefix `9a84f22551f1e9ec` to `a2d490694ef768fb`. User should commit
  `new.tex` in `NeSyCat.Logics` (recommended again, per convention).
  (5) **§10 rider, naked-claim promotion**: the unproven observation
  sentence at content.tex's quantifier-nestability discussion (with its
  own confessing "recorded here as an observation, not re-argued"
  comment) is promoted to a new UNMARKED
  `Lemma~\ref{lem:quantifier-columns-nestable}` (no Lean yet -- its
  subject `\mathcal I(Q)_n` joins the logical-signatures formalization
  slate) with the LEAD-supplied statement and proof transcribed
  verbatim in house style (register-law dashes restructured to
  parentheses/commas); the old sentence is replaced by a `\ref` to the
  new lemma; `FORMALIZE.md`'s book register law gained one sentence:
  narrative mathematical claims must be env-backed or explicitly Open,
  never merely asserted. Gates: `scripts/check.sh` GREEN (full Lean
  rebuild, notation removal touched real files); `scripts/sorry-report.sh`
  0 sorries, 0 axioms; `scripts/blueprint.sh` GREEN -- structure 88
  environments (baseline 87 per C2-E5, +1: the new lemma+its proof are
  counted as ONE structural item by this gate's own convention, not +2
  as a naive per-env count would suggest; reported here as the actual
  observed change, not the ticket's own +2 expectation), kind-check 56
  names (unchanged -- the new lemma is unmarked), census 303/48/255/0
  unclassified (unchanged), registry sync OK at 9 twins (down from 10,
  `\AndC`'s retirement), structure-mirror 15/0 (unchanged), pdf+web
  rebuilds clean (1 overfull hbox, 1.2pt, unchanged from baseline).
  DISCLOSED: `blueprint/src/print.tex` shows as locally modified
  (title/author) but this ticket made no edits there and it is outside
  this ticket's write set -- pre-existing uncommitted WIP matching
  C2-E5's own disclosed "web/print title" follow-up flag, left
  untouched and unstaged.
- See `FORMALIZE.md` for the resume protocol and work loop.
- **C2-E5 (Run 6, THE BOOK REGISTER, USER DECREE 2026-08-09):** the
  rendered blueprint now reads like a book. (1) **Apparatus off the
  page**: every bracketed source citation (`[NeSy26, ...]`,
  `[Girard 1987]`, `Coumans--Jacobs, Lem. 23`), the "Sources and
  provenance" paragraph (git refs, sha256 pins), the categorical-layer
  supersession/pinned-text history, the erratum account, the
  "Blueprint-to-Lean correspondence" itemization's enforcement
  sentence, and the two line-pin notes on the quantifier-nestability
  lemma all moved verbatim into `%` comments at their original
  locations (honesty records preserved as comments; the erratum and
  the C2-E5 decree itself already have their PROGRESS/ledger homes).
  A short reader-facing "How to read the boxes" paragraph replaces the
  correspondence itemization in plain book language, with no tool
  names or script paths. `def:domain-signature-notation`'s own
  provenance tag moved to a comment after its `\end{definition}`
  (its structural exemption from Lean-mirror purity is untouched).
  (2) **Language sweep**: zero em/en dashes and zero bracket citations
  remain in rendered text (72 dash-run occurrences and 23 bracket
  citations, measured pre-edit by a comment-stripped regex scan, swept
  to commas, colons, periods, parentheses, or comments; hyphens in
  compound words and math minus signs untouched); `$\Sigma$--$\Pi$`
  became `$\Sigma$-$\Pi$`; three rows (six cells) of empty
  LL-dictionary units (`---`) became `none`; one British
  spelling (`marginalises`) normalized to the document's own voice
  (`marginalizes`); no filler phrases, aphorisms, or overclaims were
  found in the document (a targeted regex sweep for the reviewer's
  negative-example shapes was silent both before and after). (3)
  **Mathematics untouched**: every edit inside an env body was a
  dash-only fix (parentheses/commas replacing `---`/`--`) with no
  mathematical clause altered, except `def:domain-signature-notation`,
  whose env body dropped its trailing provenance clause (moved to a
  comment per (1)); env/kind counts, `\label`/`\uses`/`\lean`
  placement, and all 56 `\lean{}` names are unchanged. (4)
  **Enforcement**: both `lint-blueprint.py` copies gained a book
  register law pass (`REGISTER_CITATION_RE`/`REGISTER_DASH_RE`/
  `REGISTER_HISTORY_RE`/`REGISTER_FILLER_RE`, scanning the whole
  comment-stripped document, not just env bodies), RED-tested against
  four synthetic violations (citation, dash, history marker, filler
  phrase) and silent on the final `content.tex`; `FORMALIZE.md` gained
  the book register law under "Blueprint structural laws". Gates:
  `scripts/check.sh` GREEN (no Lean files touched), `scripts/sorry-report.sh`
  0/0, `scripts/blueprint.sh` GREEN and numerically unchanged from
  baseline (87 environments, 56 kind-checked names, census 48
  cited/255 internal/0 unclassified, registry sync OK at 10 twins),
  pdf+web rebuild clean, overfull count unchanged at 1 hbox, 1.2pt.
  DISCLOSED OUT-OF-SCOPE FINDING: the web/print page title
  (`\title{NeSyCat Semantics --- NeSy26 blueprint}` in
  `blueprint/src/web.tex` and `blueprint/src/print.tex`) still carries
  an em dash and a bare `NeSy26` mention; both files sit outside this
  ticket's write set (`content.tex`, `lint-blueprint.py` x2,
  `FORMALIZE.md`, `PROGRESS.md` only) and were left untouched — flagged
  here for a follow-up ticket with `web.tex`/`print.tex` in scope.
- **C2-E4c (Run 6, THE RENAME + the reuse-principle fold,
  2026-08-09):** (1) **The rename (USER DECREE)**: `BLat2Mon` fields
  `parr`/`andC` renamed `oplus`/`otimes` (`dzero`/`done`/`dneg`
  unchanged) across all 9 `NeSyCat/Truth/*.lean` files that touch the
  tower, a mechanical α-rename cascade (every derived name containing
  a `parr`/`andC`/`andM`/`andD`/`andSq`/`andUnitSq`/`parrM`/`parrD`/
  `parrSq`/`parrUnitSq` segment renamed to its `oplus`/`otimes` twin --
  e.g. `andC_le_andC_left` -> `otimes_le_otimes_left`,
  `chain_andC_sup` -> `chain_otimes_sup`, `dneg_parr` -> `dneg_oplus`,
  `andC_le_parr` -> `otimes_le_oplus`, `andM`/`parrM` -> `otimesM`/
  `oplusM` (`negM` stays), `andSq`/`parrSq` -> `otimesSq`/`oplusSq`,
  `andSqENN` -> `otimesSqENN`); build-verified (`scripts/check.sh`
  GREEN, zero warnings). `content.tex`'s 12 affected `\lean{}` marks
  updated to match (`otimes_le_otimes_left`, `otimes_inf_le`,
  `dneg_oplus`, `done_eq_top_iff_otimes_le_inf`, `BoolW.oplus_eq_sup`,
  `unitInterval.coe_oplus`, `otimesSq_not_lin`, `twoSlot_otimesM_mass`,
  `twoSlot_otimesM_log`, `distReadout_otimesD`, `otimesM_assoc`,
  `exists_otimes_ne_self`); census re-verified 0 unclassified.
  `NeSyCat/Notation.lean`'s two LIVE scoped-notation declarations
  re-pointed to `BLat2Mon.oplus`/`BLat2Mon.otimes`; its historical
  "tried and reverted" transcripts (the `⊕`/`⊗` swap episode) and the
  macros.sty twin-registry's `\AndC` line are deliberately left
  quoting the PRE-RENAME `BLat2Mon.parr`/`BLat2Mon.andC` spelling
  (marked retiring in E4b, when the sibling `NeSyCat.Logics/macros.sty`
  itself is updated to match) -- macros.sty is out of scope here, and
  the registry-sync gate needs the literal old string until then.
  (2) **The calibrated reuse/fold principle (USER DECREE)**, codified
  in `FORMALIZE.md`: a result folds into its consumer only when BOTH
  trivial (one-liner) AND single-purpose (zero other uses); a "nice
  result" keeps its lemma-hood regardless of use count. Applied:
  `NeSyCat.bind_ret` (zero uses, one-liner) folded into a new bundled
  `NeSyCat.semiring_monad_laws` (proof cites `ret_bind`/`bind_assoc`
  verbatim, proves the former right-unit law inline); `ret_bind`
  (5+ uses) and `bind_assoc` (4+ uses) keep independent lemma-hood.
  `content.tex`'s `lem:bind-right-unit` env AND its `proof` env
  deleted; `thm:semiring-monad-laws` gains
  `\lean{NeSyCat.semiring_monad_laws}` + `\leanok` on both statement
  and proof, its proof
  absorbing the deleted lemma's proof text as an inline step. Axiom
  audit on `semiring_monad_laws`: `{propext, Classical.choice,
  Quot.sound}`, matching `ret_bind`/`bind_assoc`. Census net-neutral
  (bind_ret's citation swapped for semiring_monad_laws's: still 303
  declarations, 48 cited, 255 internal, 0 unclassified).
  `scripts/blueprint.sh`'s census gained a mechanical ADVISORY line
  (comment-stripped grep-based use count of every cited theorem/lemma
  name across all of `NeSyCat/`, never a gate violation): first run
  post-fold found 14 zero-further-use candidates (`semiring_monad_laws`,
  `otimes_inf_le`, `dneg_maps_units`, `dm_presentations`,
  `mix_chain`, `oplus_eq_sup`, `no_antitone_involution_nnreal`/`_logS`,
  `otimesSq_not_lin`, `twoSlot_otimesM_log`, `twoSlot_pointwiseMul`,
  `otimesM_assoc`, `exists_otimes_ne_self`, `order_iff_inf_eq_left`)
  -- reported as a folding-candidates list for future LEAD/user
  adjudication, NOT folded by this ticket (out of the disclosed scope:
  "report, do not fold others without adjudication"). (3) **Residuals**:
  `NeSyCat/Notation.lean`'s stale `def:truth-space` doc reference fixed
  to `abbr:truth-space`; this file's own N1 finding (~line 131-133,
  "never counted, never flagged" corrected to "counted under the
  truncated name and miscredited as cited"); the "Truth spaces
  `M(Bool)`" ledger row's three dead labels (`def:truth-space`,
  `cor:lifted-connective-strength`, `lem:truth-space-instances`)
  rewritten to their current spellings (`abbr:truth-space`,
  `lem:lifted-connective-strength`, `def:two-slot`/`def:dist-readout`)
  with "formerly" framing. Gates: `scripts/check.sh` GREEN (zero
  warnings after two long-line wraps), `scripts/sorry-report.sh` 0/0,
  `scripts/blueprint.sh` GREEN (structure 87 envs, kind-check 56 names,
  census 0 unclassified, registry sync OK).
- **C2-E4a-fix (Run 6, closing the V-C2E4a blind-verification FAIL
  findings, 2026-08-09):** (F-1) **Census soundness**: `CENSUS_DECL_RE`
  in `scripts/blueprint.sh` widened from an ASCII-only identifier class
  to a Unicode-correct one (`[^\W\d][\w.']*`), so it no longer
  truncates at subscript characters and silently conflates e.g.
  `lift₂_apply` with the unrelated `lift`; the 8 declarations this
  exposed (`TruthSpace.lean`'s `lift₂`/`lift₁`/`lift₂_eq`/`lift₁_eq`,
  `Lifted.lean`'s `lift₂_apply`/`lift₁_apply`/`lift₂_mass_one`/
  `lift₁_mass_one`) tagged `-- blueprint: internal (A1 bijection-law
  companion of lift, content.tex def:lifted-connective)`. Census after
  the fix: 303 declarations, 48 cited, 255 internal (was 247), 0
  unclassified. The prior "affects only precision, not soundness"
  claim in the C2-E4a note below is corrected in place (it was a
  soundness gap, not a precision one); the "80 marked envs" figure
  there is corrected to 49. (F-2) **Stale labels**: `TruthSpace.lean`'s
  6 remaining `lem:truth-space-instances` doc-comment citations
  (lines ~15, 46, 337, 369, 391, 446 post-tag-shift) rewritten to the
  current `def:two-slot`/`def:dist-readout` labels, historical phrasing
  kept at the two genuinely-historical mentions (module doc header and
  section banner, both noting the label was split). (F-3) **Principal
  re-point (LEAD-adjudicated)**: `content.tex`'s `thm:chain-lin` now
  cites `NeSyCat.chain_binop_sup_right` (the raw, bare-`[LinearOrder
  α]` lemma matching the env's own "not necessarily bounded" text)
  instead of `chain_andC_sup`; `chain_andC_sup` (a `BLat2Mon`-context
  corollary) now carries an internal tag in its place, and the
  contradictory internal tag on `chain_binop_sup_right` (now cited) is
  removed. (F-4) **Kind-truth (LEAD-adjudicated)**: `TruthSpace`
  (`NeSyCat/Truth/TruthSpace.lean`, an `abbrev`) re-kinded from a
  `definition` to an `abbreviation` blueprint env, label renamed
  `def:truth-space` -> `abbr:truth-space` (prefix hygiene), all
  `\ref`/`\uses` call sites in `content.tex` and the doc-comment
  citations in `TruthSpace.lean` rewired; `LinBLat2Mon.ofChain` stays a
  `definition` env (reducibility is a technical detail, not a naming
  concern). `scripts/blueprint.sh`'s abbreviation-branch reducible-def
  rule accepts `TruthSpace` (Lean reports it `def`/`reducible`, as
  every `abbrev` does). All Lean-file edits in this fix are
  comment/tag-only, verified code-identical to HEAD under a
  comment-stripping diff. Gates: `scripts/check.sh` GREEN;
  `scripts/sorry-report.sh` 0 sorries, 0 axioms; `scripts/blueprint.sh`
  GREEN (structure/kind-check/census/registry all clean, pdf+web
  builds clean).
- **C2-E4a (full Lean-kind sync + bijection/completeness laws,
  2026-08-09; supersedes C2-E3/A1's proposition/corollary-only kind
  sync):** (1) **Full env inventory**: `example`/`conjecture` join
  `remark`/`proposition`/`corollary` as abolished; new `class`/
  `instance` envs introduced, one-for-one with Lean's own keywords;
  `ex:lattice-semiring-rows` split into three `instance` envs
  (`inst:boolw-latcsrng`/`inst:massS-latcsrng`/`inst:logS-latcsrng`);
  `cnj:chain-bound` promoted to `thm:chain-bound` with a proof body of
  exactly "Open." (never `\leanok`); the dice/tilt-failure/MNIST
  narrative examples dissolved into plain prose. Twelve former
  `definition` envs re-kinded to `class` (BLat2Mon family, LatSRng
  family, DMStructure, the unit-bound mixins). Independent per-kind
  counters (`common.tex`), verified restarting at 1 in BOTH engines
  (pdf via `pdftotext`, web via the rendered `_thmlabel` spans).
  (2) **The bijection law (addendum A1, mid-ticket)**: every marked env
  now carries exactly one `\lean{}` name; 28 formerly multi-name envs
  (out of an original 49 marked envs, 195 names) processed --
  `thm:semiring-monad-laws` split into three per-law lemmas
  (`lem:bind-left-unit`/`lem:bind-right-unit`/`lem:bind-assoc`) plus an
  unmarked summary theorem; `thm:chain-lin` split into part (i) (kept
  the label, a `theorem`) and part (ii) (new label
  `def:chain-lin-unitbounds`, re-kinded to `definition` since its
  principal `LinBLat2Mon.ofChain` is `def`-valued); `lem:log-iso`
  re-kinded `lemma` -> `definition` for the same def-valued-witness
  reason (principal `logTensEquiv`); `lem:truth-space-instances` split
  into `def:two-slot`/`def:dist-readout`; the remaining 24 envs trimmed
  to a single principal name each (companions demoted). Final mark
  count: 56 (down from 195, expected per the decree). ~135 demoted
  Lean declarations tagged `-- blueprint: internal (A1 bijection-law
  companion of ..., content.tex LABEL)` across 9 files.
  (3) **Completeness census (addendum A2)**: every top-level
  declaration in a fixed 12-file `CENSUS_FILES` list (the
  Truth-value-structures + semiring-monad chapters; NOT yet the whole
  library -- disclosed scope reduction, future work) is now either
  cited or tagged internal -- 303 declarations, 56 cited, 247 internal,
  0 unclassified. `pSum` (`NeSyCat/Monad/LatticeSemiring.lean`) was the
  one genuine audit find (real, uncited mathematics, not plumbing) and
  got its own `def:psum` Definition env. ~106 further pre-existing
  declarations (routing-engine unfolding lemmas, the `LogS` `WithBot`
  construction scaffold, truth tables, etc.) tagged
  `-- blueprint: internal (C2-E4a/A2 completeness census: ...)`.
  Limitation found and closed by C2-E4a-fix (V-C2E4a F-1): the
  census's name-matching regex truncated at Lean's unicode subscript
  characters (e.g. `lift₂`/`lift₁`, `lift₂_apply`/`lift₁_apply`,
  `lift₂_eq`/`lift₁_eq`, `lift₂_mass_one`/`lift₁_mass_one` all
  truncated to a bare `lift`), which was *not* merely a precision
  issue: it made those 8 declarations invisible to the scanner as their
  own identity (counted under the truncated name and miscredited as
  cited, never flagged as unclassified) because the truncated `lift`
  substring happened to match the genuinely-cited name `lift` --
  a soundness gap (an uncited item can go unnoticed exactly when its
  truncated form collides with a real cited name), not merely an
  imprecision. Fixed: `CENSUS_DECL_RE`'s identifier class widened to
  Unicode word characters (`scripts/blueprint.sh`); the 8 declarations,
  now correctly distinguished from `lift`, tagged
  `-- blueprint: internal (A1 bijection-law companion of lift,
  content.tex def:lifted-connective)`. Census after the fix: 303
  declarations, 48 cited, 255 internal, 0 unclassified. (4) **Lean
  notation swap REVERTED (empirical fallback,
  same shape as the standing `¬`-episode)**: the decreed scoped
  `" ⊕ " => BLat2Mon.parr`/`" ⊗ " => BLat2Mon.andC` was probed exactly
  per the pin's protocol. `⊗` alone is clean. `⊕` alone reproducibly
  poisons elaboration: Lean core's global (always-open, non-`scoped`)
  `Sum` notation wins the no-expected-type case (a bare
  `theorem foo ... : p ⊕ q = p ⊕ q := rfl`, the ordinary shape of
  essentially every existing lemma statement in this library) before
  our scoped alternative is even tried, producing a "expected Type,
  got α" elaboration failure with zero interaction from `⊗` or `Sum`
  usage anywhere else in the file. Per the fallback protocol: **no
  swap shipped**; the existing `⅋`/`&` scoped notation in
  `NeSyCat/Notation.lean` is untouched; a new "The `⊕`/`⊗` swap was
  tried and reverted" section (mirroring the `¬`-episode) documents the
  reproduction transcript. Flagged for LEAD/user adjudication.
  E4b's macros.sty-side work (`\llparr`, box tensor, deleting
  `\parr`/`\AndC`) is independent and unaffected.
  (5) **F1/F2/F3 remediations** (V-C2E3 findings) all applied: ~17
  stale Lean doc-comment label citations fixed (plus further ones this
  ticket's own re-kinding/splitting introduced, e.g. `lem:log-iso` ->
  `Definition~\ref`, `ex:lattice-semiring-rows` -> the three new
  `inst:*` labels, part (ii) -> `def:chain-lin-unitbounds`); F2's
  seven purity-polish moves (mechanism clauses, "one-sided suffices",
  the DM commutative parenthetical, no-dm-mass's "hence", lifted-mass's
  ∞-bounds sentence, batch-transformer's gloss, `cnj:chain-bound`'s
  meta-commentary) confirmed already resolved by the prior in-progress
  work this ticket completed; F3's "retired" wording confirmed already
  reworded. Gates: `scripts/blueprint.sh` GREEN (88 environments,
  56 kind-checked names, census 0 unclassified, registry sync OK, both
  pdf/web builds clean, independent per-kind numbering verified both
  engines); `scripts/check.sh` GREEN (0 warnings after wrapping ~210
  tag-comment lines that first overran the 100-char style limit);
  `scripts/sorry-report.sh` 0 sorries. See `FORMALIZE.md`'s "Blueprint
  structural laws" for the law text (final environment inventory, the
  open-theorem convention, the bijection law, the internal-tag
  convention, the three-shape witness doctrine).
- **C2-E3 (editorial constitution pass, 2026-08-09):** a full-document
  editorial sweep of `blueprint/src/content.tex`, zero Lean changes.
  (1) **Remarks abolished**: all 24 `\begin{remark}` environments
  dissolved into plain narrative prose at their locations (condensed,
  meaning preserved; the mass-units erratum and the log-`epsilon`-floor
  scope disclosure survive as prose, flagged `\textbf{...}`); the
  `remark` environment kind no longer appears anywhere in the document.
  (2) **Proposition/corollary abolished** (C2-E3/A1 addendum): full
  LaTeX<->Lean kind sync -- `prop:dm-presentations` ->
  `thm:dm-presentations`, `prop:batch-transformer` ->
  `thm:batch-transformer`, `prop:pointwise-eval` -> `thm:pointwise-eval`
  (all promoted to `theorem`, chapter-payoff statements);
  `cor:bind-matrix-mult` -> `lem:bind-matrix-mult`,
  `cor:lifted-connective-strength` -> `lem:lifted-connective-strength`,
  `cor:normalized-heads` -> `lem:normalized-heads` (all demoted to
  `lemma`, cited-as-infrastructure); every `\ref`/`\uses` rewired, zero
  stale labels. (3) **Total Lean-mirror purity**: every theorem-family/
  definition/abbreviation/`\lean`-marked-example/proof body now
  contains only its Lean counterpart's content -- provenance brackets
  (`[NeSy26, App.~A]` etc.), dictionary glosses, contrast asides, and
  forward pointers moved to plain prose immediately before/after,
  consolidated per-subsection where a run of items shared one citation.
  `def:domain-signature-notation` is the one pinned exemption (untouched).
  (4) **LL dictionary table**: `rem:ll-dictionary` replaced by a plain
  6-column tabular (ours/LL/name/our unit/LL unit/realized-as) in prose
  flow, per the notation-reversal-revised row list; the LL column's
  `parr` cell borrows the (pre-E4) `\parr` macro with an in-source E4
  TODO to swap to a dedicated `\llparr` once macros.sty adds one.
  (5) **Notation reversal (blueprint side, FINAL state after addenda
  A3/A8)**: every OUR-VOICE `\AndC`/`\parr` macro call in `content.tex`
  was swept in-source to `\otimes`/`\oplus` directly (not left to E4's
  macro re-render as originally staged -- A8 pulled the source sweep
  into this ticket since ⅋/&-style glyphs are banned in our own voice
  outright); the ONE surviving `\parr` is the linear-logic dictionary's
  own LL-column cell (line 1065), displaying linear logic's *foreign*
  glyph on purpose, with an in-source E4 TODO to swap it to a dedicated
  `\llparr` once macros.sty adds one -- `\AndC`/`\parr` themselves stay
  defined in macros.sty, untouched, used only by that one cell.
  `\dzero`/`\done` calls are untouched (E4 renders them bold, `𝟎`/`𝟏`,
  to distinguish a monoid unit from a plain carrier numeral -- prose
  states this positively, no dates/history). Prose lost every
  now-redundant "(read `$\otimes$`)"/"(our `$\otimes$`)" parenthetical
  that the swept commands made tautological. Categorical-layer object
  tensors (SS2.2, 3.4, 4, 5) swapped `\otimes`/`\otimes_{\mathcal C/A}`
  for `\boxtimes`/`\boxtimes_{\mathcal C/A}` (macros.sty box macros
  don't exist yet, so raw `\boxtimes` is used directly per the
  ticket's fallback protocol); SS6.2's `lem:tensor` `\otimes`
  deliberately left alone (value-level pairing, same family as our
  `\otimes`, not the categorical object tensor). (6) **Register normalization**: every
  `Chapter`/`chapter` occurrence (3 `\ref` sites plus 2 bare-word
  mentions) reworded to `Section`/`section`; the relocated
  "This chapter replaces..." framing paragraph now opens "This section
  replaces...". (7) **Instance-rows reframe**:
  `ex:lattice-semiring-rows`' framing sentence reworded to the
  completion framing (computational/finite-weight form; log's in-carrier
  `-infty` bound and zero; mass/log's `top` deferred to the completion
  instances) -- the underlying claim (Boolean bounded, mass/log not, in
  this form) is unchanged. (8) **Overfull print lines**: `print.tex`
  gained an `\emergencystretch`/`\tolerance` knob (print-only, web
  unaffected); 3 genuine layout fixes (the LL table shrunk to
  `\footnotesize` with tighter `\tabcolsep`; two overwide displays split
  via `gather*`/`multline*`, content unchanged) brought 11 baseline
  `Overfull \hbox` warnings down to 1 residual at 1.2pt (well under the
  2pt bar). (9) **Statement/proof anatomy** (addenda A5/A6, a NEW
  standing law): `lem:prob-not-semiring` and `lem:copying-fails` had
  their concrete witness numerals (the `p=q=r=1/2` computation; the
  fair-coin `p=1/2` witness) moved out of the statement env into the
  proof env, matching the Lean statement's `\exists`-shape versus the
  Lean proof's `refine`+`norm_num` shape; audited the rest of the
  document for the same pattern (zero further hits). The law is now
  codified in `FORMALIZE.md` and enforced by a new lint advisory (both
  hook copies, RED-tested against the old `prob_not_semiring` text as
  the specimen). Gates: `scripts/blueprint.sh` CORRESPONDENCE OK at 83
  environments (down from 107, exactly the 24 dissolved remarks) and
  195 kind-checked `\lean{}` names (unchanged from baseline); both
  `lint-blueprint.py` copies updated (remark/prop/cor advisories, the
  purity-marker advisory, and the anatomy advisory) and RED/GREEN-tested;
  `scripts/check.sh` and `scripts/sorry-report.sh` unaffected (0
  sorries, no `NeSyCat/**` changes). See `FORMALIZE.md`'s "Blueprint
  structural laws" for the law text (final environment inventory,
  remark abolition, total purity, the pinned exemption, statement/proof
  anatomy).
- **C2-E2 (seven-layer restructure, 2026-08-09):** `blueprint/src/content.tex`
  was reorganized to the user-adopted layer architecture: 1 Introduction,
  2 Categorical layer (2.1 Semiring weight monads, 2.2 Categorical
  signatures and CD semantics), 3 Logical layer (3.1 Truth-value
  structures, 3.2 Truth spaces and lifted connectives, 3.3 Three layers,
  3.4 Logical signatures), 4 Domain layer, 5 Grammatical layer,
  6 Statistical layer (6.1 Batching, 6.2 Bridges and normalization,
  6.3 Examples). An **Inferential layer** (proof theory <-> model
  theory) is **RESERVED** between the Grammatical layer (5) and the
  Statistical layer (6), marked by a LaTeX comment at that insertion
  point in `content.tex`; it has no content yet and is not one of the
  six numbered sections above. Add it as section 6 (renumbering
  Statistical to 7) once its first item exists. Pure reorganization: no
  Lean changes, no `\lean{}`/`\leanok` mark changes, item labels stable
  except `rem:domain-signature-notation` -> `def:domain-signature-notation`
  (promoted from remark to definition per the same ticket).
