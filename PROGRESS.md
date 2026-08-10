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
| Support readout, gradient semiring, and embedding-space reasoning (C3-TL-A) | proved (Phase A of the tensor-logic cite-then-prove campaign, `.foreman/C3-TL-spec.md`: eight new blueprint items, authored and formalized together. NEW `NeSyCat/CategoricalLayer/SemiringMonads/Support.lean`: `def:support-readout` (`supp : S → BoolW`, `if a = 0 then 0 else 1` on `[Zero S] [DecidableEq S]`), `lem:support-hom-iff` (`support_hom_iff`, on a nontrivial semiring `supp` preserves `0,1,+,*` iff `S` is zerosumfree and has no zero divisors — the two hypotheses are exactly the converse halves of facts that already hold unconditionally in any semiring; citing Domingos arXiv:2510.12269 §3.1's Heaviside-step correspondence in a `%` comment per the ticket's citation discipline, invisible on the rendered page), `lem:support-fails-ring` (`support_fails_ring`, `∃`-witness `a=1,b=-1` on `ℤ`, witness kept in the proof per the statement/proof anatomy law). NEW `NeSyCat/CategoricalLayer/SemiringMonads/GradientSemiring.lean`: `def:gradient-semiring` (`GradSemiring S := DualNumber S`, Mathlib's `TrivSqZeroExt S S` identification per the ticket's de-risk note — `TrivSqZeroExt.commSemiring` supplies every semiring law free once `[CommSemiring S]`; a `definition` env since the abbrev carries genuine carrier/operation content, matching the `lem:log-iso` C2-E4a-fix re-kind precedent — rendered prose credits Eisner's expectation semiring, `\citet{eisnerExpectationSemiring2002}`, a real bibliography entry per the visible-attribution law, since Eisner genuinely proved the construction, unlike the Domingos citations which stay in `%` comments), `lem:gradient-semiring-laws` (`gradient_semiring_laws`, bundled `∧`: first projection `TrivSqZeroExt.fst` preserves `0,1,+,*`, second coordinate obeys the Leibniz rule, assembled from Mathlib's `fst_zero`/`fst_one`/`fst_add`/`fst_mul`/`DualNumber.snd_mul` as steps, not a bare citation; citing Domingos §3.3's ungrounded "gradient of a program is again a program" claim in a `%` comment), `inst:gradsemiring-mass`/`inst:gradsemiring-log` (`instCommSemiringGradSemiringMass`/`Log`, the running mass/log rows, both `inferInstance`). NEW subsection "Embedding-space reasoning" (§2.3, `NeSyCat/CategoricalLayer/Embedding/{Embedding,EmbeddingExact}.lean`, structure-mirror folder + `% lean-dir` tag landed in this commit): `thm:embedding-exact` (`embedding_exact`, a `d × Y` embedding matrix `E` over `ℝ` with `Eᵀ * E = 1` gives exact retrieval `Eᵀ(Ev) = v` and exact embedded chaining `(R Eᵀ)(Ev) = Rv` for any relation matrix `R`, both by `Matrix.mulVec_mulVec`/`Matrix.mul_assoc` plus the hypothesis; citing Domingos §5's random-unit-vector "≃" derivation in a `%` comment, disclosed in rendered prose as the exact orthonormal case only, the random-vector error bound left to a future probability layer). Item 7 (bridges rider): a `%`-comment-only citation note added at `def:normalizer` recording Domingos §4.4's `P(Q|E) = Prog(Q,E)/Prog(E)` division claim and how the pre-existing (already-`\leanok`) normalizer/normalized-heads pair keeps conditioning inside the semiring monad rather than as a bare division; no Lean or rendered-text change needed since the item was already formalized. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 90 -> 98 environments — the 8 new envs, kind-check 86 -> 94 names, kernel-truth OK 94 (only `propext`/`Classical.choice`/`Quot.sound`), census 542/86/456/0 -> 550/94/456/0 — all 8 new scanned declarations are the 8 cited names themselves, zero new `@[blueprint_internal]` companions since every helper lemma is Lean `private` (auto-exempted, invisible to the census fold) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0 -> 16/0, the one new subsection), pdf+web rebuilt clean (0 overfull hboxes, confirmed directly against `blueprint/print/print.log`), `lint-blueprint.py` silent on the touched file.) |
| Semiring-monad infrastructure (`M_S`, `D` as mass-one submonad)              | proved (C1-T3: chapter-1 cluster complete — every in-scope Definition/Lemma/Theorem of §"Semiring weight monads" is now `\leanok`, except `rem:semiring-monad-algebras`, which remains an unproved stretch target outside this cluster's scope (no Lean formalization of `MS S`'s algebras is claimed). `def:lattice-semiring`/`def:comm-lattice-semiring`/`def:bounded-lattice-semiring`/`def:bounded-comm-lattice-semiring` (`LatSRng`/`LatCSRng`/`BLatSRng`/`BLatCSRng` in `NeSyCat/CategoricalLayer/SemiringMonads/LatticeSemiring.lean`) now has all three running instances (`ex:lattice-semiring-rows`): Boolean (`BLatCSRng`, bounded), mass (`LatCSRng`, unbounded), and NEW log (`instLatCSRngLogS : LatCSRng LogS` in `NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean`, monotonicity transported along the order isomorphism `logEquiv`). `lem:prob-not-semiring` proved. `def:semiring-monad`/`thm:semiring-monad-laws`/`thm:semiring-monad-commutative` proved in `NeSyCat/CategoricalLayer/SemiringMonads/SemiringMonad.lean` (`MS`, `ret`, `bind`, `bind_apply`, the three monad laws needing no `⊗`-commutativity, and `dstL`/`dstR`/`dst_comm_iff`/`dst_comm` showing the monad's own commutativity is exactly `S`'s). NEW `def:dist-monad` proved (`NeSyCat/CategoricalLayer/SemiringMonads/Dist.lean`: `Dist X` the mass-one subtype of `MS ℝ≥0 X`, `ret_mass_one`/`bind_mass_one` the blueprint's Fubini closure computation, `Dist.pure`/`Dist.bind` the restricted monad structure — not Mathlib's `PMF`, noted). NEW `lem:log-iso` proved (`NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean`: `LogS := WithBot ℝ`, `logEquiv : ℝ≥0 ≃ LogS` transporting a `CommSemiring` structure bridged to the explicit `lse`/`logMul` formulas, `logRingEquiv : ℝ≥0 ≃+* LogS`, and the monad isomorphism `logTensEquiv X : MS ℝ≥0 X ≃ MS LogS X` via `toLogTens_ret`/`toLogTens_bind`; `LogTens` abbrevs `MS LogS`). NEW (C3-TN) the t-norm family, `NeSyCat/CategoricalLayer/SemiringMonads/TNorm.lean`: `def:tnorm` (`TNorm`, a bundled structure, not a class — comm/assoc/monotone-in-each-argument/unit-1 on `unitInterval`), `inst:tnorm-row` (`TRow.instBLatCSRng : BLatCSRng (TRow τ)` for every `τ : TNorm`, `⊕ := max`, `⊗ := τ.op`, distributivity over `max` reusing `chain_binop_sup_right`/`chain_binop_sup_left` from `thm:chain-lin`(i) directly — no fresh distributivity argument needed), `lem:godel-unique-idempotent` (`TNorm.eq_min_of_idempotent`, the two-line proof), `lem:product-not-distrib-psum` (`product_not_distrib_pSum`, scoped honestly to the product t-norm against `pSum`, reusing `prob_not_semiring`'s witness — a blanket `∀ τ` claim is FALSE in general, the drastic t-norm distributes over `pSum` everywhere, checked by hand and disclosed as out of scope, not formalized), and the three named rows `GodelS`/`ViterbiS`/`LukS` (`godelTNorm`/`viterbiTNorm`/`lukTNorm`, re-kinded from the ticket's suggested `instance` env to `definition` env since their Lean form is `def`-kind, not `instance`-kind — `scripts/blueprint.sh`'s kind-check caught this; `lukTNorm`'s associativity is the one nontrivial law, proved once at the real-number level with a four-way case split then lifted to the subtype). Upgraded the KLay connection sentence to the three-for-three form (Gödel module = Gödel row, MPE option = product row, Boolean = Gödel module on `{0,1}`). New bibliography entry `hajekMetamathematicsFuzzyLogic1998`. C3-EXEC item 3 (referee response, computable reference row): NEW `inst:qmass-latcsrng` `\leanok` in `NeSyCat/CategoricalLayer/SemiringMonads/LatticeSemiring.lean` (`instLatCSRngNNRat : LatCSRng ℚ≥0`, same four-`gcongr` proof shape as `instLatCSRngNNReal`'s mass row, but carrying NO `noncomputable` marker — `ℝ≥0`'s own instance needs one because `ℝ`'s Cauchy-sequence construction is not decidable; `ℚ≥0`'s is, kernel-verified: `#eval (2:ℝ≥0)+(3:ℝ≥0)` returns an unevaluated `Real.ofCauchy (sorry ...)` term, `#eval (2:ℚ≥0)+(3:ℚ≥0)` returns `5`). |
| Truth-value structures (tower)                                              | proved (C2-T1: the `BLat2Mon` tower's foundational items are `\leanok` and sorry-free in `NeSyCat/LogicalLayer/TruthStructures/BLat2Mon.lean` + `NeSyCat/LogicalLayer/TruthStructures/BoolInstance.lean` — `def:blat2mon`/`def:blat2cmon` (`BLat2Mon`/`BLat2CMon`, explicit-field classes over `[Lattice α] [BoundedOrder α]`, not `Monoid` instances, since one carrier bears two independent monoids), `def:lin-blat2mon`/`def:lin-blat2cmon` (`LinBLat2Mon`/`LinBLat2CMon`, the 8 linear-distribution laws), `def:dm-structure` (`DMStructure` mixin), `def:zero-bot`/`def:one-top` (`ZeroBot`/`OneTop` `Prop`-mixins) plus `def:unit-bounds` (NEW `UnitBounds` trivial-alias class naming their conjunction), `lem:lin-monotone` (4 argument-versions: `otimes_le_otimes_left/right`, `oplus_le_oplus_left/right`), `lem:lin-lax-duals` (`otimes_inf_le`, `inf_otimes_le`, `le_oplus_sup`, `le_sup_oplus`), and `lem:bool-truth-structure` (full `BoolW` instance stack `instBLat2Mon → instLinBLat2CMon`/`instDMStructure`/`instZeroBot`/`instOneTop` plus the collapse lemmas `oplus_eq_sup`/`otimes_eq_inf` — of the 9 declarations in `lem:bool-truth-structure`'s `\lean` list, 4 (`instZeroBot`, `instOneTop`, `oplus_eq_sup`, `otimes_eq_inf`) close by a single `rfl` each, the other 5 (the `BLat2Mon`/`BLat2CMon`/`LinBLat2Mon`/`LinBLat2CMon`/`DMStructure` instances) by field-wise `decide` on the finite carrier). NEW `NeSyCat/Notation.lean`: scoped `⅋`/`&` infix notation (tested empirically against `∧`/`&&`/structure literals, no conflict) and the macros.sty twin-registry block; the pinned `¬` overload for `DMStructure.dneg` was tried and reverted — it reproducibly poisons elaboration (a same-looking-but-mismatched-type error on ordinary uses, isolated down to the bare overload with no nesting or interaction with `&`/`⅋`), so `DMStructure.dneg` stays the plain working name, flagged for LEAD/user adjudication. NEW (C2-T2, incl. the C2-T2b rider) `NeSyCat/LogicalLayer/TruthStructures/Chain.lean`: `thm:chain-lin` — part (i) lives in four RAW lemmas `chain_binop_sup_right/sup_left/inf_right/inf_left` over bare `[LinearOrder α]` with an explicit operation and a monotonicity hypothesis (no bounds, no monoid laws — the blueprint's "not necessarily bounded" clause is genuinely captured; they instantiate at `ℝ≥0`/`LogS`), with the four `BLat2Mon`-context lemmas `chain_otimes_sup`/`chain_sup_otimes`/`chain_oplus_inf`/`chain_inf_oplus` as one-line corollaries, and `LinBLat2Mon.ofChain` assembling the full structure from those plus `[UnitBounds α]` for the nullary laws — the instance-diamond wrinkle between `BLat2Mon`'s free `[Lattice α]` and `LinearOrder.toLattice` is benign since the two are `rfl`-defeq on every carrier used here, confirmed both abstractly and concretely at `unitInterval`), `lem:dualabsorb-decomposition` (`done_eq_top_iff_otimes_le_inf`/`done_eq_top_iff_sup_otimes_absorb` and their `dzero`/`oplus` duals — both routed through the unit equation as a pivot, since neither outer form implies the other pointwise without it), and `lem:mix` (`otimes_le_inf`, `sup_le_oplus`, `mix_chain`, and the named MIX corollary `otimes_le_oplus`). NEW (C2-T2) `NeSyCat/LogicalLayer/TruthStructures/UnitInterval.lean`: `lem:unit-interval-truth-structure`, the full instance stack on Mathlib's `unitInterval` (`instBLat2Mon` with `oplus p q := σ(σp * σq)` PINNED as the definition, `instBLat2CMon`, `instZeroBot`/`instOneTop`/`instUnitBounds`, `instLinBLat2Mon` built via `LinBLat2Mon.ofChain` — exercising `thm:chain-lin` exactly as the blueprint's own proof does — `instLinBLat2CMon`, `instDMStructure` with `dneg := unitInterval.symm`, and the readout lemma `coe_oplus` recovering the blueprint's `p+q-pq` display formula as a coercion fact, not the definition). NEW (C2-T5) `NeSyCat/LogicalLayer/TruthStructures/DeMorgan.lean`: the De Morgan calculus at class level (`[DMStructure α]`) — `lem:dm-lattice-laws` (`dneg_inf`/`dneg_sup`/`dneg_bot`/`dneg_top`, direct antisymmetry pairs from `dneg_antitone`/`dneg_dneg`, searched against building an explicit `OrderIso` and found no shorter — disclosed route choice), `lem:dm-dual-law` (`dneg_oplus`, the blueprint's own axiom-(iii)-at-the-swapped-args computation), `lem:dm-unit-swap` (`dneg_done`/`dneg_dzero`, via the private two-sided-unit-is-`dzero` helper `oplus_unit_eq_dzero`), `prop:dm-presentations` (`DMFullCalculus`/`dm_presentations`, encoded as `List.TFAE [Antitone n, lattice-DM-law, DMFullCalculus n]` via Mathlib's `tfae_have`/`tfae_finish` — the three-implication-cycle fallback was not needed — with the (a)⇒(c) leg built via `letI : DMStructure α := ⟨n, hinv, hanti, hand⟩` citing the class-level family lemmas verbatim, no proof duplication), and `lem:dm-maps-units` (`dneg_maps_units`, the raw existential form, witness `dneg q`, no Mathlib `IsUnit` since `BLat2Mon` isn't `Monoid`-bundled). NEW (C2-T5) `NeSyCat/LogicalLayer/TruthStructures/Impossibility.lean`: `thm:no-dm-mass`/`thm:no-dm-log` (`no_antitone_involution_nnreal`/`no_antitone_involution_logS`, stated as the PINNED core order fact — "no involutive antitone map on `ℝ≥0`/`LogS`" — rather than a `¬ DMStructure` statement, since `DMStructure` needs `[BoundedOrder α]` and neither carrier has one; the doc comments explain the subsumption of the blueprint's "hence no DM structure" clause) and `thm:square-not-lin` (the full witness cluster on raw ops over `ℝ≥0ᵒᵈ × ℝ≥0`, deliberately NOT a `BLat2Mon` instance — the carrier is unbounded, so the class does not even apply, part of the theorem's own content: `otimesSq`/`oplusSq`/`swapSq` the two-slot formulas mod `toDual`/`ofDual`, `swapSq_swapSq`/`swapSq_antitone`/`swapSq_dm` the DM-structure package, `otimesSq_comm`/`otimesSq_assoc`/`oplusSq_comm`/`oplusSq_assoc` plus the four unit equations the monoid package, `otimesSq_not_monotone_right` the core non-monotonicity witness `p=(1,0)`, `r=(5,0)`, `q=(0,10)` — the `⅋`-dual witness is disclosed as not separately formalized, optional per the ticket and forced anyway by `swapSq_dm`'s exchange mechanism — `monotone_of_distrib_sup` the raw distributivity-implies-monotonicity twin of `lem:lin-monotone`, `otimesSq_not_lin` the concluding refutation by contraposition, and `otimesSqENN_not_monotone_right` the ENNReal persistence witness at `ℝ≥0∞ᵒᵈ × ℝ≥0∞` with the identical numerals). This COMPLETES §"Truth-value structures"'s formalizable slate: every in-scope Definition/Lemma/Theorem/Proposition in the section is now `\leanok` (the four remaining `\label`s in the section are `\begin{remark}` environments, out of scope by the campaign's own convention). Blueprint marks landed with `scripts/blueprint.sh` at 189 kind-checked names, well inside the raised `maxRecDepth` headroom from C2-T4's fix.) |
| Truth spaces `M(Bool)`                                                      | proved (C2-T3: `NeSyCat/LogicalLayer/TruthSpaces/TruthSpace.lean` — `abbr:truth-space` (formerly labeled `def:truth-space`; `TruthSpace S := MS S BoolW`, the `Idmon` clause read directly off `BoolW`), `def:lifted-connective` PINNED via the `n`-ary strength `dstN` (`Fin.cons`/`Fin.tail` structural recursion) with `lift` DEFINED as `bind (dstN w) (Ret ∘ op)` — the blueprint's own iterated-bind definition recovered as arity lemmas `lift_zero`/`lift_one`/`lift_two` — and `lem:lifted-connective-strength` (formerly labeled `cor:lifted-connective-strength`, before the corollary kind was abolished) closing near-`rfl` (`lift_eq_dstN_bind`), `def:two-slot`/`def:dist-readout` (formerly one bundled `lem:truth-space-instances`, later split by the A1 bijection-law pass) via `twoSlot : MS S BoolW ≃ S × S` (`w ↦ (w 0, w 1)`, two-point `Finsupp` support) instantiated at `S := ℝ≥0`/`LogS` for the `Tmon`/`LTmon` rows and `distReadout : Dist BoolW ≃ unitInterval` (single-stage, routing through the mass-one constraint) for the `Dmon` row. Named lifted ops `otimesM`/`oplusM`/`negM` (binary/unary `lift` wrappers); `negM`'s underlying Boolean-negation operand is a `BoolW`-native `ite` (`negOp`, pointwise `= !·` via `negOp_eq_not`) rather than `Bool.not` directly — composing `!` through `lift₁`'s routing machinery reproducibly desynchronized `Decidable`-instance elaboration several layers down, an empirically-isolated and disclosed encoding choice, not a weakening.) |
| Lifted connectives (mass+log, derived `p+q−pq`)                             | proved (C2-T3: `NeSyCat/LogicalLayer/TruthSpaces/Lifted.lean` — the general two-slot routing engine (`lift₂_apply`/`twoSlot_lift₂`, `lift₁_apply`/`twoSlot_lift₁`) proved ONCE at general `[Semiring S]` via `bind_apply_boolW` + `Finsupp.single_apply`, then `\&`/`⅋`/`¬`/units coordinate formulas (`twoSlot_otimesM`/`twoSlot_oplusM`/`twoSlot_negM`/`twoSlot_ret_zero`/`twoSlot_ret_one`) ALSO proved once generically and merely cited at `S := ℝ≥0` (`lem:lifted-mass`) and `S := LogS` (`lem:lifted-log`, phrased via `lem:log-iso`'s `logS_add_eq_lse`/`logS_mul_eq_logMul` bridging lemmas into the blueprint's `lse`/`+` display) — no sum manipulation duplicated per carrier. `def:order-family` PINNED as `orderedTwoSlot : MS S BoolW ≃ Sᵒᵈ × S` (`twoSlot` composed with `OrderDual.toDual`, `OrderDual` supplying the whole order family for free) with meet/join/bounds transported through it as plain functions (`orderMeet`/`orderJoin`/`orderBot`/`orderTop`, never new `Lattice`/`BoundedOrder` instances on `MS S BoolW` — the instance-pollution hard rail); the blueprint's mass/log bounds clauses (`⊥=(∞,0)` etc., needing an adjoined `∞`) are honestly NOT formalized, `ℝ≥0`/`LogS` being unbounded above. `lem:lifted-prob-readout` stated as readout homomorphy: `Dist`-restricted `otimesD`/`oplusD`/`negD` (mass-one closure by the exact Fubini technique of `NeSyCat/CategoricalLayer/SemiringMonads/Dist.lean`'s `bind_mass_one`, reused not reproved) commute with `distReadout` onto T2's stipulated `unitInterval` family (`distReadout_otimesD`/`distReadout_oplusD`/`distReadout_negD`, the latter via `unitInterval.coe_oplus`) — the "derived, not stipulated" content in homomorphism form.) |
| Completions ($[0,\infty]$, $[-\infty,\infty]$)                              | proved (C3-CMP: `NeSyCat/LogicalLayer/Completions/{Completions,MassCompletion,LogCompletion}.lean`, new `\lean`/`\leanok` subsection §"Completions" (`LogicalLayer/Completions`) inserted between "Truth spaces and lifted connectives" and "Three layers". WORKTREE-BASE DISCLOSURE: this ticket's worktree branched before C3-NS/C3-TL/C3-E12/C3-E13/C3-CB landed on the campaign's main line (git log tip at this worktree's start: C3-B4b, `3b5bce6`); the proof-substance law (C3-E12) is not yet in this worktree's own `FORMALIZE.md`, but its displayed-equation-chain standard is followed anyway per the dispatching orchestrator's explicit instruction, and `thm:chain-bound` here is still in its pre-C3-E12 unrestructured form (untouched by this ticket). Mass completion: `inst:mass-completion-latcsrng` (`instBLatCSRngENNReal : BLatCSRng ℝ≥0∞`, Mathlib's own convention `0 * ∞ = 0` stated as a chosen convention, not derived) and `inst:mass-completion-linblat2cmon` (`instLinBLat2CMonENNReal : LinBLat2CMon ℝ≥0∞` with `otimes:=(·*·)`, `done:=1`, `oplus:=(·+·)`, `dzero:=0`, ZeroBot holding via `instZeroBotENNReal` — the four linear laws via `Chain.lean`'s raw `chain_binop_sup_right`/`sup_left`/`inf_right`/`inf_left` at `f:=*`/`f:=+` needing no bound, the nullary laws via `ℝ≥0∞`'s own `mul_zero`/`zero_mul`/`add_top`/`top_add`, NOT via `LinBLat2Mon.ofChain` since that constructor needs `UnitBounds`, which fails here). `thm:mass-completion-not-unitbounds` (`not_oneTop_ennreal : ¬ OneTop ℝ≥0∞`, since `done = 1 ≠ ⊤ = ∞`) states the REGIME-BOUNDARY claim exactly as strong as proved: UnitBounds separates a bounded/normalized regime (probability row, both `ZeroBot` and `OneTop`) from an unbounded/mass regime (`ZeroBot` alone), not linear-logic-structure from its absence — both rows are full `LinBLat2CMon`. `thm:mass-submeet-fails`/`thm:mass-mix-fails` (`otimes_not_le_inf_ennreal`/`otimes_not_le_oplus_ennreal`, THE TWO SEPARATING COUNTEREXAMPLES, both witnessed at $p=q=3$: $3\otimes 3=9\not\le 3=3\wedge 3$, and $9\not\le 6=3\oplus 3$ — exactly the necessity witnesses for `lem:mix`'s `OneTop`/`UnitBounds` hypothesis, verified against the recorded framing before stating, matching the ticket's own "9 ≰ 6" check). `thm:no-dm-mass-completion` (`no_dm_ennreal`, THE DM QUESTION RESOLVES CLEANLY, in the negative: no antitone involution on `ℝ≥0∞` satisfies the De Morgan law for `(·,+)`, even though the order is self-dual (e.g. via reciprocal) — proof combines two GENERAL `DMStructure` facts needing no UnitBounds, `dneg_bot`/`dneg_dzero` from `DeMorgan.lean`, which collide at `dneg 0` exactly where ZeroBot holds without OneTop; NOT recorded via the retired "Open." convention, since it resolved). `lem:mass-completion-bounds`/`lem:log-completion-bounds` (`lifted_mass_bounds`/`lifted_log_bounds`) DISCHARGE `def:order-family`'s deferred bounds clause (Lifted.lean's `orderBot`/`orderTop`/`twoSlot_orderBot`/`twoSlot_orderTop`, generic under `[BoundedOrder S]` since C2-T3 but previously uninstantiable at `S:=ℝ≥0`/`LogS`) at the two completed carriers: `⊥=(∞,0)`, `⊤=(0,∞)` (mass) and `⊥=(∞,-∞)`, `⊤=(-∞,∞)` (log), closing the four forward pointers left in `content.tex` at `inst:massS-latcsrng`/`inst:logS-latcsrng`, `thm:no-dm-log`, `lem:log-iso`'s dictionary-table row, and `lem:lifted-mass`. Log completion: `inst:log-completion-latcsrng` (`instBLatCSRngLogSInf : BLatCSRng LogSInf`) EVALUATES `EReal` FIRST per the ticket's own instruction and finds it exactly right — Mathlib's `EReal` native `+` already carries the FORCED convention `⊤+⊥=⊥` (i.e. `∞+(-∞)=-∞`), built deliberately "to make sure that the exponential and logarithm between `EReal` and `ℝ≥0∞` respect the operations" (`EReal/Operations.lean`'s own module doc), and Mathlib's `ENNReal.logOrderIso : ℝ≥0∞ ≃o EReal` (`ENNReal.log`/`EReal.exp`) supplies the order isomorphism and the unconditional `ENNReal.log_mul_add` ready-made — no hand-built log/exp pair was needed, unlike the finite `LogIso.lean`. `LogSInf := EReal` is still a FRESH type synonym (not `EReal` itself), since `EReal` already carries competing `Add`/`Mul` instances that a fresh `CommSemiring` registration would collide with, exactly `LogS`'s own reason for not being `WithBot ℝ` itself; `lseInf`/`logMulInf` are the completion's explicit `⊕`/`⊗` formulas, bridged to the transported `+`/`*` by `logSInf_add_eq_lseInf`/`logSInf_mul_eq_logMulInf`, mirroring `LogIso.lean`'s `logS_add_eq_lse`/`logS_mul_eq_logMul` exactly (names carry an `Inf` suffix throughout to avoid colliding with `LogIso.lean`'s identically-shaped names in the same `NeSyCat` namespace). `lem:quantifier-columns-nestable` MARKED (`\lean{NeSyCat.quantifier_columns_nestable}\leanok`) per the C3-ADJ user ruling recorded in `.foreman/C3-NS-spec.md`: `NeSyCat/GrammaticalLayer/QuantifierColumns.lean`'s six-column instantiation re-pointed so `min`'s seed moves from `unitInterval`'s `1` to `ℝ≥0∞`'s `⊤`, landing max/min/Σ/Π ALL on the mass completion (one carrier for the four running families, exactly what the ruling's "wait for the top" condition asked for); the log twins stay on `LogS` untouched (they never needed a top). All sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`); `scripts/check.sh` GREEN (whole project); `scripts/sorry-report.sh` 0/0; `scripts/blueprint.sh` GREEN — structure 89 -> 98 environments (9 new: 2 `inst:mass-completion-*`, 3 `thm:mass-*`/`thm:no-dm-mass-completion`, 2 `lem:*-completion-bounds`, 1 `inst:log-completion-latcsrng`), kind-check 85 -> 95 names (the 9 new envs' names plus `quantifier_columns_nestable` newly marked), kernel-truth OK 95, census 573 scanned (95 cited, 478 internal, 0 unclassified), registry sync 9 twins, structure-mirror 16/0; pdf+web rebuilt clean (0 overfull hboxes), lint-blueprint.py silent on the touched file. ONE worktree commit; report at `.foreman/scratch/C3-CMP-report.md`.) Merge: this ticket's worktree `b0b7974` merged to main; the gate numbers recorded above are worktree-era, and the merged main-line sentinels are recorded at the merge commit. |
| Pointwise/linear-laws/copying-laws lemmas + three-layers theorem            | proved (C2-T4; the marks-blocking kind-check maxRecDepth ceiling was closed by the LEAD one-line generator fix and the held-back marks landed, both in commit 1ca5ee5 — all four items are `\leanok` statement+proof at HEAD, CORRESPONDENCE OK at 163 names: `NeSyCat/LogicalLayer/ThreeLayers/ThreeLayers.lean` — `lem:pointwise` via `instLatSRngProd`/`instLatCSRngProd`/`instBLatSRngProd`/`instBLatCSRngProd` (Prod, `Mathlib`'s `Prod.instSemiring`/`Prod.instLattice`/`Prod.instBoundedOrder` plus the four monotonicity fields componentwise) and `instLatSRngPi`/`instLatCSRngPi` (Pi, ARBITRARY index type `ι`, generalizing the blueprint's "(finite) power" clause a fortiori — the chapter-1 Lean-more-general precedent), plus the `S^𝔹 ≅ S × S` transport as equational lemmas on values (`twoSlot_add`, real content since `MS S BoolW` genuinely has `+`; `pointwiseMul`/`pointwiseOne`/`pointwiseMeet`/`pointwiseJoin`/`pointwiseBot`/`pointwiseTop` as plain (non-instance) `def`s pulling `S × S`'s own ops back through `twoSlot`, mirroring `orderMeet`/`orderJoin`'s pattern but un-dualized — Finsupp has no canonical pointwise-mul instance, so no instance is registered on `MS S BoolW`, the hard rail honored). `lem:linear-lift` over `[CommSemiring S]`: `otimesM_assoc`/`otimesM_comm`/`ret_one_otimesM`/`otimesM_ret_one`, `oplusM_assoc`/`oplusM_comm`/`ret_zero_oplusM`/`oplusM_ret_zero`, `negM_negM`/`negM_ret_zero`/`negM_oplusM`/`negM_otimesM` — all by `twoSlot` transport (`twoSlot.injective` + `lem:lifted-mass`'s routing formulas, the blueprint's own sanctioned proof route), assoc needing no commutativity (`ring`-provable from the semiring axioms alone), comm being exactly where `S`'s `mul_comm` enters (the concrete shadow of `thm:semiring-monad-commutative`'s `dstL = dstR ↔ S` commutative). `lem:copying-fails`: `fairCoin` (`distReadout.symm` of `½`), `otimesD_fairCoin_ne` (`¼ ≠ ½` via `distReadout_otimesD`), and `exists_otimes_ne_self` (the general `∃ p ∈ (0,1), p \& p ≠ p` witness, matching the blueprint's own `∃`-statement shape). `thm:three-layers` witness cluster: (i) `latCSRngBoolWSq`/`latCSRngNNRealSq`/`latCSRngLogSSq` (resolution witnesses at the three named squares, citing `prob_not_semiring` for the excluded row); (ii) needs no additional Lean (covered by `lem:linear-lift`/`lem:copying-fails`'s own marks); (iii) `order_iff_inf_eq_left` (`u ≤ v ↔ u ⊓ v = u`), the `𝔹`-coincidence citing `BoolW.oplus_eq_sup`/`BoolW.otimes_eq_inf` (NOT a claim that `MS BoolW BoolW`'s `otimesM`/`oplusM` pointwise-agree with `orderMeet`/`orderJoin` — checked by hand and found false, the disprove-guard catching a wrong reading before it was written), units-vs-bounds citing `unitInterval.instUnitBounds` (positive) and `not_isBot_orderedTwoSlot_ret_zero` (negative, the `⅋`-unit's `orderedTwoSlot` image at `S := ℝ≥0` is not a bottom). All sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`), `scripts/check.sh` GREEN. (Historical, RESOLVED at 1ca5ee5: the kind-check's flat do-block hit Lean's default `maxRecDepth` past ~123 names; the LEAD one-line generator fix — `set_option maxRecDepth 8000` — closed it, and this cluster's marks landed in the same commit.) ) |
| Categorical signatures and CD semantics (`Σ_α`, CD category, `𝓘_α`)        | stated (C3-B1: `def:categorical-signature`/`def:cd-category`/`def:categorical-interpretation` all `\leanok` in `NeSyCat/CategoricalLayer/Signatures/Signatures.lean` — `CatSignature` (three bare name fields `catSymbol`/`actorSymbol`/`monadSymbol`, `Mon := {Id, ○}`'s companion code `MonSym`, `@[blueprint_internal]`), `CDCategory` (route (a) of the LEAD encoding pin: `[Category C] [MonoidalCategory C] [SymmetricCategory C]` plus a chosen `ComonObj X`/`IsCommComonObj X` on every object, `copy_tensor`/`del_tensor` stating that the chosen comonoid on `X ⊠ Y` agrees with the one Mathlib's own `ComonObj (A ⊗ B)` instance induces from `X`'s and `Y`'s — no law beyond what the environment states), and `CatInterpretation` (`cd : CDCategory`, an actor category `A`, the actegory action `act : A → cd.C → cd.C` as a bare object map with NO functoriality/coherence fields — the environment states none, and `def:domain-interpretation` only ever applies it to objects — and `monad : CategoryTheory.Monad cd.C`; `CatInterpretation.interpretMon`, `@[blueprint_internal]`, is the companion definitional clause for "`Id` is always interpreted by the identity functor"). All three definitions only, no theorem proofs in this batch; the three running interpretations (Set/Tens/Identity, Set/Tens/Dist, Tens/Tens/LogVec) are prose examples, not envs, and are not formalized. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 environments unchanged, kind-check 56 -> 59 names, kernel-truth OK 59, census 317/56/261/0 -> 333/59/274/0 -- the 16 new scanned declarations are the 3 cited structures plus `MonSym`/`CatInterpretation.interpretMon` and 11 `deriving`-synthesized `DecidableEq`/`Repr` byproducts, all `@[blueprint_internal]`, matching the `BoolW` precedent for post-hoc-tagged derived instances -- 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) |
| Logical signatures (`Σ_β`, `𝓘_β`)                                          | stated (C3-B2: `def:logical-signature`/`def:logical-interpretation` both `\leanok` in `NeSyCat/LogicalLayer/LogicalSignatures/LogicalSignatures.lean` — `LogSignature` (`tauSymbol : String`, `Conn`/`connArity`/`connMonad`, `Quan`/`quanMonad`, reusing B1's `MonSym` for `Mon`) and `LogInterpretation` (`Ω : I.cd.C`, `connMor : ∀ c, (I(M)Ω)^⊠(arity c) ⟶ I(M)Ω`, `quanMor : ∀ Q n, (I(M)Ω)^⊠n ⟶ I(M)Ω`, both via the new shared `tensorList`/`interpretPow` companions, `@[blueprint_internal]`). **Comparison-symbol gap, disclosed not resolved**: the environment's prose names a "comparison symbol" `≺ : Mτⁿ → MBool` alongside the plain connective `* : Mτⁿ → Mτ`, but `def:logical-signature`'s own "consists of" sentence gives `Conn` only arity + monad symbol data — no field distinguishing which members are Bool-targeted — and `def:logical-interpretation` confirms the reading by interpreting every connective uniformly via `connMor`, with no separate Bool-valued clause anywhere. `LogSignature`/`LogInterpretation` are encoded with exactly the stated data; no `ConnTarget`/Bool-codomain field was added (a deviation from the night-campaign LEAD sketch's own suggestion, disclosed here — see `.foreman/scratch/C3-B2-report.md`). Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0.) |
| Domain layer (`Σ_γ`, writing convention, `𝓘_γ`)                            | stated (C3-B2: `def:domain-signature`/`def:domain-signature-notation`/`def:domain-interpretation` all `\leanok` in `NeSyCat/DomainLayer/DomainLayer.lean` — `DomSignature` (`Dom`/`Spc`/`Fun`/`Rel`/`Var`/`Par` Type-valued symbol sets, `fdom`/`fcod`/`fpar`/`rari`/`rpar`/`varOver`/`parOver` matching the environment's `dom`/`cod`/`par`/`ari`/`par`/`ovr`/`ovr` functions verbatim) and `DomInterpretation` (`domObj : Dom → I.cd.C`, `spcObj : Spc → I.A`, `funMor`/`relMor` valued in the actegory action `I.act`, via the new `interpretMS`/`interpretSpc` companions for `𝓘(M₁S₁,…,MₙSₙ)`/`𝓘(Θ₁,…,Θₖ)`; `DomInterpretation.interpretVar`/`interpretPar`, `@[blueprint_internal]`, are the companion definitional clauses for `𝓘(x) := id`/`𝓘(θ) := id`). **`def:domain-signature-notation` no-Lean exemption retired**: attempted the honest display-function counterpart the FORMALIZE.md pin itself invites, `DomSignature.TypedSymbol.display` (a `String`-valued display over a `fun_`/`rel`/`var`/`par` sum type, `ToString` instances on the abstract symbol Types plus a `monName : String` parameter standing in for the signature's own `○` name) — it lands cleanly (pure `String`/`List` code, no monoidal-category involvement), so the environment now carries `\lean`/`\leanok` marks; kind-check accordingly reads 64 names (not 63). The `FORMALIZE.md` pin text describing this as a standing no-Lean exemption is now stale and needs a follow-up documentation edit — out of this ticket's write set (`NeSyCat/**`, `content.tex` marks, `PROGRESS.md` only), flagged here for a follow-up ticket. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN for both clusters together (structure 88 environments unchanged, kind-check 59 -> 64 names, kernel-truth OK 64, census 333/59/274/0 -> 347/64/283/0 -- the 14 new scanned declarations are the 5 cited names plus 9 `@[blueprint_internal]` companions (`tensorList`, `interpretPow`, `displayMonDom`, `interpretMS`, `interpretSpc`, `DomInterpretation.interpretVar`, `DomInterpretation.interpretPar`, `DomSignature.TypedSymbol`, `DomSignature.TypedSymbol.ctorElimType`) -- 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) |
| Grammatical layer (`Σ_δ`, contexts, wire adapters, feed-forward)            | stated (C3-B3: `def:context`/`def:grammatical-signature`/`def:wire-adapters`/`def:feed-forward` all `\leanok` — `NeSyCat/GrammaticalLayer/Context.lean` (`Context sigG := {l : List sigG.Var // l.Nodup}`, the Elephant-style Nodup-list presentation); `NeSyCat/GrammaticalLayer/Grammar.lean` (`GramSignature sigG sigB : Type × Type := (Tm sigG sigB, Fm sigG sigB)`, the cited principal bundling the grammar's two syntactic categories as the pair of Types itself — `Tm`/`Fm` mutual inductives, raw untyped syntax per the CODES + INTERPRETATION pin, the six grammar rules as six constructors, substitution an explicit `Fm.subst` constructor; `Tm.inn`/`Fm.on` structural free-variable computation, `Tm.out := Tm.inn` disclosed — the document states no separate formula for a functional term's output beyond the one law `inn(ξ)=out(ξ)` for variable terms, and its own Kleisli-interpretation typing table reads a functional term's codomain off `Σγ.fcod f` directly; `Tm.WellFormed`/`Fm.WellFormed` extrinsic Prop predicates carrying all three pinned WF conditions — arity match, `x ∈ [φ]` for `subst`, and context distinctness/`xs.Nodup` for `quant` — decided separately from the untyped grammar); `NeSyCat/GrammaticalLayer/WireAdapters.lean` (`adapter` the cited principal for `def:wire-adapters`, the four-row marker table as one `match`-defined morphism via `adapterTargetMon`/`adapterCod` companions, `isBoundWire`/`bindSet` the bind-set `J` companion; `feedForward` the cited principal for `def:feed-forward`, the Do-form composite via the recursive wire-sequencing engine `StrongCatInterpretation.bindWires`, `Fmor ≫ adaptedTensor ≫ bindWires ≫ 𝓜g`, plus the point-free reformulation `feedForwardPointFree` and the proof obligation `feedForward_eq_pointFree` — Do-form and point-free agree by the monad's right-unit law collapsing `bind(g≫η)` back to `𝓜g`). **STRENGTH TRAP resolved**: `def:categorical-interpretation`'s `CatInterpretation.monad` bundles only "a monad" (no strength); the section opener's "Kleisli category of a STRONG monad" (content.tex l.654) is scene-setting prose, not itself an environment. `def:feed-forward` is the first environment in the document to write down a strength morphism (`σ^{(j)}`, in its point-free form) — `def:wire-adapters`' own per-wire table needs no strength (built from `CatInterpretation.monad`'s unit `η` alone). Strength lands as `StrongCatInterpretation`, a companion wrapper structure of `CatInterpretation` defined in `NeSyCat/GrammaticalLayer/WireAdapters.lean` (NOT a field added to `CatInterpretation` itself, `NeSyCat/CategoricalLayer/Signatures/Signatures.lean` being out of this ticket's write set — flagged as a natural fold candidate for a future ticket), with `leftStrength`/`dst` derived via the CD category's symmetry and the monad's multiplication, mirroring `SemiringMonad.lean`'s own concrete `dstL`/`dstR`/`dst` pattern abstractly. At the fully abstract CD-category level this layer is stated at, threading multiple tensor-factor wires through a Kleisli-style bind is only meaningful via strength — both the recursive Do-form (`bindWires`) and the point-free reformulation use it, disclosed as a genuine reading (not an artifact) of the STRENGTH TRAP: sequencing a Kleisli Do-block over several tensor factors abstractly requires strength regardless of which of the two formulas is "primary". Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 environments unchanged, kind-check 64 -> 68 names — the four new cited names, kernel-truth OK 68, census 347/64/283/0 -> 387/68/319/0 — the 40 new scanned declarations are the 4 cited names plus 36 `@[blueprint_internal]` companions/byproducts (`Tm`, `Fm`, `Tm.inn`, `Tm.out`, `Fm.on`, `Tm.WellFormed`, `Fm.WellFormed`, `adapterTargetMon`, `adapterCod`, `isBoundWire`, `bindSet`, `sourceTensor`, `targetTensor`, `adaptedTensorCod`, `adaptedTensor`, `StrongCatInterpretation`, `StrongCatInterpretation.leftStrength`, `StrongCatInterpretation.dst`, `StrongCatInterpretation.bind`, `StrongCatInterpretation.bindWires`, `StrongCatInterpretation.feedForwardPointFree`, `StrongCatInterpretation.feedForward_eq_pointFree`, plus the mutual-inductive/equation-lemma byproducts `Tm.brecOn.go`/`.eq`, `Tm.brecOn_1.go`/`.eq`, `Tm.brecOn_2.go`/`.eq`, `Fm.brecOn.go`/`.eq`, `Tm.ctorElimType`, `Fm.ctorElimType`, `Tm.inn.eq_def`, `Fm.on.eq_def`, `Tm.WellFormed.eq_def`, `Fm.WellFormed.eq_def`) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes). One deviation disclosed: `def:wire-adapters`/`def:feed-forward` are encoded generically over an explicit wire list `List (MonSym × MonSym × Dom)` and a bare object map `dObj : Dom → I.cd.C` (matching `interpretMS`'s own established genericity pattern in `DomainLayer.lean`), rather than literally through two `DomSignature.Fun`/`Rel` symbols `f`,`g` and their `fdom`/`fcod` lists — the per-wire/per-position mathematical content is identical either way, — genericity is the document's own intended level, though `def:kleisli-interpretation` (B4) does NOT literally call `feedForward`: it rebuilds its own `⨟`-composites (the term/relation-symbol clause, and — after C3-B4-FIX's BOTH-MARKERS repair — the `Id`-marked connective/quantifier clauses) directly from `StrongCatInterpretation.dst`/`strength`/`bind`, per-use, rather than by instantiating the generic `feedForward` machinery; see the C3-B4-FIX ledger entry below for the corrected description.) (C3-B4: `def:kleisli-interpretation` `\leanok` in `NeSyCat/GrammaticalLayer/Kleisli.lean` — the env's one cited principal is `Fm.sem` (`⟦φ⟧ : 𝓘([φ]) → 𝓜Ω`), `Tm.sem` (`⟦ξ⟧ : 𝓘(inn ξ) → 𝓜𝓘(kcod ξ)`) its `@[blueprint_internal]` mutually-recursive term-side half; both by structural recursion over all six grammar rules. Six cases: variable term `⟦x⟧ := η`; functional term `⟦f(ξ⃗)⟧ := ⟦ξ⃗⟧ ⨟_∘ 𝓘(f)` via `TmList.sem` (tensor-then-bind over the argument list, no `copy` needed since `Tm.inn`'s flatten already gives each occurrence its own slot) composed with the new `KleisliInterpretation.funMorK`; atomic formula `⟦R(ξ⃗)⟧` identically via `relMorK`; compound formula `⟦*(φ⃗)⟧ := ⟦φ⃗⟧ ⨟ 𝓘(*)` via `FmList.sem` (left uncollapsed, feeding `LogInterpretation.connMor` directly) composed with `connMor`; quantified formula `⟦Qx⃗(φ)⟧` via the product-state enumeration `listCard`/`listPt` (folded from `KleisliInterpretation.varCard`/`varPt` through `finProdFinEquiv`'s lexicographic decomposition), the `n`-ary self-copy `comulN` (from the CD category's chosen comonoid) of the remaining context, per-state insertion via the new context-merge primitive `ctxMerge` (structural on the context list, sliding each variable past the recursively-built rest via symmetry — reused for both the quantifier's multi-position and the substitution's single-position insertion), `tensorFin`'s indexed tensor of the resulting per-state semantics feeding `LogInterpretation.quanMor`; substituted formula `⟦φ[x:=ξ]⟧ := ⟦ξ⟧^{(p)} ⨟_∘ ⟦φ⟧` via `ctxAppendIso`/`SI.strength` threading the term's semantics into `x`'s slot, `ctxMerge`+`SI.bind` joining it into `body`'s own semantics. **Three disclosed deviations** (documented in-file, `Kleisli.lean`'s module doc and each companion's doc comment): (1) `def:domain-interpretation`'s `funMor`/`relMor` thread the actegory action `I.act(𝓘(Θ⃗))(-)` against a symbol's parameter space, but this grammar's six rules supply no syntax for passing parameters to a functional/atomic-formula node and this environment's own typing table elides `I.act` entirely (matching `def:wire-adapters`' own parameter-subscript elision) — `KleisliInterpretation` (new companion structure, `@[blueprint_internal]`, mirroring the STRENGTH TRAP precedent's `StrongCatInterpretation`) supplies `funMorK`/`relMorK` directly at the parameter-free instance the table needs, plus the quantifier clause's finite-enumeration data (`varCard`/`varPt`); (2) `Tm.KTyped`/`Fm.KTyped` (new extrinsic Prop side conditions, `@[blueprint_internal]`, threaded as explicit hypotheses to `Tm.sem`/`Fm.sem`, per the Prop-elimination doctrine) state the value-type match between a function/relation symbol's declared slots and its arguments' own `Tm.kcod` — a condition `Tm.WellFormed`/`Fm.WellFormed` (arity-only) do not state; the same predicate restricts a compound/quantified formula's connective/quantifier to its `○`-marked instance (`connMonad c = Id`/`quanMonad Q = Id` is not encoded — the case every one of the four running quantifier families and their connectives actually are); (3) the substituted-formula clause further restricts to a variable occurring exactly once in `body.on` (`Fm.KTyped`'s subst case) — the document's "single-position insertion" reading; the general "copy the computation's value into every occurrence of `x`" reading (the dice-or-die example) needs an `n`-ary copy of the term's own value this ticket does not build. **`lem:quantifier-nestable`: explicit remainder, not landed.** Two real attempts: (i) traced the document's own length-induction proof sketch against this file's concrete quantifier-clause encoding (`listCard`/`listPt`/`ctxMerge`/`comulN`/`tensorFin`) and confirmed the base case `l=1` is definitional (the simultaneous and iterated readings are literally the same expression, nothing to prove) but the inductive step needs `Nestable`/`Symmetric` formalized as Props on `LogInterpretation.quanMor` (block-grouping and permutation-invariance respectively) plus a substantial reindexing argument connecting `finProdFinEquiv`'s lexicographic product-state decomposition to "peel the first variable, recurse on the rest" — a second, independent piece of categorical infrastructure on the scale of the insertion machinery itself; (ii) confirmed no shortcut through the existing companions (`ctxMerge`'s generality doesn't reduce the reindexing burden, and `Tm`/`Fm`'s `KTyped`-hypothesis threading pattern doesn't shrink a length-induction over an arbitrary-order variable list). Per the hard sorry ban, no `theorem` statement for `lem:quantifier-nestable` was added to Lean or `\lean`/`\leanok`-marked in `content.tex` — landing an unproved statement is not an option; the lemma stays fully open, reported here as the ticket's disclosed remainder for a future ticket. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 environments unchanged, kind-check 68 -> 69 names — the one new cited name `Fm.sem`, kernel-truth OK 69, census 387/68/319/0 -> 406/69/337/0 — the 19 new scanned declarations are the 1 cited name plus 18 `@[blueprint_internal]` companions/byproducts (`Tm.kcod`, `ctxObj`, `KleisliInterpretation`, `ctxMerge`, `listCard`, `listPt`, `ctxAppendIso`, `kcodAppendIso`, `comulN`, `tensorFin`, `Tm.KTyped`, `TmList.sem`, `Tm.sem`, `Fm.KTyped`, `FmList.sem`, `Tm.KTyped.eq_def`, `Fm.KTyped.eq_def`, `Fm.KTyped.congr_simp`) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) |
| Grammatical layer — C3-B4-FIX (verification-driven repair of the Kleisli interpretation) | proved (blind verifier confirmed `def:kleisli-interpretation`'s overall encoding faithful except five gaps, all now repaired in `NeSyCat/GrammaticalLayer/{Grammar,Kleisli}.lean`: (1) CONTEXT FIDELITY — `Fm.on` now returns the genuinely deduplicated context (`firstDedup`, an order-preserving first-occurrence dedup, `Grammar.lean`, plus its `mem_firstDedup`/`firstDedup_nodup` companions) for the `.rel`/`.conn` clauses, matching `def:context`'s distinct-list reading; `Fm.sem`'s `.rel`/`.conn` clauses now prepend the new `ctxCopy` companion (`Kleisli.lean`: `ctxProjFilter`/`filter_eq_singleton_of_nodup_mem`/`projTo` build the single-variable projection, `ctxCopy` itself comultiplies the whole deduplicated context once per target-list position and projects), routing one copy of each shared variable to every raw occurrence — exactly the document's own `copy : I([φ⃗]) -> I([φ_1]) ⊠ ... ⊠ I([φ_n])`; (2) POSITIONAL SUBSTITUTION — `Fm.on`'s `.subst` clause now splices `t.inn` at `x`'s own position in `body.on` (via `List.takeWhile`/`List.dropWhile`, plus the new `list_split_pre_post` reassembly lemma needing only `x ∈ body.on`) rather than appending it at the list's end, matching the document's `[φ]_{[x]↦inn(ξ)} = [y_1,...,y_{p-1}] + inn(ξ) + [y_{p+1},...,y_m]` reading; `Fm.sem`'s `.subst` clause rebuilt to match, threading the term's (unitor-squeezed) value through `SI.leftStrength`/`SI.strength` into the reassembled position, joined via `SI.bind`; (3) BOTH MARKERS — `Fm.KTyped`'s `connMonad c = ○`/`quanMonad Q = ○` restrictions dropped; `Fm.sem`'s `.conn`/`.quant` clauses now dispatch on `sigB.connMonad c`/`sigB.quanMonad Q` directly, composing `FmList.sem`'s tensor of monadic factors straight into `connMor`/`quanMor` at the `○`-marked instance, or first collapsing it via the new `dstFoldN` (`n`-ary `StrongCatInterpretation.dst`-fold, `Kleisli.lean`) before applying the plain `Id`-marked morphism inside the monad — the `def:wire-adapters` `○`/`Id` bind-set row, rebuilt directly from `dst` rather than by invoking `feedForward`; (4) the substitution clause's `Fm.KTyped` conjunct is now literally the document's own `x ∈ body.on` (the exactly-once filter condition dropped — with `body.on` a genuine context whenever it is itself dedup'd/filtered, mere membership already forces uniqueness, and `Fm.sem`'s new positional construction only ever needs `x`'s first occurrence regardless); (5) `Kleisli.lean`'s module doc rewritten to record the file's own remaining deviations in place (no `feedForward` reuse — this file rebuilds `⨟`-composites directly from `SI.dst`/`strength`/`bind`; the `funMorK`/`relMorK` parameter-free bridging, no-coherence debt; the `varCard`/`varPt` finite-enumeration-completeness encoding), and the PROGRESS.md C3-B3 entry's false `feedForward`-reuse claim corrected in place. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 environments unchanged, kind-check 69 names unchanged — no cited name renamed, `content.tex` untouched, kernel-truth OK 69, census 406/69/337/0 -> 415/69/346/0 — the 9 new scanned declarations are all `@[blueprint_internal]` companions/byproducts (`firstDedup`, `mem_firstDedup`, `firstDedup_nodup`, `list_split_pre_post` in `Grammar.lean`; `ctxProjFilter`, `filter_eq_singleton_of_nodup_mem`, `projTo`, `ctxCopy`, `dstFoldN` in `Kleisli.lean`) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes, `content.tex` unchanged so nothing to rebuild against). |
| Batch monad + transformer + pointwise evaluation                           | partial (C3-B6(+B10): `def:batch-monad`/`thm:batch-transformer` `\leanok` in `NeSyCat/StatisticalLayer/Batching/{BatchMonad,BatchTransformer}.lean`; `thm:pointwise-eval` PART 1 ONLY `\leanok`, part 2 split out honestly. `Bmon B X := Fin B → X` (PLAIN FUNCTIONS, disclosed encoding pin: `Fin B`-indexed reader monad, hand-rolled `Bmon.ret`/`Bmon.bind` mirroring `SemiringMonad.lean`'s own `ret`/`bind` style — no `Monad`/`LawfulMonad` instance for `MS S` exists to route through Lean's `ReaderT (Fin B) Id` here). `thm:batch-transformer` switches encodings once an inner effect monad `M` enters: `BmonT B M X := ReaderT (Fin B) M X` (Lean/Mathlib's own `ReaderT`, disclosed), reusing Lean core's `LawfulMonad (ReaderT ρ m)` instance (`Init/Control/Lawful/Instances.lean`, given `[Monad M] [LawfulMonad M]`) as BACKGROUND machinery for "the composite is again a monad" clause, and proving the two canonical lifts by hand: `liftM` (the `MonadLift`-shaped embedding, definitionally Lean core's own `ReaderT` `MonadLift` instance) and `liftBmon` (a `MonadFunctor`-SHAPED lift along `M`'s unit, DISCLOSED as not literally an instance of Lean core's `MonadFunctor` class — that class's `monadMap` signature is a same-monad endo-map `{β} → m β → m β`, not a monad-changing map `Id ⟶ M`, so `liftBmon`/`liftBmon_ret`/`liftBmon_bind` are hand-proved, the bind clause reducing to `M`'s own left-unit law `pure_bind`). Bundled principal `batchTransformer` cites `liftM_ret`/`liftM_bind`/`liftBmon_ret`/`liftBmon_bind` (all `@[blueprint_internal]` companions), matching `semiring_monad_laws`'s own bundling precedent. `thm:pointwise-eval` SPLIT (bijection-law peer-claim split, two genuine claims the original env bundled): PART 1 keeps the `thm:pointwise-eval` label (`ev_i` is a monad morphism, unconditional — `NeSyCat.ev_isMonadMorphism`, `\leanok` both sides, two `rfl`s from `ReaderT`'s own diagonal-bind unfolding); PART 2 is the NEW env `thm:pointwise-eval-kleisli` (commutation with the Kleisli interpretation of `def:kleisli-interpretation` under the batch-naturality hypothesis) — carries NO `\lean`/`\leanok` mark on either statement or proof, left for a rider ticket: it needs a generic account of the Kleisli interpretation over an ARBITRARY strong monad `M` (to instantiate at both `M` and `Bmon M`), which `NeSyCat/GrammaticalLayer/Kleisli.lean` does not provide (built only for the library's own concrete interpretations) — the real dependency, not literally `lem:quantifier-nestable`/B4b (a different open item) though the spec named that as the blocking rider. B10 stray `lem:bind-matrix-mult` `\leanok`: retagged the PRE-EXISTING `NeSyCat.bind_apply` (`SemiringMonad.lean`, formerly an undisclosed `@[blueprint_internal]` companion of `def:semiring-monad`'s `bind`) as this lemma's own cited principal — its formula `bind f k y = f.sum fun x w => w * k x y` already IS the blueprint's matrix-multiplication identity, immediate unfolding, no new Lean needed. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 88 -> 89 environments — the one new `thm:pointwise-eval-kleisli` env, kind-check 69 -> 73 names — `NeSyCat.Bmon.bind`/`NeSyCat.batchTransformer`/`NeSyCat.ev_isMonadMorphism`/`NeSyCat.bind_apply`, kernel-truth OK 73, census 415/69/346/0 -> 428/73/355/0 — the 13 new scanned declarations are the 3 newly-cited names (`bind_apply` was already scanned, now flips internal -> cited) plus 10 `@[blueprint_internal]` companions/byproducts (`Bmon`, `Bmon.ret`, `BmonT`, `liftM`, `liftBmon`, `liftM_ret`, `liftM_bind`, `liftBmon_ret`, `liftBmon_bind`, `ev`) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) C3-EXEC item 1 (referee response, carrier-agnostic exactness): NEW `thm:batch-exactness` `\leanok` in `NeSyCat/StatisticalLayer/Batching/BatchTransformer.lean` (`NeSyCat.batch_layer_exact`, a six-clause bundling theorem citing `batchTransformer`/`ev_isMonadMorphism` verbatim, no new proof) — the point being that its OWN statement is fully generic (`X Y : Type` unconstrained — `Type`, not `Type*`, the inner monad being taken at `Type -> Type*`; corrected at C3-EXEC-FIX — with `[Monad M]` only and NO `[LawfulMonad M]` since C3-EXEC-FIX2, no `Semiring`/`LatCSRng`/lattice hypothesis anywhere), mechanically confirmed by the classification gate (item 2, corrected and gated at C3-EXEC-FIX) finding zero algebraic markers in its type. Prose after the env states the a-fortiori float-carrier consequence and the scope disclaimer (batching contributes no error of its own; this does not claim float arithmetic is exact), plus the explicit non-goals paragraph (IEEE-754/float-bound work stays open, `thm:chain-bound` cited as the template for that bound's shape). |
| dec/enc/Z suite + tilt lemma + mass preservation + pull-out theorem + normalizer corollaries | proved (C3-B7: `def:dec-enc-mass`/`lem:pure-maps`/`lem:tensor`/`lem:units`/`lem:strengths` all `\leanok` in `NeSyCat/StatisticalLayer/BridgesNormalization/DecEncMass.lean`. Throughout, a `Tmon X`-value is realized as `LogTens X = MS LogS X` (`lem:log-iso`), reusing `ofLogTens`/`toLogTens`/`dstL` directly rather than re-deriving exp/log analysis: `Z` is `(ofLogTens a).sum (fun _ w => w)` (`Dist`'s own mass-sum pattern); `dec` scales `ofLogTens a` by `(Z a)⁻¹` and lands in the full mass carrier `Tens X`, not the mass-one subtype (disclosed scope note: the all-`-∞`/zero-mass log-vector has no mass-one softmax, `0/0=0` convention); `enc` is `toLogTens ∘ Subtype.val` on `Dist X`. `pure_maps`'s `\Tmon(h)`/`\Dmon(h)` are `Finsupp.mapDomain h` at the log/mass carriers respectively (the fiber-sum argument is `Finsupp.sum_mapDomain_index` against a hand-derived additivity of `logEquiv.symm`); `tensor`'s `⊗` is the PRE-EXISTING `NeSyCat.dstL` (`SemiringMonad.lean`) specialized to `S = LogS`, whose `dstL_apply` together with `logS_mul_eq_logMul`/`logMul_coe_coe` already gives the `a_x+b_y` pairing formula for free — new companion lemmas `ofLogTens_dstL`/`toLogTens_dstL`/`dstL_sum_mul`/`ret_sum_one`/`bind_sum_eq` supply the mass-multiplicativity and decode-commutation. `strengths` generalizes the blueprint's `m`-ary, slot-`j` insertion to a three-factor reduction `strength bkg a aft := (Ret(bkg) ⊗ a) ⊗ Ret(aft)` (`bkg : B`, `aft : A` standing for the pure coordinates before/after the effectful slot; every concrete `m,j` instantiates `B`/`A` as products of the omitted coordinates) — the blueprint's own statement was tightened to this proven form per the absolutely-lean work-loop step. Zero `sorry`; axiom-audited (`propext`/`Classical.choice`/`Quot.sound` only) on all four theorems. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 89 environments unchanged — no new envs, only marks — kind-check 73 -> 78, the five newly-cited names, census 452 scanned/78 cited/374 internal/0 unclassified, registry sync 9, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes). C3-B8: `lem:tilt`/`def:mass-preserving`/`lem:mass-preserving-closure`/`thm:pullout` all `\leanok` in NEW `NeSyCat/StatisticalLayer/BridgesNormalization/Tilt.lean`. `tilt` is introduced inline inside `lem:tilt`'s own displayed equation (no separate `definition` env, matching the document), realized as the companion cluster `reweight`/`tiltMass`/`tilt` (`@[blueprint_internal]`); the cited principal `tilt_bind` carries the blueprint's own positivity hypothesis in its signature for exact statement fidelity, but is proved by an UNCONDITIONAL internal lemma `tilt_bind'` that needs no such hypothesis — the ambient `0⁻¹ = 0` convention `dec`/`tilt` already share makes a zero-mass continuation `k(x)` contribute exactly `0` on both sides of the identity, verified both abstractly (a `by_cases Z(k(x))` split collapses cleanly either way) and against a concrete non-mass-preserving `k` by hand before writing; the hypothesis is disclosed as unused, not silently dropped from the statement. `MassPreserving k := ∃ c, ∀ x, Z(k x) = c` (`def:mass-preserving`). `mass_preserving_closure` bundles the six clauses (pure maps via `Z_ret`, units, strengths via `strengths`' own mass clause, Kleisli composition via new `Z_bind_of_forall_const`, `⊗` via `Z_dstL`, and precomposition with a pure reindexing arrow) into one `∧`-conjunction theorem, the bijection law's single cited name. `thm:pullout`'s point-free chain `Φ = L ⨟ B_1 ⨟ ⋯ ⨟ B_r` is realized as a NEW inductive family `PulloutChain` (fixed at `Type`, not `Type*`, after a universe-polymorphism failure with per-constructor `Type*` binders — disclosed, harmless here since every concrete instantiation is an ordinary `Type 0` type): `base` (the leaf tensor `L`), `pureMap` (`\Tmon(h)`, `Finsupp.mapDomain`), `unitIns`/`strengthStep` (a unit/general-leaf tensor insertion via `dstL`, both realizing `lem:tensor` directly — `unitIns` is exactly the special case `strengthStep` at a `\Ret_\Tmon` leaf, disclosed as a deliberate simplification of `lem:strengths`' own 3-part slot-insertion formula, itself built from the same `dstL` two-factor pairing), and `bindStep`; `toTmon`/`toDmon`/`AllMassPreserving` read the chain in `Tmon`/`Dmon` and collect the per-bind mass-preservation hypothesis, and `pullout` proves `dec ∘ toTmon = toDmon` by structural induction on the chain (the blueprint's own "induction on `r`"), the bind case via a new internal corollary `dec_bind_of_massPreserving` built from `tilt_bind'` plus a `tilt`-at-constant-weight-is-identity lemma (`tilt_const_dec`). Two attempts were not needed: the capstone landed on the first full pass once `tilt_bind'`'s unconditional route was found. DISCLOSED judgment call: `thm:pullout`'s own statement and proof also carry a second clause ("if some `k_i` is not mass preserving, the two sides differ in general, and Lemma tilt gives the exact discrepancy") that this ticket's Lean proof does not independently establish (no formalized "tilt-failure example" witness exists yet, that illustrative example living in the not-yet-formalized §Examples); both are marked `\leanok` on the reading that this clause is citation-backed by the already-`\leanok` `lem:tilt` (which literally computes the general, non-identity `tilt` formula this clause refers to) rather than an independent unproven existential claim — flagged here for LEAD/verifier adjudication rather than silently assumed. `thm:chain-bound` (OPEN, "How wrong can it get") untouched, per the open-theorem convention. Two micro-riders landed in the same section: "Every other coordinate of `Tmon X`" -> "Every other value of `Tmon X`" (`def:dec-enc-mass`'s scope disclosure), and the "`0/0=0`" phrase corrected to name the actual Lean convention ("the inverse of `0` is `0`, so `dec` is there the zero function"). Zero `sorry`; axiom-audited (`propext`/`Classical.choice`/`Quot.sound` only) on `tilt_bind`/`mass_preserving_closure`/`pullout`. Gates: `scripts/check.sh` GREEN, `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 89 environments unchanged — no new envs, only marks — kind-check 78 -> 82, the four newly-cited names, census 479 scanned/82 cited/397 internal/0 unclassified — the 27 new scanned declarations are the 4 cited names plus 23 `@[blueprint_internal]` companions/byproducts, including the `PulloutChain.ctorElimType`/`brecOn.go`/`brecOn.eq` compiler byproducts post-hoc tagged via `attribute [blueprint_internal] ...`, matching the `Tm`/`Fm` precedent in `Grammar.lean` — registry sync 9, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes). C3-B9: `def:normalizer`/`lem:normalizer-props`/`lem:normalized-heads` all `\leanok` in NEW `NeSyCat/StatisticalLayer/BridgesNormalization/Normalizer.lean`. `nrm := dec ⨟ enc` realized as `toLogTens ∘ dec` rather than literally `enc ∘ dec` (`enc`'s domain is the mass-one subtype `Dist X`, and `dec(a)` is not proof-carrying mass-one; `enc` itself is exactly `toLogTens ∘ Subtype.val`, so applying `toLogTens` directly is the same construction generalized to non-mass-one inputs), total at the degenerate `a = 0` (`Z(a)=0`) input too (`nrm(0) = 0`). `normalizer_props` bundles all four numbered clauses into the bijection law's single cited name: (i) `dec ∘ nrm = dec` and (iii)/(iv) (shift-invariance/idempotence) hold UNCONDITIONALLY; (ii) (`Z(nrm(a))=1`, mass one) genuinely needs `Z(a) ≠ 0` — the same degenerate-input edge case `dec`'s own mass-one property already carries (`dec_total_mass_eq_one`, C3-B8), stated as a hypothesis on that one clause (`Z a ≠ 0 → Z(nrm a) = 1`) rather than silently claimed unconditionally; DISCLOSED for LEAD/verifier adjudication, content.tex's own item (ii) wording untouched per this ticket's WRITE SET (marks only). "`a+c\cdot\mathbf1`" (introduced inline inside the lemma's own displayed clause, no separate `definition` env, the `lem:tilt`/`tilt` precedent) is realized as the `@[blueprint_internal]` companion `shift`, scaling the mass-carrier reading by `Real.exp c`. `lem:normalized-heads`'s "every neural symbol interpretation is post-composed with `nrm`" is realized as `PulloutChain.normalized`, the node-by-node transform of C3-B8's `PulloutChain` replacing every leaf/strength-leaf/bind continuation with its `nrm`-composed form; `normalized_heads` needs a `PulloutChain.AllNondegenerate` hypothesis (`Z ≠ 0` at every RAW bind continuation only — leaves need none, since `dec_nrm` is unconditional and `AllMassPreserving` itself only ever constrains bind nodes) to conclude `dec c.normalized.toTmon = c.toDmon`, combining mass-preservation-after-normalizing (`thm:pullout`) with "no prediction changes" (`lem:normalizer-props`(i), threaded through the chain unconditionally via the new `PulloutChain.normalized_toDmon_eq`). RIDER (LEAD adjudication of the C3-B8 DISCLOSED judgment call): `thm:pullout`'s env body no longer states the non-mass-preserving-case sentence ("if some `k_i` is not mass preserving, the two sides differ in general, and Lemma tilt gives the exact discrepancy") — moved verbatim to plain prose immediately after the env's `proof` env (not literally between `\end{theorem}` and `\begin{proof}`, since the CORRESPONDENCE structural gate hard-requires a theorem-family env be immediately followed by its `proof` env; placed after `\end{proof}` instead, the nearest gate-legal reading of "immediately after the env" for this theorem+proof unit), so `thm:pullout`'s own env now states exactly what `NeSyCat.pullout` proves; no other wording change, `\uses`/labels untouched. Zero `sorry`; axiom-audited (`propext`/`Classical.choice`/`Quot.sound` only) on `normalizer_props`/`normalized_heads`. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 89 environments unchanged — no new envs, only marks — kind-check 82 -> 85, the three newly-cited names `nrm`/`normalizer_props`/`normalized_heads`, kernel-truth OK 85, census 479 scanned/82 cited/397 internal/0 unclassified -> 494/85/409/0, the 15 new scanned declarations are the 3 newly-cited names plus 12 `@[blueprint_internal]` companions/byproducts (`dec_toLogTens`, `dec_nrm`, `expC`, `expC_ne_zero`, `shift`, `ofLogTens_shift`, `Z_shift`, `dec_shift`, `PulloutChain.AllNondegenerate`, `PulloutChain.normalized`, `PulloutChain.normalized_allMassPreserving`, `PulloutChain.normalized_toDmon_eq`) — 0 unclassified, registry sync 9, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes). C3-CB (escalation seat, isolated worktree): `thm:chain-bound` ("How wrong can it get"), the library's standing open problem, RESOLVED — `\leanok` in NEW `NeSyCat/StatisticalLayer/BridgesNormalization/ChainBound.lean` (`NeSyCat.chain_bound`). Proof route R1/R2 of the attack dossier: a division-free multiplicative sandwich `Π m_i · dec(Φ_Tmon)(y) ≤ Π M_i · Φ_Dmon(y)` (and its mirror) by structural induction on `PulloutChain`, needing NO positivity hypotheses at all — the `0⁻¹ = 0` convention collapses every degenerate case (zero-mass prefix, zero denominator, empty carriers); the bind step is a three-estimate bound on the matrix-multiplication form of bind (`bind_apply`/`dec_mul_Z`/`Z_bind`, extended to a common support `Finset`), and the blueprint's log form follows by `Real.log` bridging under the statement's tacit positivity, realized as explicit hypotheses `0 < m_i ≤ M_i` and `t_Dmon(y) > 0` with `t_Tmon(y) > 0` DERIVED from the sandwich, not assumed (disclosed statement-shape realization, not a weakening — the log inequality is meaningless without it). Bounds are attached as `PulloutChain.HasMassBounds : PulloutChain W → List (ℝ≥0 × ℝ≥0) → Prop`, one `(m_i, M_i)` pair per `bindStep`. Equality clause BOTH directions: `⇐` via `allMassPreserving_of_bounds_eq` + `thm:pullout` (both sides `0`, "the identity"); `⇒` (the converse, the genuinely hard half) by forcing every inequality of the sandwich chain tight and extracting termwise equality over the common support (`Finset.sum_eq_sum_iff_of_le`), which pins `Z(k_i) = m_i` AND `Z(k_i) = M_i` simultaneously at a positive-weight witness index per bind and hands the attained equality down the chain (`bind_layer_eq_upper`/`_lower`, `chain_bound_eq_upper`/`_lower`). R3 numeric sanity (two-bind two-point ℚ chains, extreme masses incl. adversarially correlated tilts) was run BEFORE trusting the direction, per the dossier's honesty branch: all five configurations inside the bound, no counterexample. Zero `sorry`; axiom-audited (`propext`/`Classical.choice`/`Quot.sound` only) on `chain_bound`. content.tex: the env gains `\lean{NeSyCat.chain_bound}`/`\leanok` and the Lean statement's hypothesis shape, its `\uses` widened to the real dependency set, the proof body "Open." replaced by the real proof mirror, the "no known proof / standing research target" paragraph replaced by the one-bind-instance note, and the `% OPEN` comment rewritten as a resolution record preserving the old text (moved, not deleted). NOTE for LEAD: FORMALIZE.md's open-theorem convention still names `thm:chain-bound` as its "Current instance" — FORMALIZE.md is outside this ticket's scope rail; needs a one-line LEAD edit (convention stays, no live instance). Gates (all in the C3-CB worktree): `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 89 environments unchanged — no new envs, only marks on the existing theorem — kind-check 85 -> 86 (`chain_bound`), kernel-truth OK 86, census 494/85/409/0 -> 567/86/481/0, the new scanned declarations being `chain_bound` plus its `@[blueprint_internal]` companion cluster (`PulloutChain.HasMassBounds`, `lbProd`/`ubProd` with nil/cons/pos lemmas, `mapDomain_apply_sum`, `sandwich_mul_right`, `eq_of_mul_mul_right_cancel`, `bind_num_eq_sum`/`Z_bind_eq_sum`/`Z_eq_finset_sum`/`bind_dec_eq_sum`, `bind_layer_sandwich`/`bind_layer_eq_upper`/`bind_layer_eq_lower`, `chain_bound_sandwich`/`chain_bound_eq_upper`/`chain_bound_eq_lower`, `log_ratio_sum`, `allMassPreserving_of_bounds_eq`, plus compiler byproducts) — 0 unclassified, structure-mirror 15/0), pdf rebuilt clean (0 overfull hboxes) + web rebuilt. Statistical layer §"Bridges and normalization" (`def:dec-enc-mass` through `lem:normalized-heads`, `thm:chain-bound` now INCLUDED) is fully `\leanok`; the open-theorem convention has no live instance. CLARIFICATION (C3-E12 rider): the C3-CB gate numbers just above are worktree-era, taken from an isolated escalation-seat worktree and cherry-picked into main; the main-line numbers at landing were 98 environments / 95 kind-checked names / census 575 scanned/95 cited/480 internal/0 unclassified / structure-mirror 16/0 (the blind verifier, V-CB, reproduced this three times).) |
| Quantifier nestability + columns; pointwise-eval-kleisli; normalizer erratum (C3-B4b, escalation seat) | partial (C3-B4b: the three amber escalation items each got their strongest honest formalization; NONE of the three envs is `\lean`/`\leanok`-marked, each for a disclosed reason below — an honest amber over a false green, full analysis in `.foreman/scratch/C3-B4b-report.md`. **`lem:quantifier-nestable`, proven at combinator level, env unmarked for two KERNEL-CHECKED reasons the statement as written does not survive.** NEW `NeSyCat/GrammaticalLayer/QuantifierNestable.lean` (all `@[blueprint_internal]`): the env's two hypothesis predicates `Nestable` (`𝓘(Q)_{mn} = (𝓘(Q)_n)^{⊠m} ⨟ 𝓘(Q)_m` against the block-regrouping iso `tensorPowMulIso`) and `SymmetricFamily` (invariance under the generating adjacent transpositions `swapPow`), the classical-point predicate `IsClassicalPoint` (copyable + discardable state), and the full combinator-level machinery — `tensorPow`/`tensorFinHom`/`comulPow` built TAIL-FIRST so every ℕ-recursion is cast-free (`Nat.add`/`Nat.mul` reduce on the second argument; the head-first draft drowned in `eqToHom` transport, disclosed), `tensorPowAddIso`/`tensorPowMulIso`, the split/refinement lemmas `comulPow_add`/`tensorFinHom_add`/`comulPow_mul`/`tensorFinHom_mul`, the classical-point lemmas `insertPoint_comul`/`insertPoint_counit` (insertion of a classical point is a comonoid morphism, via `Comon.tensorObj_comul`/`tensorμ_natural_right`/`tensor_right_unitality`) and `comulPow_insertPoint`, then `simQuant` (the exact `comulN ⨟ tensorFin ⨟ 𝓘(Q)_N` shape of `Fm.sem`'s quantifier clause), `simQuant_peel` (the env's INDUCTIVE STEP: peel one variable's block structure off the lexicographic enumeration, `blockIdx j i = n·j + i` matching `listPt`'s `finProdFinEquiv` head-slow convention), and `simQuant_nest` (the env's full STATEMENT: simultaneous = iterated over a `PointedObj` list of variables, induction with `simQuant_peel` as the step, base `l = 1` definitional — the env's own proof). The two blockers: (1) CLASSICAL-POINT PROVISO — the iterated reading inserts the head variable's state once and then copies the enlarged context, the simultaneous reading inserts a fresh state into each copy; in a CD category a general state is not copyable (e.g. a randomized state: fresh-sample-per-copy ≠ one-sample-copied), so the env is FALSE as stated for non-classical enumerations, and the fix is an erratum-style proviso ("whose enumeration states are copyable and discardable") that is an env-body edit outside this ticket's write set (marks only) — LEAD adjudication requested; (2) `Id`-MARKED QUANTIFIERS — the clause wraps the family in `dstFoldN` built from `StrongCatInterpretation.dst`, and `StrongCatInterpretation` carries strength as bare DATA with no laws, so no `dstFoldN` block coherence is provable at all; only the `○`-marked case (which `simQuant` captures) is provable without new strength-law infrastructure. Disclosed remainder: the syntax-level bridge from `simQuant_nest` to `Fm.sem`'s own clause (the `ctxMerge` two-stage factorization, the head-first `tensorList (List.replicate …)` vs tail-first `tensorPow` coherence iso, and `Fm.sem`'s tactic-elaborated equation lemmas), and the "any ordering" clause (`SymmetricFamily` is defined and proven for the columns, but the strided-regrouping permutation argument that consumes it is not built). **`lem:quantifier-columns-nestable`, fully proven at scalar level, env unmarked pending carrier adjudication.** NEW `NeSyCat/GrammaticalLayer/QuantifierColumns.lean`: `foldFam` (the `n`-ary reduction of a binary operation as tensor-power morphisms in the category of sets, the running interpretations' base), `foldFam_nestable` (nestability from ASSOCIATIVITY + the seed-unit law) and `foldFam_symmetric` (symmetry from COMMUTATIVITY) — the env's own proof sentence, generically — and the bundled `quantifier_columns_nestable` instantiating all six columns: max, Σ, Π on `ℝ≥0` (the mass carrier), min on `unitInterval` (min needs the top element the unbounded mass carrier lacks — the probability carrier supplies it, a DISCLOSED carrier choice), and the log twins on `LogS`, where `lem:log-iso`'s transported `CommSemiring` makes `lse`/`logMul` literally `+`/`*`, so both properties transport — the env's own "along the log isomorphism" argument. Unmarked because the env's "running interpretation families" denote `𝓘(Q)ₙ` data of `def:logical-interpretation` and no concrete `LogInterpretation` witnessing the columns exists in Lean; the families here are their scalar reductions (the level the env's own proof argues at) — LEAD may judge this faithful and mark it, recommendation in the scratch report. **`thm:pointwise-eval-kleisli`, proven at the concrete program-model level, env unmarked.** NEW `NeSyCat/StatisticalLayer/Batching/PointwiseKleisli.lean`: `BatchProgram` (the `PulloutChain` precedent — a feed-forward program model whose constructors `ret`/`sym`/`comp`/`pair`/`node` mirror the clause shapes of `def:kleisli-interpretation`), the two readings `run` (at `M`) and `runB` (at `BmonT B M`, every symbol `lift_M`-embedded and every `n`-ary op applied index by index — the batch-naturality hypothesis embodied structurally), the commutation theorem `BatchProgram.ev_runB` (`ev_i ∘ ⟦·⟧^{Bmon M} = ⟦·⟧^{M}`, structural induction: `thm:pointwise-eval`'s monad-morphism clauses give `ret`/`comp`/`pair`, batch-naturality gives `sym`/`node` — the env's own proof sketch, one clause shape at a time), and `runBatch_apply` (the env's display equation `⟦φ⟧^{Bmon M}(s)(i) = ⟦φ⟧^{M}(s_i)` for a batch `s` of inputs). Unmarked because the env's parenthetical cites `def:kleisli-interpretation` itself, and instantiating the abstract `Fm.sem` at the concrete pair needs a full CD-category instance at `Type` plus a strong-monad-morphism commutation proved by mutual induction over `Fm.sem`'s six tactic-elaborated clauses — genuinely beyond a night ticket (transport-hell scale documented in the scratch report), the exact remainder recorded there. **ERRATUM RIDERS (kernel-confirmed C3-B9 findings, LEAD-ruled document corrections)** landed in `content.tex`: `lem:normalizer-props` clause (ii) now reads "`Z(nrm(a)) = 1` whenever `Z(a) > 0`", and `lem:normalized-heads` gains "provided each head's mass is nowhere zero", each with the adjacent `%` erratum comment. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 89 environments unchanged, kind-check 85 names unchanged — no new marks, kernel-truth OK 85, census 494/85/409/0 -> 542/85/457/0 — the 48 new scanned declarations are all `@[blueprint_internal]` (the three new files' declarations plus the `BatchProgram` inductive byproducts and `@[reassoc]`-generated companions, post-hoc tagged per the `Tm`/`PulloutChain` precedent) — 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes).) **`lem:quantifier-nestable` LANDED GREEN (C3-ADJ, USER RULING).** The user ruled the C3-B4b classicality blocker a FEATURE, not a defect: shared-vs-independent randomness across quantified branches is a semantic axis the framework deliberately distinguishes. `lem:quantifier-nestable`'s statement gained the classical-point hypothesis (matching `PointedObj.classical` exactly) and now reads `\lean{NeSyCat.simQuant_nest}\leanok`, citing the ALREADY-sorry-free `simQuant_nest` (untagged from `@[blueprint_internal]`); a feature-note paragraph after its proof records the axis, with a `%` comment citing `QuantifierNestable.lean`'s analysis and the coin-flip enumeration-state counterexample (kernel-checked twice: C3-B4b's own analysis, and V-B4b's independent repro). The closing "for any ordering of `x⃗`" clause resisted two real attempts to close via `SymmetricFamily` — (1) reducing a two-variable swap to `insertPoint` commutativity plus `simQuant_peel` at both groupings `n·m`/`m·n` lands on a genuine GRID-TRANSPOSE permutation of `Fin(n·m)≃Fin(m·n)` (not the identity in general, e.g. `m=2,n=3`: index 1 transposes to index 2), needing `q`'s invariance under an ARBITRARY permutation, not just `SymmetricFamily`'s one adjacent transposition; (2) building that general invariance from `SymmetricFamily`'s generators via a permutation-morphism combinator (`Equiv.Perm (Fin n) → End(tensorPow X n)` compatible with `tensorFinHom`) has no Mathlib precedent (checked `Mathlib/CategoryTheory/Monoidal/**`, no `Equiv.Perm`-indexed tensor action) and is a second infrastructure piece on the scale of `tensorPowMulIso`/`tensorPowAddIso`, not completable in-ticket — so the clause SPLIT per the bijection/peer-claim precedent (`thm:pointwise-eval` C3-B6/B10): the proved lexicographic claim keeps the `lem:quantifier-nestable` label and marks green, the new env `lem:quantifier-nestable-order` (`\uses{lem:quantifier-nestable}`) carries the "any ordering" claim unmarked, with its own ordinary (non-"Open.") informal proof sketch — a known, believed argument, not yet Lean-formalized. Gates: `scripts/check.sh` GREEN (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure 89 -> 90 environments — the one new `lem:quantifier-nestable-order` split env, kind-check 85 -> 86 names — the one newly cited `NeSyCat.simQuant_nest`, kernel-truth OK 86, census 542/85/457/0 -> 542/86/456/0 — same 542 total scanned, `simQuant_nest` flips internal -> cited, 0 unclassified, registry sync 9 twins, structure-mirror 15/0), pdf+web rebuilt clean (0 overfull hboxes). `.foreman/C3-NS-spec.md` gained a rider on its item 4 (completions): `lem:quantifier-columns-nestable` marks on the [0,∞] completion landing, not before (user ruling — wait for the top; the mixed-carrier proof stays internal machinery until then).) **RIDER (C3-CMP).** `lem:quantifier-columns-nestable` MARKED at the mass completion's landing: `min`'s seed re-pointed from `unitInterval`'s `1` to `ℝ≥0∞`'s `⊤`, landing max/min/Σ/Π on one carrier as the C3-ADJ ruling's condition asked for. |
| Examples (failure numbers, MNIST commute)                                  | partial (C3-EXEC item 3: NEW `def:rational-mass-row`/`thm:rational-mass-row-monad` `\leanok` in NEW `NeSyCat/StatisticalLayer/Examples/RationalMassRow.lean` — `QRow` (a `Fintype`-indexed plain function `X → ℚ≥0`, mirroring `Bmon`'s own plain-function encoding-pin device since Mathlib's `Finsupp` is itself `noncomputable`, independently of the scalar semiring: kernel-verified that instantiating `NeSyCat.ret`/`NeSyCat.bind` at `S := ℚ≥0` does not remove the marker), with `QRow.ret`/`QRow.bind` genuinely `#eval`-executable (no `noncomputable` anywhere in the file) and `QRow_monad_laws` proving the same three laws `thm:semiring-monad-laws` proves for `MS`, via `Finset.sum` rearrangements built from the same three ingredients but assembled differently (C3-EXEC-FIX: the "identical shape" claim was false — `QRow` performs the double-sum interchange in the open, `Finset.sum_comm`, where `MS` gets it packaged inside `Finsupp.sum_sum_index`/`sum_smul_index`/`smul_sum`). A concrete weighted bind chain (`(1/3,2/3,0)` bound through a two-way `ret`-valued continuation) computes to `(1/3, 2/3)` under `#eval`, matching a by-hand check. The two pre-existing narrative examples (Tilt failure numbers, MNIST chains commute) stay illustrative prose with no Lean counterpart, per the three-shape witness doctrine — nothing formal is missing for them.) |

OPEN: chain version of the tilt bound.

Fine-grained per-item status (labels, `\lean`/`\leanok` marks) lives in
`blueprint/src/content.tex`, not in this table.

## Notes

- **C3-EXEC-FIX (closing the V-C3EXEC blind-verification FAIL,
  2026-08-10):** six items, no Lean statement or proof changes (Lean
  edits are comments/docstrings only). (1) THE FALSE STRUCTURAL.
  `scripts/blueprint.sh`'s `CLASSIFY_ALGEBRAIC_MARKERS` deliberately
  excluded `CategoryTheory.*`, so `NeSyCat.simQuant_nest`
  (`lem:quantifier-nestable`) was reported carrier-agnostic although
  its type binds `[MonoidalCategory C] [BraidedCategory C]
  [ComonObj Z]` plus `Nestable q` — monoidal coherence is structure ON
  the carrier, and an implementation whose tensor is not associative on
  the nose does not satisfy it. `CategoryTheory`/`Quiver` are now
  markers, together with the Mathlib algebraic/order vocabulary the
  verifier named (`Monoid`, `CommMonoid`, `AddCommMonoid`, `AddMonoid`,
  `PartialOrder`, `Preorder`, `Mul`, `Add`, `Zero`, `One`) and every
  sibling found by MECHANICALLY enumerating the used-constant heads of
  all 59 cited theorem types (`AddZeroClass`, `MulZeroClass`,
  `DivInvMonoid`, `Distrib`, `Module`, `MulOpposite`, `NonAssocSemiring`
  and the non-unital ring tower, `LE`, `LT`, `SemilatticeInf/Sup`,
  `OrderBot/Top`, `Bot`, `Top`, `Max`, `Min`, `OrderDual`,
  `ZeroLEOneClass`, `Monotone`, `Antitone`, `abs`, `Int`, `NeSyCat.LogSInf`,
  `NeSyCat.DMFullCalculus`, `NeSyCat.Nestable`, `NeSyCat.PointedObj`,
  `NeSyCat.SymmetricFamily`, and the `OfNat`/`H*` operation classes).
  Counts BEFORE 4 structural / 55 arithmetic, AFTER **3 structural / 56
  arithmetic** of 59; exactly one verdict moved (`simQuant_nest`), the
  rest of the enlarged list is drift insurance. The three survivors were
  re-examined one by one against their FULL printed types:
  `batchTransformer`, `ev_isMonadMorphism`, `batch_layer_exact`, no
  algebraic constant anywhere; `ℕ`/`Fin` occur only as batch size and
  index. DISCLOSED, in the script comment and in the rendered document:
  `Monad`/`LawfulMonad` are not markers, so "structural" means "no
  constraint on the VALUE carrier". **ERRATUM (C3-EXEC-FIX2,
  2026-08-10).** This entry recorded all three binder lists as
  `{B : ℕ} {M : Type → Type u} {X Y : Type} [Monad M] [LawfulMonad M]`
  and added that "structural" still presupposes a lawful ambient monad.
  That was FALSE of `ev_isMonadMorphism`, which already carried
  `omit [LawfulMonad M]` and two `rfl`s, and overstated the other two,
  whose only use of a monad law was `pure_bind`. C3-EXEC-FIX2 restates
  all three at their true minimal hypotheses; see its own entry below.
  (2) THE GATE IS NOW A GATE. The section used to end in
  `|| true` and assert nothing; it now recomputes total, per-bucket
  counts, and the sorted structural NAME list (`LC_ALL=C` byte order, so
  the sentinel cannot flip with the caller's locale) and compares them
  against a `% CLASSIFY-SENTINEL:` line in `content.tex`, failing the
  whole gate on any drift or on a missing sentinel. RED-tested by
  perturbing the sentinel to `structural=4 ... ,NeSyCat.simQuant_nest`:
  `BLUEPRINT: RED (exit 1)` with both lines printed; restored, GREEN.
  (3) THE MISSING ARTIFACT (C3-EXEC spec item 2a, never written).
  `content.tex` now STATES the dichotomy where a referee reply can cite
  it: a labelled two-row table plus prose after `thm:batch-exactness`,
  naming the three carrier-agnostic statements, saying that everything
  else (Lemma `lem:quantifier-nestable` included, with its reason) holds
  only insofar as the implementation's arithmetic satisfies the axioms,
  and stating the two things the carrier-agnostic column does NOT say.
  Delivered as table+prose, NOT as a new environment, deliberately: the
  bijection law and the census require each Lean declaration to be cited
  by exactly one env, so a second env citing `batch_layer_exact` would
  be a hard gate violation, and the dichotomy is a classification of
  already-proved statements rather than a new claim. (4) THE AMBIGUOUS
  SENTENCE. "the theorem holds for a float-valued tensor carrier exactly
  as it holds for `\MS S`" had a reading on which the float
  implementation satisfies the monad laws (`\MS S` occupies the INNER
  MONAD slot everywhere else in that section, and that slot carries
  `[LawfulMonad M]`) — the one thing this work must not assert.
  Rewritten so only the value-slot reading survives, with an explicit
  sentence that nothing here proves a floating-point implementation of
  any monad satisfies the monad laws. (5) PROOF SUBSTANCE on the two new
  theorem proofs, which had zero displays and escaped the linter only by
  being under its word threshold. `thm:rational-mass-row-monad` now
  transcribes the actual Lean steps: the two unit laws as indicator
  collapses (`Finset.sum_ite_eq'`/`sum_ite_eq`) and associativity as a
  five-step chain whose crux, the INTERCHANGE of the two summations
  (`Finset.sum_comm`), appeared nowhere on the page before. The
  "identical shape as `thm:semiring-monad-laws`'s proof" claim was FALSE
  as written and is corrected in both places (page and Lean docstring):
  same three ingredients (distributivity, interchange, associativity of
  `⊗`), different assembly — `MS`'s route packages the interchange
  inside `Finsupp.sum_sum_index`/`sum_smul_index`/`smul_sum` over a
  tracked support, `QRow`'s performs it in the open over the whole
  finite carrier. `thm:batch-exactness`'s proof gains the six cited
  clauses as a display, one projection apiece. (6) MINORS: the two
  `RationalMassRow.lean` companion tags now point at the env's principal
  `QRow_monad_laws` (they said `QRow.bind_assoc`); `BatchTransformer.lean`
  said "`X Y : Type*`" where the binders are `Type` (the inner monad is
  taken at `Type → Type*`), and `content.tex` said "every type X" for
  the same universe-0-only statement, both corrected to what is true;
  `def:rational-mass-row`/`thm:rational-mass-row-monad` now state the
  `[DecidableEq X]` the computability rests on (and what each hypothesis
  buys); "every field is a pair of integers" (read as the algebraic
  *field*, and the denominator is a `ℕ`) is now "every element is
  carried by a fraction in lowest terms, an integer numerator over a
  nonzero natural-number denominator". Gates: `scripts/check.sh` GREEN,
  `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN (structure
  119 environments UNCHANGED — item 3 adds no env by design — kind-check
  117 names, kernel-truth OK, census 653 scanned/117 cited/536
  internal/0 unclassified, classification 4/55 -> 3/56 with the sentinel
  now asserted, registry sync 9, structure-mirror 17/0), pdf+web
  rebuilt, 0 overfull hboxes (the table's `p`-columns carry a
  cell-local `\raggedright` so they add no underfull ones either),
  `lint-blueprint.py` silent.

- **C3-EXEC-FIX2 (the batch layer restated at its true minimal
  hypotheses, 2026-08-10):** four items. (1) THE FALSE HYPOTHESIS LIST.
  C3-EXEC-FIX's dichotomy prose asserted "Lawfulness is a hypothesis of
  all three statements". It was not a hypothesis of `ev_isMonadMorphism`
  at all (`omit [LawfulMonad M]`, both clauses `rfl`), and for the other
  two the only monad law consumed was `pure_bind`, the LEFT UNIT law,
  never `bind_assoc`. (2) STATEMENT WORK (hypothesis weakening,
  authorized in-ticket because it strengthens the theorems; every
  conclusion is byte-identical to its predecessor). `[LawfulMonad M]` is
  dropped from `batchTransformer`, `batch_layer_exact`, and
  `liftBmon_bind`; each now carries the one law it actually uses as an
  explicit hypothesis, at exactly the two value types it is applied at,
  `hleft : ∀ (x : X) (g : X → M Y), (pure x : M X) >>= g = g x`.
  `ev_isMonadMorphism` needed no change (already lawfulness-free).
  Three new `@[blueprint_internal]` companions:
  `batch_layer_exact_lawFree` (the FIVE clauses that need no monad law
  whatever, under `[Monad M]` alone, proof
  `⟨liftM_ret, liftM_bind, liftBmon_ret, (ev_isMonadMorphism i).1,
  (ev_isMonadMorphism i).2⟩`, every component an `rfl`), and
  `batchTransformer_of_lawful`/`batch_layer_exact_of_lawful`, which
  restate the pre-fix statements VERBATIM under `[LawfulMonad M]` and
  prove them by discharging `hleft` with `pure_bind` — a machine-checked
  witness that each new statement implies the one it replaces. (3) THE
  PROSE, rewritten so the citable artifact stands alone:
  `thm:batch-transformer` now opens "Let `M` be a monad, not assumed
  lawful" and its proof exhibits the one clause that consumes a law as a
  two-line display evaluated at an index; `thm:pointwise-eval` states
  that no monad law is assumed; `thm:batch-exactness` states the left
  unit law as its only assumption on `M` and records that five of six
  clauses need not even that; the dichotomy table's carrier-agnostic row
  and the paragraphs around it name the left unit law, and name
  ASSOCIATIVITY as the law floating-point arithmetic breaks and the
  batch layer never invokes (`bind_assoc` for `MS S` rests on
  `Finsupp.sum_sum_index`/`add_smul`, i.e. on `⊕`'s associativity and
  `⊗`'s distributivity; `ret_bind` rests on `one_smul` alone —
  `SemiringMonad.lean`). What is NOT claimed, in either place: that a
  floating-point implementation satisfies the left unit law or any other
  monad law. (4) FORMALIZE.md's scope rail updated to match
  `.claude/hooks/guard-scope.py`, which removed `FORMALIZE.md`,
  `scripts/`, `references/`, and `.claude/` from protection on
  2026-08-09; the rail now lists what IS still protected
  (`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.github/`,
  `.foreman/`, `.gitignore`) and records that `scripts/` edits are
  ticket-scoped rather than forbidden. Gates: `scripts/check.sh` GREEN
  (whole project), `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh`
  GREEN (structure 119 environments unchanged, kind-check 117 names
  unchanged, kernel-truth OK, census 653/117/536/0 -> 656/117/539/0 —
  the 3 new scanned declarations are exactly the 3 new
  `@[blueprint_internal]` companions above — 0 unclassified,
  classification sentinel OK and UNCHANGED at
  `total=59 structural=3 arithmetic=56` with the same three names, since
  `Monad`/`LawfulMonad` were never markers and dropping one changes no
  verdict, registry sync 9, structure-mirror 17/0), pdf+web rebuilt,
  0 overfull hboxes, `lint-blueprint.py` silent. KNOWN STALE, outside
  this ticket's write set: `scripts/blueprint.sh`'s marker-list comment
  still says a structural verdict "PRESUPPOSES the ambient monad is
  lawful", which is no longer true of the three statements it describes.

- **C3-E13-FIX (display-fidelity fixes + audit of the sweep campaign's
  displays, 2026-08-10):** `blueprint/src/content.tex` only, no Lean
  changes. Four verifier-confirmed defects fixed. (1) BLOCKING,
  `thm:three-layers`' units-vs-bounds negative witness: the display
  claimed `\bot = (\top_\MassS, \bot_\MassS)` "tested against
  `v = (2,0)`", an object that cannot be FORMED — `orderBot` needs
  `[BoundedOrder S]` (`Lifted.lean`) and `ℝ≥0` has no top, which is
  exactly why `not_isBot_orderedTwoSlot_ret_zero` states `¬ IsBot`
  rather than `≠ ⊥` — and read literally its test came out TRUE,
  contradicting the conclusion drawn from it. Rewritten to state the
  Lean lemma: `\Ret(0) = (1,0)`, leastness would put it below
  `v = (2,0)`, and the order family's two clauses give `0 \le 0` and
  `1 \ge 2`, the slot-`0` clause false. (2) `lem:tilt`'s degenerate
  branch mis-attributed the vanishing of `a`'s weights to the
  `0^{-1}=0` convention; in `tilt_bind'` that step is
  `ofLogTens_eq_zero_of_Z_eq_zero`, whose mechanism is
  `Finset.sum_eq_zero_iff_of_nonneg` (NONNEGATIVITY), with
  `\dec(a) = 0` following by `smul_zero`. The convention's genuine use
  is one step later, at `\dec(a \bind k)`, now named there explicitly.
  (3) `thm:chain-bound-sandwich`: dropped the unused `lem:strengths`
  `\uses` entry (`ChainBound.lean`'s `strengthStep` branch closes by
  `dec_dstL` + `sandwich_mul_right`, i.e. `lem:tensor` alone — the same
  entry removed from `thm:pullout` in C3-E13), and introduced `L,U`
  in the proof's opening paragraph, before the two steps that used
  them. (4) STATEMENT TEXT (authorized, cross-reference only):
  `thm:pullout`'s "a strength factor (Lemma~\ref{lem:strengths})" ->
  "(Lemma~\ref{lem:tensor})", matching both its own proof and the Lean
  (`pullout`'s `strengthStep` branch is `rw [dec_dstL, ih hm]`, with
  no `dec_ret`). AUDIT of the campaign's other swept displays
  (`thm:pullout`, `thm:chain-lin`, `thm:square-not-lin`,
  `thm:semiring-monad-laws`, `thm:batch-transformer`,
  `thm:embedding-exact`, `lem:support-hom-iff`,
  `thm:semiring-monad-commutative`, `thm:chain-bound-sandwich`,
  `thm:chain-bound`), each re-derived from its Lean by transcription:
  one further gap fixed (`thm:pullout`'s bind case asserted that a
  constant tilt weight leaves `\tilt` the identity, true only for a
  NONZERO constant — `tilt_const_dec` carries `c \ne 0`, and
  `dec_bind_of_massPreserving` splits `by_cases c = 0` with the zero
  branch collapsing through `bind_zero_cont`; the branch is now shown),
  one arguable divergence reported and NOT edited
  (`thm:embedding-exact`'s chaining display associates as
  `R(E^\top(Ev))` where the Lean groups matrices first,
  `mulVec_mulVec` then `mul_assoc` — same identity, different
  bracketing). Gates: `scripts/check.sh` GREEN,
  `scripts/sorry-report.sh` 0/0, `scripts/blueprint.sh` GREEN with
  sentinels UNCHANGED (106 envs / 103 kind-checked names / census
  614/103/511/0 / registry 9 / structure-mirror 16/0), pdf+web
  rebuilt with 0 `Overfull \hbox`, `lint-blueprint.py` silent.
  ENVIRONMENT NOTE: the structure-mirror gate first came up RED on an
  orphan `NeSyCat/LogicalLayer/Completions/` folder — empty, untracked,
  created outside this ticket; removed with `rmdir` (git tracks no
  empty directory, so nothing was lost) to restore the 16/0 sentinel.

- **C2-E11 (dep-graph proved-status collapse for definition-like kinds,
  2026-08-10):** web-only, no `.tex` content or Lean touched. Symptom:
  `class`/`abbreviation` envs never got a background fill on `\leanok`
  (border only), so every theorem/lemma depending on one was denied
  the dark-green fully-proved fill even once genuinely formalized.
  Traced the cause in the venv's
  `leanblueprint/Packages/blueprint.py:make_lean_data` (postParse-150):
  a node's `proved` flag comes only from `proof =
  node.userdata.get('proved_by')` (set by a separate `\proof` env via
  `\proves`) — `class`/`abbreviation` never carry one (nothing is
  asserted separately from the declaration), so `proved` stayed
  hardwired `False` forever, and `fully_proved`'s ancestor scan
  (`all(n.userdata.get('proved', False) or item_kind(n) ==
  'definition' for n in ...)`) auto-passes only `definition`-kind
  ancestors, never `class`/`abbreviation`. Doctrine (LEAD-ruled): for
  definition-like kinds the statement/proof distinction collapses —
  kernel acceptance IS the discharge, so `\leanok ⇒ proved`; `instance`
  stays two-event (real proof obligations) and is untouched. Extended
  `blueprint/src/nesycatshapes.py` (the E9 local plastex package) with
  a postParse-160 callback (after leanblueprint's own postParse-150
  `make_lean_data`, confirmed via `plasTeX/TeX.py`'s ascending-order
  callback dispatch) that patches `node.userdata['proved'] =
  bool(leanok)` for `class`/`abbreviation` nodes only, then re-runs
  `fully_proved`'s own ancestor-scan formula VERBATIM (not forked) so
  the correction propagates to dependents — leanblueprint's own
  unmodified `fillcolorizer`/`colorizer` then do the right thing with
  no override needed at all. Mirrored byte-identical into
  `plugin/nesycat-lean4-harness/blueprint-scaffold/nesycatshapes.py`.
  Verified with a stashed-vs-fixed before/after rebuild of
  `dep_graph_document.html`'s dot: BEFORE, `def:lin-blat2mon` (a class)
  was `[color=green, label="lin-blat2mon", shape=box]` (no fill) and
  its dependent `thm:chain-lin` was capped at the medium-green
  `proved` fill (`fillcolor="#9CEC8B"`, not fully-proved); AFTER, both
  are `fillcolor="#1CAC78"` (dark green, `style=filled`) — the
  fully-proved fill now propagates through a leanok'd class exactly as
  it already did through a leanok'd definition. `def:bounded-comm-
  lattice-semiring` (the ticket's own class example) went from
  border-only to `fillcolor="#1CAC78"` too. `inst:massS-latcsrng`
  (instance) is byte-identical before and after
  (`[color=green, label="massS-latcsrng", shape=ellipse]`, no fill,
  since instance envs carry no separate `\proof` in this blueprint's
  convention and were never touched by the patch) — (c) confirmed
  unchanged. Legend wording (extended by E9) already reads truthfully
  for the new fills ("Green/Dark green background — the proof of this
  result [and all its ancestors] is formalized") and needed no
  further edit. `thm:semiring-monad-laws`, the ticket's other named
  example, turned out on inspection to have no class in its ancestor
  chain at all (`def:semiring-monad` plus two already-proved lemmas)
  — it was already dark-green before this ticket; `thm:chain-lin` (the
  ticket's own alternative) is the one genuinely gated by a class
  ancestor and is used above as the primary evidence instead.
  Worktree-only environment note: this worktree's nested location
  under `.claude/worktrees/` breaks `blueprint/src/macros/common.tex`'s
  hardcoded `\input{../../../NeSyCat.Logics/macros.sty}` (three levels
  up lands in `.claude/worktrees/`, not the sibling-repo parent);
  worked around with an untracked symlink
  `.claude/worktrees/NeSyCat.Logics -> .../NeSyCat/NeSyCat.Logics`
  placed OUTSIDE this worktree's own git tree (sibling of the worktree
  dir itself), not a repo change and not part of this commit. Gates:
  `scripts/check.sh`-equivalent `lake build` clean (8697 jobs, only
  pre-existing `checkUnivs` linter warnings in `Signatures.lean`,
  untouched by this ticket), `scripts/blueprint.sh` GREEN twice in a
  row with every sentinel unchanged (structure 89 environments/85
  names kind-checked, kernel-truth OK 85, census 542/85/457/0,
  registry sync 9 twins, structure-mirror 15/0) — unaffected by
  construction, since `nesycatshapes.py` is `\usepackage`'d only by
  `web.tex` (confirmed by grep) while structure/kind-check/census read
  `content.tex`/Lean directly, and pdf/web both rebuilt clean (print
  build untouched: `nesycatshapes` is never loaded by `print.tex`).

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
