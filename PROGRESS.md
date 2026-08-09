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
| Batch monad + transformer + pointwise evaluation                           | not-started |
| dec/enc/Z suite + tilt lemma + mass preservation + pull-out theorem + normalizer corollaries | not-started |
| Examples (failure numbers, MNIST commute)                                  | not-started |

OPEN: chain version of the tilt bound.

Fine-grained per-item status (labels, `\lean`/`\leanok` marks) lives in
`blueprint/src/content.tex`, not in this table.

## Notes

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
