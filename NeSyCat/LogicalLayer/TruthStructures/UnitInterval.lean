/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.LogicalLayer.TruthStructures.BLat2Mon
import NeSyCat.LogicalLayer.TruthStructures.Chain

/-!
# The probability row: `unitInterval` as a `LinBLat2CMon` with DM structure

Blueprint item `lem:unit-interval-truth-structure` (`blueprint/src/content.tex`,
§"Truth-value structures", `[NeSy26, App. A]`): `unitInterval` (Mathlib's
`Set.Icc (0:ℝ) 1`), with `otimes := (· * ·)`, `done := 1`, `oplus` the
`unitInterval.symm`-conjugate of multiplication, `dzero := 0`, is a
`LinBLat2CMon` with `DMStructure` (`dneg := unitInterval.symm`) and
`UnitBounds`.

**The pinned definition of `oplus`.** `oplus p q := σ (σ p * σ q)` (`σ` is
`unitInterval.symm`, `σ p = 1 - p`), *not* the blueprint's own display
formula `p + q - p*q`. The latter is recovered as a coercion lemma
(`coe_oplus`), not baked into the definition: monoid laws for `oplus`
(associativity, unit) transport from `*`'s along the involution `σ` for
free (`σσ` cancels in the middle of `oplus (oplus p q) r`; the unit
`σ 0 = 1` gives `oplus` its right unit `0` directly), and the closure
`p + q - pq ∈ [0,1]` is discharged automatically by working in the
subtype throughout, rather than needing a separate membership argument on
the real-number formula.

**Routing through `thm:chain-lin`.** The `LinBLat2Mon unitInterval`
instance is built via `LinBLat2Mon.ofChain` (`NeSyCat/LogicalLayer/TruthStructures/Chain.lean`),
not by proving the eight linear laws directly — this is the blueprint's
own proof of this item ("Theorem~`thm:chain-lin` applies"), and exercises
the instance-diamond wrinkle noted there: Lean resolves `Lattice
unitInterval` to `Set.Icc.lattice` (built from `Real.lattice`), a
different instance path than `LinearOrder.toLattice`, but the two are
definitionally equal on this carrier, so `ofChain` applies with no
manual `letI` bridging.
-/

namespace NeSyCat

namespace unitInterval

open BLat2Mon _root_.unitInterval

/-- Blueprint `lem:unit-interval-truth-structure` (`BLat2Mon unitInterval`):
`otimes := (· * ·)` (real multiplication, restricted to the subtype), `done :=
1`, `oplus p q := σ (σ p * σ q)` (the pinned `σ`-conjugate of multiplication,
`σ` Mathlib's `unitInterval.symm`), `dzero := 0`. Associativity and unit laws
for `otimes` are inherited from `Icc.instMonoidWithZero`'s multiplication
(`mul_assoc`/`one_mul`/`mul_one`); for `oplus` they transport along `σ`: `σσ`
cancels in the associativity chain, and `σ 0 = 1` gives the right unit,
`σ 1 = 0` mirrored on the left (`dzero_oplus`/`oplus_dzero`, from
`symm_symm`/`symm_zero`/`symm_one`). -/
-- blueprint: internal (A1 bijection-law companion of
-- `unitInterval.coe_oplus`, content.tex lem:unit-interval-truth-structure)
noncomputable instance instBLat2Mon : BLat2Mon (_root_.unitInterval) where
  oplus p q := σ (σ p * σ q)
  dzero := 0
  otimes p q := p * q
  done := 1
  oplus_assoc p q r := by simp [mul_assoc]
  dzero_oplus p := by simp
  oplus_dzero p := by simp
  otimes_assoc p q r := mul_assoc p q r
  done_otimes p := one_mul p
  otimes_done p := mul_one p

/-- Blueprint `lem:unit-interval-truth-structure` (`BLat2CMon unitInterval`):
both monoids are commutative — `otimes` since real multiplication is, `oplus`
since its `σ`-conjugated multiplication is (`mul_comm` transports through
`σ`). -/
-- blueprint: internal (A1 bijection-law companion of
-- `unitInterval.coe_oplus`, content.tex lem:unit-interval-truth-structure)
noncomputable instance instBLat2CMon : BLat2CMon (_root_.unitInterval) where
  __ := instBLat2Mon
  oplus_comm p q := by
    have key1 : (oplus p q : _root_.unitInterval) = σ (σ p * σ q) := rfl
    have key2 : (oplus q p : _root_.unitInterval) = σ (σ q * σ p) := rfl
    rw [key1, key2, mul_comm]
  otimes_comm p q := mul_comm p q

/-- Blueprint `lem:unit-interval-truth-structure` (`ZeroBot unitInterval`):
`dzero = 0 = ⊥` by construction (`Set.Icc`'s `⊥` and `0` coincide, both the
left endpoint). -/
-- blueprint: internal (A1 bijection-law companion of
-- `unitInterval.coe_oplus`, content.tex lem:unit-interval-truth-structure)
instance instZeroBot : ZeroBot (_root_.unitInterval) where
  dzero_eq_bot := rfl

/-- Blueprint `lem:unit-interval-truth-structure` (`OneTop unitInterval`):
`done = 1 = ⊤` by construction (`Set.Icc`'s `⊤` and `1` coincide, both the
right endpoint). -/
-- blueprint: internal (A1 bijection-law companion of
-- `unitInterval.coe_oplus`, content.tex lem:unit-interval-truth-structure)
instance instOneTop : OneTop (_root_.unitInterval) where
  done_eq_top := rfl

/-- Blueprint `lem:unit-interval-truth-structure` (`UnitBounds unitInterval`):
the packaged `ZeroBot`/`OneTop` conjunction (Definition `def:unit-bounds`). -/
-- blueprint: internal (A1 bijection-law companion of
-- `unitInterval.coe_oplus`, content.tex lem:unit-interval-truth-structure)
instance instUnitBounds : UnitBounds (_root_.unitInterval) where

/-- Blueprint `lem:unit-interval-truth-structure` (monotonicity of `otimes`,
right argument): `p ≤ q → r * p ≤ r * q`, `mul_le_mul_of_nonneg_left` on the
real coercions. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
private theorem otimes_mono_left {p q : _root_.unitInterval} (h : p ≤ q)
    (r : _root_.unitInterval) : otimes r p ≤ otimes r q :=
  mul_le_mul_of_nonneg_left h r.2.1

/-- Blueprint `lem:unit-interval-truth-structure` (monotonicity of `otimes`,
left argument): dually, `p ≤ q → p * r ≤ q * r`. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
private theorem otimes_mono_right {p q : _root_.unitInterval} (h : p ≤ q)
    (r : _root_.unitInterval) : otimes p r ≤ otimes q r :=
  mul_le_mul_of_nonneg_right h r.2.1

/-- Blueprint `lem:unit-interval-truth-structure` (monotonicity of `oplus`,
right argument): `σ` is antitone (`symm_le_symm`), so `p ≤ q` gives
`σ q ≤ σ p`, hence `σ r * σ q ≤ σ r * σ p` (monotone multiplication by a
nonnegative factor), hence `σ(σ r * σ p) ≤ σ(σ r * σ q)` (antitone `σ`
again). -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
private theorem oplus_mono_left {p q : _root_.unitInterval} (h : p ≤ q)
    (r : _root_.unitInterval) : oplus r p ≤ oplus r q := by
  have key1 : (oplus r p : _root_.unitInterval) = σ (σ r * σ p) := rfl
  have key2 : (oplus r q : _root_.unitInterval) = σ (σ r * σ q) := rfl
  rw [key1, key2]
  exact symm_le_symm.mpr (mul_le_mul_of_nonneg_left (symm_le_symm.mpr h) (σ r).2.1)

/-- Blueprint `lem:unit-interval-truth-structure` (monotonicity of `oplus`,
left argument): dual to `oplus_mono_left`. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
private theorem oplus_mono_right {p q : _root_.unitInterval} (h : p ≤ q)
    (r : _root_.unitInterval) : oplus p r ≤ oplus q r := by
  have key1 : (oplus p r : _root_.unitInterval) = σ (σ p * σ r) := rfl
  have key2 : (oplus q r : _root_.unitInterval) = σ (σ q * σ r) := rfl
  rw [key1, key2]
  exact symm_le_symm.mpr (mul_le_mul_of_nonneg_right (symm_le_symm.mpr h) (σ r).2.1)

/-- Blueprint `lem:unit-interval-truth-structure` (`LinBLat2Mon unitInterval`,
"Theorem `thm:chain-lin` applies"): assembled via `LinBLat2Mon.ofChain` from
`unitInterval`'s `LinearOrder`, the `otimes`/`oplus` monotonicity above, and
`UnitBounds` — the point of this row: it exercises `thm:chain-lin` rather
than proving the eight linear laws by hand. -/
-- blueprint: internal (A1 bijection-law companion of
-- `unitInterval.coe_oplus`, content.tex lem:unit-interval-truth-structure)
noncomputable instance instLinBLat2Mon : LinBLat2Mon (_root_.unitInterval) :=
  LinBLat2Mon.ofChain otimes_mono_left otimes_mono_right oplus_mono_left oplus_mono_right

/-- Blueprint `lem:unit-interval-truth-structure` (`LinBLat2CMon
unitInterval`): the commutative linear structure, combining
`instLinBLat2Mon` and `instBLat2CMon`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `unitInterval.coe_oplus`, content.tex lem:unit-interval-truth-structure)
noncomputable instance instLinBLat2CMon : LinBLat2CMon (_root_.unitInterval) where
  __ := instLinBLat2Mon
  __ := instBLat2CMon

/-- Blueprint `lem:unit-interval-truth-structure` (`DMStructure unitInterval`):
`dneg := σ` (`unitInterval.symm`, `σ p = 1 - p`) is involutive
(`symm_symm`), antitone (`symm_le_symm`), and satisfies the De Morgan law
`σ(p * q) = oplus (σ q) (σ p)` — near-definitional: `oplus (σ q) (σ p) = σ(σσq
* σσp) = σ(q * p) = σ(p * q)`, the `σσ` cancelling by `symm_symm` and the
remaining equality by commutativity of `*`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `unitInterval.coe_oplus`, content.tex lem:unit-interval-truth-structure)
noncomputable instance instDMStructure : DMStructure (_root_.unitInterval) where
  dneg := σ
  dneg_dneg := symm_symm
  dneg_antitone p q h := symm_le_symm.mpr h
  dneg_otimes p q := by
    have key1 : (otimes p q : _root_.unitInterval) = p * q := rfl
    have key2 : (oplus (σ q) (σ p) : _root_.unitInterval) = σ (σ (σ q) * σ (σ p)) := rfl
    rw [key1, key2, symm_symm, symm_symm, mul_comm]

/-- Blueprint `lem:unit-interval-truth-structure` (closure/readout formula):
the blueprint's display formula `p + q - p*q` for `oplus`, recovered as a
coercion lemma from the pinned `σ`-conjugate definition (`1 - (1-p)(1-q) =
p + q - pq`); membership in `[0,1]` needs no separate closure argument since
`oplus p q` is already an element of the subtype by construction. -/
theorem coe_oplus (p q : _root_.unitInterval) :
    (↑(oplus p q) : ℝ) = ↑p + ↑q - ↑p * ↑q := by
  have key : (oplus p q : _root_.unitInterval) = σ (σ p * σ q) := rfl
  rw [key]
  push_cast [coe_symm_eq]
  ring

end unitInterval

end NeSyCat
