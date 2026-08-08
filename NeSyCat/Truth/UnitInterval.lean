/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.Truth.BLat2Mon
import NeSyCat.Truth.Chain

/-!
# The probability row: `unitInterval` as a `LinBLat2CMon` with DM structure

Blueprint item `lem:unit-interval-truth-structure` (`blueprint/src/content.tex`,
§"Truth-value structures", `[NeSy26, App. A]`): `unitInterval` (Mathlib's
`Set.Icc (0:ℝ) 1`), with `andC := (· * ·)`, `done := 1`, `parr` the
`unitInterval.symm`-conjugate of multiplication, `dzero := 0`, is a
`LinBLat2CMon` with `DMStructure` (`dneg := unitInterval.symm`) and
`UnitBounds`.

**The pinned definition of `parr`.** `parr p q := σ (σ p * σ q)` (`σ` is
`unitInterval.symm`, `σ p = 1 - p`), *not* the blueprint's own display
formula `p + q - p*q`. The latter is recovered as a coercion lemma
(`coe_parr`), not baked into the definition: monoid laws for `parr`
(associativity, unit) transport from `*`'s along the involution `σ` for
free (`σσ` cancels in the middle of `parr (parr p q) r`; the unit
`σ 0 = 1` gives `parr` its right unit `0` directly), and the closure
`p + q - pq ∈ [0,1]` is discharged automatically by working in the
subtype throughout, rather than needing a separate membership argument on
the real-number formula.

**Routing through `thm:chain-lin`.** The `LinBLat2Mon unitInterval`
instance is built via `LinBLat2Mon.ofChain` (`NeSyCat/Truth/Chain.lean`),
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
`andC := (· * ·)` (real multiplication, restricted to the subtype), `done :=
1`, `parr p q := σ (σ p * σ q)` (the pinned `σ`-conjugate of multiplication,
`σ` Mathlib's `unitInterval.symm`), `dzero := 0`. Associativity and unit laws
for `andC` are inherited from `Icc.instMonoidWithZero`'s multiplication
(`mul_assoc`/`one_mul`/`mul_one`); for `parr` they transport along `σ`: `σσ`
cancels in the associativity chain, and `σ 0 = 1` gives the right unit,
`σ 1 = 0` mirrored on the left (`dzero_parr`/`parr_dzero`, from
`symm_symm`/`symm_zero`/`symm_one`). -/
noncomputable instance instBLat2Mon : BLat2Mon (_root_.unitInterval) where
  parr p q := σ (σ p * σ q)
  dzero := 0
  andC p q := p * q
  done := 1
  parr_assoc p q r := by simp [mul_assoc]
  dzero_parr p := by simp
  parr_dzero p := by simp
  andC_assoc p q r := mul_assoc p q r
  done_andC p := one_mul p
  andC_done p := mul_one p

/-- Blueprint `lem:unit-interval-truth-structure` (`BLat2CMon unitInterval`):
both monoids are commutative — `andC` since real multiplication is, `parr`
since its `σ`-conjugated multiplication is (`mul_comm` transports through
`σ`). -/
noncomputable instance instBLat2CMon : BLat2CMon (_root_.unitInterval) where
  __ := instBLat2Mon
  parr_comm p q := by
    have key1 : (parr p q : _root_.unitInterval) = σ (σ p * σ q) := rfl
    have key2 : (parr q p : _root_.unitInterval) = σ (σ q * σ p) := rfl
    rw [key1, key2, mul_comm]
  andC_comm p q := mul_comm p q

/-- Blueprint `lem:unit-interval-truth-structure` (`ZeroBot unitInterval`):
`dzero = 0 = ⊥` by construction (`Set.Icc`'s `⊥` and `0` coincide, both the
left endpoint). -/
instance instZeroBot : ZeroBot (_root_.unitInterval) where
  dzero_eq_bot := rfl

/-- Blueprint `lem:unit-interval-truth-structure` (`OneTop unitInterval`):
`done = 1 = ⊤` by construction (`Set.Icc`'s `⊤` and `1` coincide, both the
right endpoint). -/
instance instOneTop : OneTop (_root_.unitInterval) where
  done_eq_top := rfl

/-- Blueprint `lem:unit-interval-truth-structure` (`UnitBounds unitInterval`):
the packaged `ZeroBot`/`OneTop` conjunction (Definition `def:unit-bounds`). -/
instance instUnitBounds : UnitBounds (_root_.unitInterval) where

/-- Blueprint `lem:unit-interval-truth-structure` (monotonicity of `andC`,
right argument): `p ≤ q → r * p ≤ r * q`, `mul_le_mul_of_nonneg_left` on the
real coercions. -/
private theorem andC_mono_left {p q : _root_.unitInterval} (h : p ≤ q)
    (r : _root_.unitInterval) : andC r p ≤ andC r q :=
  mul_le_mul_of_nonneg_left h r.2.1

/-- Blueprint `lem:unit-interval-truth-structure` (monotonicity of `andC`,
left argument): dually, `p ≤ q → p * r ≤ q * r`. -/
private theorem andC_mono_right {p q : _root_.unitInterval} (h : p ≤ q)
    (r : _root_.unitInterval) : andC p r ≤ andC q r :=
  mul_le_mul_of_nonneg_right h r.2.1

/-- Blueprint `lem:unit-interval-truth-structure` (monotonicity of `parr`,
right argument): `σ` is antitone (`symm_le_symm`), so `p ≤ q` gives
`σ q ≤ σ p`, hence `σ r * σ q ≤ σ r * σ p` (monotone multiplication by a
nonnegative factor), hence `σ(σ r * σ p) ≤ σ(σ r * σ q)` (antitone `σ`
again). -/
private theorem parr_mono_left {p q : _root_.unitInterval} (h : p ≤ q)
    (r : _root_.unitInterval) : parr r p ≤ parr r q := by
  have key1 : (parr r p : _root_.unitInterval) = σ (σ r * σ p) := rfl
  have key2 : (parr r q : _root_.unitInterval) = σ (σ r * σ q) := rfl
  rw [key1, key2]
  exact symm_le_symm.mpr (mul_le_mul_of_nonneg_left (symm_le_symm.mpr h) (σ r).2.1)

/-- Blueprint `lem:unit-interval-truth-structure` (monotonicity of `parr`,
left argument): dual to `parr_mono_left`. -/
private theorem parr_mono_right {p q : _root_.unitInterval} (h : p ≤ q)
    (r : _root_.unitInterval) : parr p r ≤ parr q r := by
  have key1 : (parr p r : _root_.unitInterval) = σ (σ p * σ r) := rfl
  have key2 : (parr q r : _root_.unitInterval) = σ (σ q * σ r) := rfl
  rw [key1, key2]
  exact symm_le_symm.mpr (mul_le_mul_of_nonneg_right (symm_le_symm.mpr h) (σ r).2.1)

/-- Blueprint `lem:unit-interval-truth-structure` (`LinBLat2Mon unitInterval`,
"Theorem `thm:chain-lin` applies"): assembled via `LinBLat2Mon.ofChain` from
`unitInterval`'s `LinearOrder`, the `andC`/`parr` monotonicity above, and
`UnitBounds` — the point of this row: it exercises `thm:chain-lin` rather
than proving the eight linear laws by hand. -/
noncomputable instance instLinBLat2Mon : LinBLat2Mon (_root_.unitInterval) :=
  LinBLat2Mon.ofChain andC_mono_left andC_mono_right parr_mono_left parr_mono_right

/-- Blueprint `lem:unit-interval-truth-structure` (`LinBLat2CMon
unitInterval`): the commutative linear structure, combining
`instLinBLat2Mon` and `instBLat2CMon`. -/
noncomputable instance instLinBLat2CMon : LinBLat2CMon (_root_.unitInterval) where
  __ := instLinBLat2Mon
  __ := instBLat2CMon

/-- Blueprint `lem:unit-interval-truth-structure` (`DMStructure unitInterval`):
`dneg := σ` (`unitInterval.symm`, `σ p = 1 - p`) is involutive
(`symm_symm`), antitone (`symm_le_symm`), and satisfies the De Morgan law
`σ(p * q) = parr (σ q) (σ p)` — near-definitional: `parr (σ q) (σ p) = σ(σσq
* σσp) = σ(q * p) = σ(p * q)`, the `σσ` cancelling by `symm_symm` and the
remaining equality by commutativity of `*`. -/
noncomputable instance instDMStructure : DMStructure (_root_.unitInterval) where
  dneg := σ
  dneg_dneg := symm_symm
  dneg_antitone p q h := symm_le_symm.mpr h
  dneg_andC p q := by
    have key1 : (andC p q : _root_.unitInterval) = p * q := rfl
    have key2 : (parr (σ q) (σ p) : _root_.unitInterval) = σ (σ (σ q) * σ (σ p)) := rfl
    rw [key1, key2, symm_symm, symm_symm, mul_comm]

/-- Blueprint `lem:unit-interval-truth-structure` (closure/readout formula):
the blueprint's display formula `p + q - p*q` for `parr`, recovered as a
coercion lemma from the pinned `σ`-conjugate definition (`1 - (1-p)(1-q) =
p + q - pq`); membership in `[0,1]` needs no separate closure argument since
`parr p q` is already an element of the subtype by construction. -/
theorem coe_parr (p q : _root_.unitInterval) :
    (↑(parr p q) : ℝ) = ↑p + ↑q - ↑p * ↑q := by
  have key : (parr p q : _root_.unitInterval) = σ (σ p * σ q) := rfl
  rw [key]
  push_cast [coe_symm_eq]
  ring

end unitInterval

end NeSyCat
