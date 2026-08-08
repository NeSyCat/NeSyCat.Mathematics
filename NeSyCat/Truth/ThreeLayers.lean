/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.Truth.Lifted
import NeSyCat.Truth.BoolInstance
import NeSyCat.Truth.UnitInterval

/-!
# Three layers: pointwise closure, linear-lift, copying failure, decomposition

Blueprint items `lem:pointwise`, `lem:linear-lift`, `lem:copying-fails`, and
`thm:three-layers` (`blueprint/src/content.tex`, §"Three layers",
`[NeSy26, App. A]`), per the `.foreman/C2-T4-spec.md` encoding pin.

## `lem:pointwise`

Two parts: (1) `LatSRng`/`LatCSRng` (and, where both factors are bounded,
`BLatSRng`/`BLatCSRng`) instances on `Prod`, and `LatSRng`/`LatCSRng` on `Pi`
for an *arbitrary* index type `ι` (no finiteness needed — this covers the
blueprint's own "(finite) power" clause a fortiori, a Lean-more-general
instance in the chapter-1 precedent); (2) the `S^𝔹 ≅ S × S` clause,
connecting `MS S BoolW`'s `twoSlot` readout to the pointwise `Prod`
structure. `MS S BoolW` (`= X →₀ S`, `NeSyCat/Monad/SemiringMonad.lean`)
genuinely has an `+` (Finsupp's own `AddCommMonoid`, always pointwise, no
ambiguity — `twoSlot_add` below records that `twoSlot` is additive for it),
but **no** canonical multiplication is registered on it (Finsupp
deliberately carries no global pointwise-mul semiring instance, to avoid
clashing with the different `AddMonoidAlgebra`-style convolution product a
reader might otherwise expect): the hard rail against instance pollution on
Mathlib-shaped carriers forbids inventing one here. So the `⊗`/`0̇... /1`/
order-componentwise content is recorded as plain (non-instance) `def`s
transporting `S × S`'s own pointwise operations *backward* through
`twoSlot`, each with an "equational lemma on values" readout
(`pointwiseMul`/`pointwiseOne`/`pointwiseMeet`/`pointwiseJoin`/
`pointwiseBot`/`pointwiseTop` below) — mirroring exactly the pattern
`NeSyCat/Truth/Lifted.lean`'s `def:order-family` already uses for
`orderMeet`/`orderJoin` (transported functions, never new instances), just
via the plain (non-dualized) `twoSlot` rather than the dualized
`orderedTwoSlot` (a different order — see the note on `thm:three-layers`
below).

## `lem:linear-lift`

Over `[CommSemiring S]` (the `163adf1`-patched blueprint hypothesis): the
lifted family's monoid laws (associativity, commutativity, two-sided units)
for `⅋`/`\&` (`parrM`/`andM`), plus the De Morgan involution package for `¬`
(`negM`), stated as EQUATIONAL LEMMAS on `MS S BoolW` — no
`Lattice`/`BLat2Mon`/`Monoid`-style instance is registered on `MS S BoolW`
or `Finsupp`, matching the hard rail. Proved by two-slot transport: each
identity is checked after applying the (injective) `twoSlot` equivalence,
reducing to an equation in `S` closed by `ring` — exactly `lem:lifted-mass`'s
own explicit formulas (`twoSlot_andM`/`twoSlot_parrM`/`twoSlot_negM`), the
blueprint's own sanctioned proof route ("Directly from Lemma
lem:lifted-mass"). Associativity needs no commutativity of `S` at all (the
same six/four cross terms appear on both sides, `ring`-provably equal via
only the semiring axioms); commutativity of `⅋`/`\&` is exactly the one
place `S`'s own `mul_comm` enters the argument — this is the concrete,
routing-formula-level shadow of `thm:semiring-monad-commutative`'s
`dstL = dstR ↔ S` commutative (`NeSyCat/Monad/SemiringMonad.lean`): the two
independent binds building `parrM`/`andM` from their two arguments agree in
either order exactly because `S`'s multiplication does, the same fact
`dst_comm` packages at the level of the general strength maps `dstL`/`dstR`.

## `lem:copying-fails`

The fair-coin witness (`fairCoin : Dist BoolW`, mass `½`/`½`, built directly
from `distReadout.symm` on the readout `½ : unitInterval`) has
`andD fairCoin fairCoin ≠ fairCoin`, via `distReadout_andD` reducing this to
`(1/2 : unitInterval) * (1/2) ≠ (1/2 : unitInterval)` — `norm_num` on the
real coercions. The blueprint's own general statement ("fail in general.
Witness: …") is additionally recorded at `unitInterval` level as an
`∃`-statement (`exists_andC_ne_self`), matching its stated shape rather than
strengthening it to a `∀`.

## `thm:three-layers`

A witness cluster, not a monster theorem: (i) is witnessed by
`lem:pointwise`'s own `Prod`/`Pi` instances, resolved at the three concrete
squares the item names (`BoolW`, `ℝ≥0`, `LogS`) plus a citation of
`prob_not_semiring` for the excluded `ProbS` row; (ii) needs no additional
Lean beyond `lem:linear-lift`'s and `lem:copying-fails`'s own marks (a
lemma-free clause, "the copying axioms are exactly the order-generating
ones" and "two commutative monoids with a De Morgan involution, not a
semiring" both already witnessed there); (iii) is `def:order-family`
(`NeSyCat/Truth/Lifted.lean`, already `\leanok`) plus three boundary
witnesses proved here: `order_iff_inf_eq_left` (order-generation, `u ≤ v ↔
u ⊓ v = u`, any lattice), the `𝔹`-coincidence (already `lem:bool-truth-structure`'s
`BoolW.parr_eq_sup`/`BoolW.andC_eq_inf` — cited, not reproved: "the carrier is
idempotent, on `𝔹` itself" reads as `S := BoolW`, where the lifted family's
*definitional source* on `BoolW` collapses onto the lattice, not a claim
about `MS BoolW BoolW`'s own `andM`/`parrM` pointwise agreeing with
`orderMeet`/`orderJoin` — the latter is false in general, checked and
rejected before writing this file, the disprove-guard in action), and
units-vs-bounds: the positive witness is `unitInterval`'s own `UnitBounds`
instance (`NeSyCat/Truth/UnitInterval.lean`, cited), the negative witness
(`not_isBot_orderedTwoSlot_ret_zero`) exhibits the `⅋`-unit's image under
`orderedTwoSlot` at `S := ℝ≥0` failing `IsBot`.
-/

namespace NeSyCat

open scoped NNReal

/-! ## `lem:pointwise`, part 1: `Prod`/`Pi` lattice-semiring instances -/

section PointwiseInstances

variable {S T : Type*}

/-- Blueprint `lem:pointwise` (Product lattice-semiring, general form):
the product of two `LatSRng`s is again a `LatSRng` — `Prod.instSemiring`
and `Prod.instLattice` supply the semiring/lattice data; only the four
monotonicity fields (absent from a bare `Semiring`/`Lattice` bundle) need
proving, each componentwise from the corresponding fact in `S`/`T` (`≤` on
`S × T` is *definitionally* the conjunction of the two componentwise `≤`s,
`Prod.le_def`, so the anonymous constructor suffices). -/
instance instLatSRngProd [LatSRng S] [LatSRng T] : LatSRng (S × T) where
  add_le_add_left h c := ⟨LatSRng.add_le_add_left h.1 c.1, LatSRng.add_le_add_left h.2 c.2⟩
  add_le_add_right h c := ⟨LatSRng.add_le_add_right h.1 c.1, LatSRng.add_le_add_right h.2 c.2⟩
  mul_le_mul_left h c := ⟨LatSRng.mul_le_mul_left h.1 c.1, LatSRng.mul_le_mul_left h.2 c.2⟩
  mul_le_mul_right h c := ⟨LatSRng.mul_le_mul_right h.1 c.1, LatSRng.mul_le_mul_right h.2 c.2⟩

/-- Blueprint `lem:pointwise` (Product commutative lattice-semiring): the
commutative refinement, adding `mul_comm` componentwise. -/
instance instLatCSRngProd [LatCSRng S] [LatCSRng T] : LatCSRng (S × T) where
  __ := (inferInstance : LatSRng (S × T))
  mul_comm p q := Prod.ext (LatCSRng.mul_comm p.1 q.1) (LatCSRng.mul_comm p.2 q.2)

/-- Blueprint `lem:pointwise` (Product bounded lattice-semiring): where both
factors are bounded, so is the product (`Prod.instBoundedOrder`), giving a
`BLatSRng` on `S × T`. -/
instance instBLatSRngProd [BLatSRng S] [BLatSRng T] : BLatSRng (S × T) where
  __ := (inferInstance : LatSRng (S × T))
  __ := (inferInstance : BoundedOrder (S × T))

/-- Blueprint `lem:pointwise` (Product bounded commutative lattice-semiring):
the commutative refinement of `instBLatSRngProd`. -/
instance instBLatCSRngProd [BLatCSRng S] [BLatCSRng T] : BLatCSRng (S × T) where
  __ := (inferInstance : BLatSRng (S × T))
  mul_comm p q := Prod.ext (BLatCSRng.mul_comm p.1 q.1) (BLatCSRng.mul_comm p.2 q.2)

variable {ι : Type*}

/-- Blueprint `lem:pointwise` (Pointwise-power lattice-semiring, general
form): `LatSRng (ι → S)` for an *arbitrary* index type `ι` — no finiteness
hypothesis is needed, generalizing the blueprint's own "(finite) power"
clause a fortiori (the chapter-1 precedent for a Lean-more-general
instance: `Pi.semiring`/`Pi.instLattice` already hold at this generality in
Mathlib, so the monotonicity fields, proved pointwise via `S`'s own, cost
nothing extra). -/
instance instLatSRngPi [LatSRng S] : LatSRng (ι → S) where
  add_le_add_left h c i := LatSRng.add_le_add_left (h i) (c i)
  add_le_add_right h c i := LatSRng.add_le_add_right (h i) (c i)
  mul_le_mul_left h c i := LatSRng.mul_le_mul_left (h i) (c i)
  mul_le_mul_right h c i := LatSRng.mul_le_mul_right (h i) (c i)

/-- Blueprint `lem:pointwise` (Pointwise-power commutative lattice-semiring):
the commutative refinement, `mul_comm` pointwise. -/
instance instLatCSRngPi [LatCSRng S] : LatCSRng (ι → S) where
  __ := (inferInstance : LatSRng (ι → S))
  mul_comm f g := funext fun i => LatCSRng.mul_comm (f i) (g i)

end PointwiseInstances

/-! ## `lem:pointwise`, part 2: the `S^𝔹 ≅ S × S` clause -/

section PointwiseTransport

variable {S : Type*} [Semiring S]

/-- Blueprint `lem:pointwise` (`⊕` componentwise): `twoSlot` is additive for
`MS S BoolW`'s own (genuine, unambiguous) `+` — `Finsupp.add_apply` is
already pointwise, so this is the real content of the `⊕`-clause, needing
no auxiliary `def`. -/
theorem twoSlot_add (w v : MS S BoolW) : twoSlot (w + v) = twoSlot w + twoSlot v := by
  ext <;> simp [twoSlot_apply, Finsupp.add_apply]

/-- `twoSlot` sends `MS S BoolW`'s `0` to `S × S`'s `(0, 0)` — the trivial
half of the `⊕`-clause (the identity element matching the additive unit
transported by `twoSlot_add`). -/
theorem twoSlot_zero : twoSlot (0 : MS S BoolW) = (0, 0) := by
  ext <;> simp [twoSlot_apply]

/-- Blueprint `lem:pointwise` (`⊗` componentwise, transported value, NOT an
instance on `MS S BoolW`): the pointwise product of two truth-space values,
defined by pulling `S × S`'s own multiplication back through `twoSlot` —
mirrors `NeSyCat/Truth/Lifted.lean`'s `orderMeet`/`orderJoin` pattern
exactly, just via the plain (non-dualized) `twoSlot`. -/
noncomputable def pointwiseMul (w v : MS S BoolW) : MS S BoolW :=
  twoSlot.symm (twoSlot w * twoSlot v)

/-- Readout of `pointwiseMul`: its `twoSlot` image is `S × S`'s own
product, componentwise — the equational-lemma-on-values form of the
`⊗`-clause. -/
theorem twoSlot_pointwiseMul (w v : MS S BoolW) :
    twoSlot (pointwiseMul w v) = twoSlot w * twoSlot v :=
  Equiv.apply_symm_apply _ _

/-- Blueprint `lem:pointwise` (`⊗`-unit componentwise, transported value):
the multiplicative unit of the pointwise structure, `twoSlot.symm (1, 1)` —
a genuinely new value (distinct from both `Ret(0) = (1,0)` and
`Ret(1) = (0,1)`, `NeSyCat/Truth/Lifted.lean`'s `twoSlot_ret_zero`/
`twoSlot_ret_one`), matching the blueprint's `1` clause for the pointwise
structure specifically. -/
noncomputable def pointwiseOne : MS S BoolW := twoSlot.symm (1, 1)

theorem twoSlot_pointwiseOne : twoSlot (pointwiseOne : MS S BoolW) = (1, 1) :=
  Equiv.apply_symm_apply _ _

variable [Lattice S]

/-- Blueprint `lem:pointwise` (`∧` componentwise, transported value): the
pointwise meet, `twoSlot.symm (twoSlot w ⊓ twoSlot v)` — the *un-dualized*
counterpart of `NeSyCat/Truth/Lifted.lean`'s `orderMeet` (which dualizes
slot `0` for the different `def:order-family` purpose, `thm:three-layers`
item (iii)); this is the plain `S^𝔹` lattice order used for item (i)'s
closure/iteration clause. -/
noncomputable def pointwiseMeet (w v : MS S BoolW) : MS S BoolW :=
  twoSlot.symm (twoSlot w ⊓ twoSlot v)

theorem twoSlot_pointwiseMeet (w v : MS S BoolW) :
    twoSlot (pointwiseMeet w v) = twoSlot w ⊓ twoSlot v :=
  Equiv.apply_symm_apply _ _

/-- Blueprint `lem:pointwise` (`∨` componentwise, transported value), dually. -/
noncomputable def pointwiseJoin (w v : MS S BoolW) : MS S BoolW :=
  twoSlot.symm (twoSlot w ⊔ twoSlot v)

theorem twoSlot_pointwiseJoin (w v : MS S BoolW) :
    twoSlot (pointwiseJoin w v) = twoSlot w ⊔ twoSlot v :=
  Equiv.apply_symm_apply _ _

variable [BoundedOrder S]

/-- Blueprint `lem:pointwise` (`⊥` componentwise, transported value). -/
noncomputable def pointwiseBot : MS S BoolW := twoSlot.symm ⊥

theorem twoSlot_pointwiseBot : twoSlot (pointwiseBot : MS S BoolW) = (⊥, ⊥) :=
  Equiv.apply_symm_apply _ _

/-- Blueprint `lem:pointwise` (`⊤` componentwise, transported value). -/
noncomputable def pointwiseTop : MS S BoolW := twoSlot.symm ⊤

theorem twoSlot_pointwiseTop : twoSlot (pointwiseTop : MS S BoolW) = (⊤, ⊤) :=
  Equiv.apply_symm_apply _ _

end PointwiseTransport

/-! ## `lem:linear-lift` -/

section LinearLift

variable {S : Type*} [Semiring S]

/-! ### Value-level component lemmas (general `[Semiring S]`), the routing
engine specialized to a single coordinate — used throughout the equational
package below. -/

theorem andM_apply_zero (w v : MS S BoolW) :
    andM w v 0 = w 0 * v 0 + w 0 * v 1 + w 1 * v 0 :=
  congrArg Prod.fst (twoSlot_andM w v)

theorem andM_apply_one (w v : MS S BoolW) : andM w v 1 = w 1 * v 1 :=
  congrArg Prod.snd (twoSlot_andM w v)

theorem parrM_apply_zero (w v : MS S BoolW) : parrM w v 0 = w 0 * v 0 :=
  congrArg Prod.fst (twoSlot_parrM w v)

theorem parrM_apply_one (w v : MS S BoolW) :
    parrM w v 1 = w 0 * v 1 + w 1 * v 0 + w 1 * v 1 :=
  congrArg Prod.snd (twoSlot_parrM w v)

theorem negM_apply_zero (w : MS S BoolW) : negM w 0 = w 1 :=
  congrArg Prod.fst (twoSlot_negM w)

theorem negM_apply_one (w : MS S BoolW) : negM w 1 = w 0 :=
  congrArg Prod.snd (twoSlot_negM w)

theorem ret_zero_apply_zero : (ret (0 : BoolW) : MS S BoolW) 0 = 1 :=
  congrArg Prod.fst twoSlot_ret_zero

theorem ret_zero_apply_one : (ret (0 : BoolW) : MS S BoolW) 1 = 0 :=
  congrArg Prod.snd twoSlot_ret_zero

theorem ret_one_apply_zero : (ret (1 : BoolW) : MS S BoolW) 0 = 0 :=
  congrArg Prod.fst twoSlot_ret_one

theorem ret_one_apply_one : (ret (1 : BoolW) : MS S BoolW) 1 = 1 :=
  congrArg Prod.snd twoSlot_ret_one

variable {R : Type*} [CommSemiring R]

/-! ### `⅋`/`\&` are commutative monoids (`lem:linear-lift`, over
`[CommSemiring S]`) -/

/-- Blueprint `lem:linear-lift` (`\&` associativity): proved by `twoSlot`
transport — both sides expand, via `andM_apply_zero`/`andM_apply_one`, to
the same sum of three-fold products, `ring`-closed with no need for `S`'s
commutativity (matching the blueprint proof: associativity uses only the
semiring axioms of `S`). -/
theorem andM_assoc (a b c : MS R BoolW) : andM (andM a b) c = andM a (andM b c) := by
  apply twoSlot.injective
  rw [twoSlot_andM, twoSlot_andM, andM_apply_zero, andM_apply_one, andM_apply_zero,
    andM_apply_one]
  ext <;> ring

/-- Blueprint `lem:linear-lift` (`\&` commutativity): the one identity that
genuinely needs `S`'s own `mul_comm` — the concrete, routing-formula-level
shadow of `thm:semiring-monad-commutative`'s `dstL = dstR ↔ S` commutative
(`NeSyCat/Monad/SemiringMonad.lean`'s `dst_comm`): the two independent
binds building `andM` from its arguments agree in either order exactly
because `*` does on `S`. -/
theorem andM_comm (a b : MS R BoolW) : andM a b = andM b a := by
  apply twoSlot.injective
  rw [twoSlot_andM, twoSlot_andM]
  ext <;> ring

/-- Blueprint `lem:linear-lift` (`\&` left unit): `Ret(1) \& w = w`. -/
theorem ret_one_andM (w : MS R BoolW) : andM (ret 1) w = w := by
  apply twoSlot.injective
  rw [twoSlot_andM, ret_one_apply_zero, ret_one_apply_one]
  ext <;> simp

/-- Blueprint `lem:linear-lift` (`\&` right unit): `w \& Ret(1) = w`. -/
theorem andM_ret_one (w : MS R BoolW) : andM w (ret 1) = w := by
  apply twoSlot.injective
  rw [twoSlot_andM, ret_one_apply_zero, ret_one_apply_one]
  ext <;> simp

/-- Blueprint `lem:linear-lift` (`⅋` associativity), dual to `andM_assoc`. -/
theorem parrM_assoc (a b c : MS R BoolW) : parrM (parrM a b) c = parrM a (parrM b c) := by
  apply twoSlot.injective
  rw [twoSlot_parrM, twoSlot_parrM, parrM_apply_zero, parrM_apply_one, parrM_apply_zero,
    parrM_apply_one]
  ext <;> ring

/-- Blueprint `lem:linear-lift` (`⅋` commutativity), dual to `andM_comm` —
again the one place `S`'s commutativity enters, matching the blueprint's
"commutativity of `⅋, \&` specifically needs … `dstL = dstR`" proof note. -/
theorem parrM_comm (a b : MS R BoolW) : parrM a b = parrM b a := by
  apply twoSlot.injective
  rw [twoSlot_parrM, twoSlot_parrM]
  ext <;> ring

/-- Blueprint `lem:linear-lift` (`⅋` left unit): `Ret(0) ⅋ w = w`. -/
theorem ret_zero_parrM (w : MS R BoolW) : parrM (ret 0) w = w := by
  apply twoSlot.injective
  rw [twoSlot_parrM, ret_zero_apply_zero, ret_zero_apply_one]
  ext <;> simp

/-- Blueprint `lem:linear-lift` (`⅋` right unit): `w ⅋ Ret(0) = w`. -/
theorem parrM_ret_zero (w : MS R BoolW) : parrM w (ret 0) = w := by
  apply twoSlot.injective
  rw [twoSlot_parrM, ret_zero_apply_zero, ret_zero_apply_one]
  ext <;> simp

/-! ### `¬` is a De Morgan involution between them (general `[Semiring S]`,
no commutativity needed) -/

/-- Blueprint `lem:linear-lift` (De Morgan involution): `¬¬w = w`. -/
theorem negM_negM (w : MS S BoolW) : negM (negM w) = w := by
  apply twoSlot.injective
  rw [twoSlot_negM, negM_apply_zero, negM_apply_one, twoSlot_apply]

/-- Blueprint `lem:linear-lift` (De Morgan, unit swap): `¬ Ret(0) = Ret(1)`. -/
theorem negM_ret_zero : (negM (ret 0) : MS S BoolW) = ret 1 := by
  apply twoSlot.injective
  rw [twoSlot_negM, ret_zero_apply_zero, ret_zero_apply_one, twoSlot_ret_one]

/-- Blueprint `lem:linear-lift` (De Morgan law, `⅋` to `\&`): `¬(w ⅋ v) = ¬w
\& ¬v`. Unlike `negM_negM`/`negM_ret_zero` above, this needs `S`'s
commutativity (the first coordinate's cross terms reorder as `w0v1+w1v0`
vs. `w1v0+w0v1`, an `+`-only reordering that holds at any `[Semiring S]` —
but stated under `[CommSemiring R]` alongside `negM_andM` to keep
`lem:linear-lift`'s De Morgan package at one uniform hypothesis, matching
the blueprint's own single-item bundling). -/
theorem negM_parrM (w v : MS R BoolW) : negM (parrM w v) = andM (negM w) (negM v) := by
  apply twoSlot.injective
  rw [twoSlot_negM, twoSlot_andM, parrM_apply_zero, parrM_apply_one, negM_apply_zero,
    negM_apply_one, negM_apply_zero, negM_apply_one]
  ext <;> ring

/-- Blueprint `lem:linear-lift` (De Morgan law, `\&` to `⅋`): `¬(w \& v) =
¬v ⅋ ¬w`. This one genuinely needs `R`'s `mul_comm` (`w1*v1 = v1*w1` in the
first coordinate), the De Morgan identity where `S`'s commutativity is
load-bearing, not merely convenient. -/
theorem negM_andM (w v : MS R BoolW) : negM (andM w v) = parrM (negM v) (negM w) := by
  apply twoSlot.injective
  rw [twoSlot_negM, twoSlot_parrM, andM_apply_zero, andM_apply_one, negM_apply_zero,
    negM_apply_one, negM_apply_zero, negM_apply_one]
  ext <;> ring

end LinearLift

/-! ## `lem:copying-fails` -/

section CopyingFails

open scoped unitInterval

/-- The fair-coin witness: the `Dist BoolW` value with mass `½`/`½`,
constructed directly as `distReadout.symm` of the readout point `½`. -/
noncomputable def fairCoin : Dist BoolW := distReadout.symm ⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩

theorem distReadout_fairCoin :
    distReadout fairCoin = (⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : _root_.unitInterval) :=
  Equiv.apply_symm_apply _ _

/-- Blueprint `lem:copying-fails` (fair-coin witness): the `Dist`-restricted
`\&`-lift is not idempotent at the fair coin — `andD ρ ρ ≠ ρ`. Proved via
the readout homomorphism `distReadout_andD`: `readout (ρ andD ρ) = ½ * ½ =
¼ ≠ ½ = readout ρ`, `norm_num` on the real/`unitInterval` coercions. -/
theorem andD_fairCoin_ne : andD fairCoin fairCoin ≠ fairCoin := by
  intro h
  have hread : distReadout (andD fairCoin fairCoin) = distReadout fairCoin := by rw [h]
  rw [distReadout_andD, distReadout_fairCoin] at hread
  have hcoe : ((BLat2Mon.andC
      (⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : _root_.unitInterval)
      (⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : _root_.unitInterval) :
      _root_.unitInterval) : ℝ) =
      ((⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : _root_.unitInterval) : ℝ) :=
    congrArg _ hread
  norm_num [BLat2Mon.andC] at hcoe

/-- Blueprint `lem:copying-fails` (general clause, `∃`-form matching the
blueprint's own "fail in general. Witness: …" statement shape): `\&` is not
idempotent — some `p` strictly between `0` and `1` has `p \& p ≠ p`,
witnessed by `p = 1/2` (`p \& p = p² ≠ p` since `p ∈ \{0,1\}` would be
needed for equality, `norm_num`). -/
theorem exists_andC_ne_self :
    ∃ p : _root_.unitInterval, (0 : ℝ) < p ∧ (p : ℝ) < 1 ∧ BLat2Mon.andC p p ≠ p := by
  refine ⟨⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩, by norm_num, by norm_num, fun h => ?_⟩
  have hcoe : ((BLat2Mon.andC (⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : _root_.unitInterval)
      (⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : _root_.unitInterval) :
      _root_.unitInterval) : ℝ) =
      ((⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : _root_.unitInterval) : ℝ) :=
    congrArg _ h
  norm_num [BLat2Mon.andC] at hcoe

end CopyingFails

/-! ## `thm:three-layers`: the witness cluster -/

section ThreeLayers

/-! ### (i) closure/iteration: the pointwise construction closes -/

/-- Blueprint `thm:three-layers` (i), `BoolW` square: `BoolW × BoolW`
resolves a `LatCSRng` instance purely from `lem:pointwise`'s `instLatCSRngProd`
plus `BoolW`'s own `BLatCSRng` (hence `LatCSRng`, via `BLatCSRng.toLatCSRng`)
instance — `MS BoolW (BoolW)` can serve as a next layer's weight semiring. -/
@[reducible] def latCSRngBoolWSq : LatCSRng (BoolW × BoolW) := inferInstance

/-- Blueprint `thm:three-layers` (i), mass square: `ℝ≥0 × ℝ≥0` resolves a
`LatCSRng` instance from `lem:pointwise`'s `instLatCSRngProd` plus `ℝ≥0`'s
own `instLatCSRngNNReal`. The excluded row, `ProbS = [0,1]` with `⊕ := p ⊕
q = p+q-pq`, is `lem:prob-not-semiring` (`prob_not_semiring`, cited, nothing
new to prove here). -/
@[reducible] noncomputable def latCSRngNNRealSq : LatCSRng (ℝ≥0 × ℝ≥0) := inferInstance

/-- Blueprint `thm:three-layers` (i), log square: `LogS × LogS` resolves a
`LatCSRng` instance from `lem:pointwise`'s `instLatCSRngProd` plus `LogS`'s
own `instLatCSRngLogS` (`NeSyCat/Monad/LogIso.lean`). -/
@[reducible] noncomputable def latCSRngLogSSq : LatCSRng (LogS × LogS) := inferInstance

/-! ### (ii) linear/lifted: no additional Lean needed

Covered entirely by `lem:linear-lift`'s and `lem:copying-fails`'s own marks
above — a lemma-free clause of the theorem, per the `.foreman/C2-T4-spec.md`
pin. -/

/-! ### (iii) order origin: `def:order-family` plus three boundary witnesses -/

/-- Blueprint `thm:three-layers` (order-generation): the copying axioms are
exactly the order-generating ones, `u ≤ v ↔ u ⊓ v = u`, on any lattice —
named here (rather than left as a bare citation of `inf_eq_left`) so the
item's own `\lean` mark has a home. -/
theorem order_iff_inf_eq_left {α : Type*} [Lattice α] (u v : α) : u ≤ v ↔ u ⊓ v = u :=
  inf_eq_left.symm

/-! **𝔹-coincidence.** "They coincide exactly where the carrier is
idempotent, on `𝔹` itself" is `BoolW.parr_eq_sup`/`BoolW.andC_eq_inf`
(`NeSyCat/Truth/BoolInstance.lean`, already `\leanok` under
`lem:bool-truth-structure`) — cited, not reproved: this is a statement about
`BoolW`'s own `BLat2Mon` structure collapsing onto its lattice ops when the
carrier `S := BoolW` is idempotent, not a claim that `MS BoolW BoolW`'s
lifted `andM`/`parrM` pointwise agree with `orderMeet`/`orderJoin` in
general (checked by hand and found FALSE — e.g. `andM` at `w₀=1,v₀=0,w₁=0,
v₁=0` gives coordinate `0`, but `orderMeet`'s `w₀ ⊔ v₀` gives `1` — before
writing this file, the disprove-guard in action: the correct reading routes
through `BoolW`'s own instance, not the monad-lifted family at `S := BoolW`). -/

/-! **Units-vs-bounds, positive witness.** `unitInterval`'s own `UnitBounds`
instance (`NeSyCat/Truth/UnitInterval.lean`'s `unitInterval.instUnitBounds`,
built from `instZeroBot`/`instOneTop`) is the positive case: `Ret(0),Ret(1)`
agree with `⊥,⊤` on the normalized (mass-one) row — cited, not reproved. -/

/-- Blueprint `thm:three-layers` (units-vs-bounds, negative witness): in the
mass order family (`Sᵒᵈ × S` at `S := ℝ≥0`), the `⅋`-unit's image under
`orderedTwoSlot` is not a bottom — exhibited via the point
`(toDual 2, 0)`, since `toDual 1 ≤ toDual 2` would force `2 ≤ 1` in `ℝ≥0`. -/
theorem not_isBot_orderedTwoSlot_ret_zero :
    ¬ IsBot (orderedTwoSlot (ret (0 : BoolW) : MS ℝ≥0 BoolW)) := by
  intro hbot
  have h := hbot (OrderDual.toDual (2 : ℝ≥0), (0 : ℝ≥0))
  rw [orderedTwoSlot_apply, ret_zero_apply_zero, ret_zero_apply_one] at h
  have h1 : (OrderDual.toDual (1 : ℝ≥0) : (ℝ≥0)ᵒᵈ) ≤ OrderDual.toDual (2 : ℝ≥0) := h.1
  have h2 : (2 : ℝ≥0) ≤ 1 := OrderDual.toDual_le_toDual.mp h1
  norm_num at h2

end ThreeLayers

end NeSyCat
