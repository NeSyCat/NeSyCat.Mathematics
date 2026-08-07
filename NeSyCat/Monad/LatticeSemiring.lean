/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib

/-!
# Lattice-semirings

Blueprint items `def:lattice-semiring` and `lem:prob-not-semiring`
(`blueprint/src/content.tex`, §"Semiring weight monads", `[NeSy26, App. A]`).

This file defines the `LatticeSemiring` class and delivers two of its three
running instances (Boolean, mass); the third (log) arrives via transport
along the log isomorphism in a later ticket (C1-T3), see the note below. It
also proves that `([0,1], p ⊕ q := p+q-pq, ·, 0, 1)` is *not* a semiring,
witnessing the failure of distributivity concretely.
-/

namespace NeSyCat

/-- Blueprint `def:lattice-semiring` (Lattice-semiring): a lattice-semiring is
a commutative semiring `(S, ⊕, ⊗, 0, 1)` equipped with a lattice order `≤` on
the carrier `S` (a meet `⊓` and a join `⊔` exist for every pair of elements,
with bounds `⊥`, `⊤` existing where indicated — e.g. the library's mass
instance has an in-carrier `⊥ = 0` but no in-carrier `⊤`, only after
adjoining `∞` externally) such that `⊕` (`+`) and `⊗` (`*`) are each
monotone in every argument with respect to `≤`. Only left-monotonicity is
taken as a field; right-monotonicity (`LatticeSemiring.add_le_add_right`,
`LatticeSemiring.mul_le_mul_right`) is derived from it via commutativity, so
the class still faithfully captures "monotone in each argument" without
redundant fields. -/
class LatticeSemiring (S : Type*) extends CommSemiring S, Lattice S where
  /-- `+` is monotone in its right argument. -/
  add_le_add_left : ∀ {a b : S}, a ≤ b → ∀ c : S, c + a ≤ c + b
  /-- `*` is monotone in its right argument. -/
  mul_le_mul_left : ∀ {a b : S}, a ≤ b → ∀ c : S, c * a ≤ c * b

namespace LatticeSemiring

variable {S : Type*} [LatticeSemiring S]

/-- `+` is monotone in its left argument, derived from
`LatticeSemiring.add_le_add_left` via commutativity. -/
theorem add_le_add_right {a b : S} (h : a ≤ b) (c : S) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]
  exact LatticeSemiring.add_le_add_left h c

/-- `*` is monotone in its left argument, derived from
`LatticeSemiring.mul_le_mul_left` via commutativity. -/
theorem mul_le_mul_right {a b : S} (h : a ≤ b) (c : S) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c]
  exact LatticeSemiring.mul_le_mul_left h c

end LatticeSemiring

/-! ### The Boolean lattice-semiring instance

Mathlib already equips `Bool` with a `CommSemiring` structure (`+ = xor`,
`* = and`: the two-element Boolean *ring* `GF(2)`), which is **not** the
Boolean semiring of the blueprint (`⊕ = or`, `⊗ = and`, no additive
inverses). To avoid clobbering, or being clobbered by, that existing
instance, `BoolW` is a fresh type synonym carrying the blueprint's own
operations. -/

/-- Type synonym for `Bool` carrying the blueprint's Boolean lattice-semiring
structure (`⊕ = or`, `⊗ = and`), kept separate from Mathlib's existing
`CommSemiring Bool` (the `xor`/`and` Boolean ring) so the two instances do
not conflict. -/
def BoolW : Type := Bool
  deriving DecidableEq, Fintype

namespace BoolW

instance : Lattice BoolW := inferInstanceAs (Lattice Bool)

instance : Zero BoolW := ⟨(false : Bool)⟩
instance : One BoolW := ⟨(true : Bool)⟩
instance : Add BoolW := ⟨fun a b => a ⊔ b⟩
instance : Mul BoolW := ⟨fun a b => a ⊓ b⟩

instance : CommSemiring BoolW where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  nsmul := nsmulRec

/-- The Boolean instance of `NeSyCat.LatticeSemiring`: `⊕ = or` is exactly
the lattice join and `⊗ = and` is exactly the lattice meet, so monotonicity
reduces to `sup_le_sup_left`/`inf_le_inf_left`. -/
instance instLatticeSemiring : LatticeSemiring BoolW where
  add_le_add_left h c := sup_le_sup_left h c
  mul_le_mul_left h c := inf_le_inf_left c h

end BoolW

/-! ### The mass lattice-semiring instance (`ℝ≥0`)

Assembled entirely from Mathlib's existing `CommSemiring`, `Lattice`, and
order-monotonicity instances on `NNReal` — no algebraic law is reproved
here, only assembled into the `LatticeSemiring` bundle. The mass carrier has
an in-carrier bottom (`0`) but **no** in-carrier top: the blueprint's
`⊤ = ∞` bound only exists after adjoining `∞` externally, which is not part
of this instance. -/

open scoped NNReal

/-- The mass instance of `NeSyCat.LatticeSemiring`, on `ℝ≥0` (`⊕ = +`,
`⊗ = ·`). `NNReal`'s own `CommSemiring`/`Lattice`/order instances supply
everything except the two monotonicity fields, which are Mathlib's
`add_le_add_right`/`mul_le_mul_right` for `ℝ≥0`. -/
noncomputable instance instLatticeSemiringNNReal : LatticeSemiring ℝ≥0 where
  add_le_add_left h c := add_le_add_right h c
  mul_le_mul_left h c := mul_le_mul_right h c

/-! The log instance (`lse`, `+`) is deliberately **not** provided here: per
the blueprint it arrives by transporting the mass instance along the log
isomorphism (`lem:log-iso`), which is ticket C1-T3's job, not this one. -/

/-! ### `lem:prob-not-semiring`: probability is not a semiring -/

/-- The probabilistic-sum operation `p ⊕ q := p + q - p*q` used to test
whether `([0,1], ⊕, ·, 0, 1)` forms a semiring (blueprint
`lem:prob-not-semiring`). Defined on all of `ℝ` for convenience; the lemma
below only uses it on `[0,1]`. -/
def pSum (p q : ℝ) : ℝ := p + q - p * q

/-- Blueprint `lem:prob-not-semiring` (Probability is not a semiring):
`([0,1], pSum, ·, 0, 1)` is not a semiring, because `·` does not distribute
over `pSum` in general: at the witness `p = q = r = 1/2`,
`p * pSum q r = 3/8 ≠ 7/16 = pSum (p*q) (p*r)`, all three witnesses lying in
`[0,1]`. -/
theorem prob_not_semiring :
    ∃ p ∈ Set.Icc (0 : ℝ) 1, ∃ q ∈ Set.Icc (0 : ℝ) 1, ∃ r ∈ Set.Icc (0 : ℝ) 1,
      p * pSum q r ≠ pSum (p * q) (p * r) := by
  refine ⟨1 / 2, by norm_num, 1 / 2, by norm_num, 1 / 2, by norm_num, ?_⟩
  unfold pSum
  norm_num

end NeSyCat
