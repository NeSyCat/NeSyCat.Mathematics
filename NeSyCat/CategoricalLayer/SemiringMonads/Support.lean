/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.SemiringMonads.LatticeSemiring

/-!
# The support readout

Blueprint items `def:support-readout`, `lem:support-hom-iff`, and
`lem:support-fails-ring`
(`blueprint/src/content.tex`, §"Semiring weight monads", C3-TL-A; see that
section's own citation comment for the Domingos provenance of
`lem:support-hom-iff`).

`supp` reads a semiring element off to `BoolW` by asking whether it is
nonzero. `support_hom_iff` characterizes exactly when this readout is a
semiring homomorphism: precisely when the semiring is zerosumfree (a sum is
zero only when both summands are) and has no zero divisors. `Semiring`'s own
`zero_add`/`add_zero` and `zero_mul`/`mul_zero` laws already make the
"forward" half of each biconditional (`a = b = 0 → a + b = 0`,
`a = 0 ∨ b = 0 → a * b = 0`) hold unconditionally in any semiring, so the
two named hypotheses are exactly, and only, their converses.
`support_fails_ring` witnesses that this collapses on `ℤ`, a genuine ring:
`1` and `-1` are both nonzero, yet their sum `0` reads out as `0`, not the
`BoolW`-join of two `1`s.
-/

namespace NeSyCat

/-- Blueprint `def:support-readout`: the **support readout**
`supp : S → 𝔹` on a semiring `S` sends `a` to `1` (true) when `a ≠ 0` and to
`0` (false) when `a = 0`. -/
def supp {S : Type*} [Zero S] [DecidableEq S] (a : S) : BoolW :=
  if a = 0 then 0 else 1

private theorem supp_eq_zero_of_eq_zero {S : Type*} [Zero S] [DecidableEq S]
    {a : S} (h : a = 0) : supp a = 0 :=
  if_pos h

private theorem supp_eq_one_of_ne_zero {S : Type*} [Zero S] [DecidableEq S]
    {a : S} (h : a ≠ 0) : supp a = 1 :=
  if_neg h

private theorem boolw_add_left_one (y : BoolW) : (1 : BoolW) + y = 1 := by revert y; decide
private theorem boolw_add_right_one (x : BoolW) : x + (1 : BoolW) = 1 := by revert x; decide
private theorem boolw_zero_ne_one : (0 : BoolW) ≠ 1 := by decide

/-- Blueprint `lem:support-hom-iff` (support readout is a homomorphism iff
zerosumfree and no zero divisors): for a nontrivial semiring `S`, the support
readout `supp` (Definition `def:support-readout`) preserves `0`, `1`, `+`,
and `*` exactly when `S` is **zerosumfree** (`a + b = 0 → a = 0 ∧ b = 0`)
and has **no zero divisors** (`a * b = 0 → a = 0 ∨ b = 0`). -/
theorem support_hom_iff {S : Type*} [Semiring S] [DecidableEq S] [Nontrivial S] :
    (supp (0 : S) = 0 ∧ supp (1 : S) = 1 ∧
      (∀ a b : S, supp (a + b) = supp a + supp b) ∧
      (∀ a b : S, supp (a * b) = supp a * supp b))
    ↔ (∀ a b : S, a + b = 0 → a = 0 ∧ b = 0) ∧ (∀ a b : S, a * b = 0 → a = 0 ∨ b = 0) := by
  constructor
  · rintro ⟨-, -, hadd, hmul⟩
    refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
    · by_contra hne
      rw [not_and_or] at hne
      have h1 := hadd a b
      rw [hab, supp_eq_zero_of_eq_zero rfl] at h1
      rcases hne with hne | hne
      · rw [supp_eq_one_of_ne_zero hne, boolw_add_left_one] at h1
        exact boolw_zero_ne_one h1
      · rw [supp_eq_one_of_ne_zero hne, boolw_add_right_one] at h1
        exact boolw_zero_ne_one h1
    · by_contra hne
      rw [not_or] at hne
      have h1 := hmul a b
      rw [hab, supp_eq_zero_of_eq_zero rfl, supp_eq_one_of_ne_zero hne.1,
        supp_eq_one_of_ne_zero hne.2, one_mul] at h1
      exact boolw_zero_ne_one h1
  · rintro ⟨hzsf, hnzd⟩
    refine ⟨supp_eq_zero_of_eq_zero rfl, supp_eq_one_of_ne_zero one_ne_zero, fun a b => ?_,
      fun a b => ?_⟩
    · rcases eq_or_ne a 0 with ha | ha
      · rw [ha, zero_add, supp_eq_zero_of_eq_zero rfl, zero_add]
      · rw [supp_eq_one_of_ne_zero ha]
        have hab_ne : a + b ≠ 0 := fun hab => ha (hzsf a b hab).1
        rw [supp_eq_one_of_ne_zero hab_ne, boolw_add_left_one]
    · rcases eq_or_ne a 0 with ha | ha
      · rw [ha, zero_mul, supp_eq_zero_of_eq_zero rfl, zero_mul]
      · rcases eq_or_ne b 0 with hb | hb
        · rw [hb, mul_zero, supp_eq_zero_of_eq_zero rfl, mul_zero]
        · rw [supp_eq_one_of_ne_zero ha, supp_eq_one_of_ne_zero hb, one_mul]
          have hab_ne : a * b ≠ 0 := fun hab => (hnzd a b hab).elim ha hb
          rw [supp_eq_one_of_ne_zero hab_ne]

/-- Blueprint `lem:support-fails-ring` (support fails additivity on a ring):
on `ℤ`, the support readout `supp` (Definition `def:support-readout`) is not
additive. -/
theorem support_fails_ring : ∃ a b : ℤ, supp (a + b) ≠ supp a + supp b := by
  refine ⟨1, -1, ?_⟩
  decide

end NeSyCat
