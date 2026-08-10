/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.SemiringMonads.LatticeSemiring
import NeSyCat.CategoricalLayer.SemiringMonads.LogIso

/-!
# The gradient semiring

Blueprint items `def:gradient-semiring`, `lem:gradient-semiring-laws`,
`inst:gradsemiring-mass`, and `inst:gradsemiring-log`
(`blueprint/src/content.tex`, §"Semiring weight monads", C3-TL-A; see that
section's own citation comment for the Eisner/Domingos provenance of
`def:gradient-semiring`).

The gradient semiring pairs a value `a` with its derivative `da`, adding
componentwise and multiplying by the Leibniz rule
`(a,da) ⊗ (b,db) = (ab, a·db + da·b)`. This is exactly Mathlib's dual
numbers `DualNumber S = TrivSqZeroExt S S`: its
`TrivSqZeroExt.commSemiring` instance already supplies every semiring law
for free once `S` itself is a commutative semiring, so `GradSemiring` is
defined here as a plain name for `DualNumber S`, not a fresh structure. The
first-coordinate projection `TrivSqZeroExt.fst` is then a semiring
homomorphism, and the second coordinate obeys the Leibniz rule on the nose
(`TrivSqZeroExt.fst_mul`/`DualNumber.snd_mul`, background machinery cited
as steps, not restated).
-/

namespace NeSyCat

/-- Blueprint `def:gradient-semiring`: the **gradient semiring** on a
commutative semiring `S` pairs a value with its derivative, carrier `S × S`
with `(a,da) ⊕ (b,db) := (a+b, da+db)` and
`(a,da) ⊗ (b,db) := (ab, a·db + da·b)`. Identified with Mathlib's dual
numbers `DualNumber S = TrivSqZeroExt S S`. -/
abbrev GradSemiring (S : Type*) := DualNumber S

/-- Blueprint `lem:gradient-semiring-laws`: on a commutative semiring `S`,
the first projection `TrivSqZeroExt.fst : GradSemiring S → S` is a semiring
homomorphism (preserves `0`, `1`, `+`, `*`), and the second coordinate obeys
the Leibniz rule
`(a,da) ⊗ (b,db) → a·db + da·b` under multiplication. -/
theorem gradient_semiring_laws {S : Type*} [CommSemiring S] :
    ((0 : GradSemiring S).fst = 0) ∧ ((1 : GradSemiring S).fst = 1) ∧
      (∀ a b : GradSemiring S, (a + b).fst = a.fst + b.fst) ∧
      (∀ a b : GradSemiring S, (a * b).fst = a.fst * b.fst) ∧
      (∀ a b : GradSemiring S, (a * b).snd = a.fst * b.snd + b.fst * a.snd) :=
  ⟨TrivSqZeroExt.fst_zero, TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul,
    fun a b => by rw [DualNumber.snd_mul, mul_comm b.fst a.snd]⟩

open scoped NNReal

/-- Blueprint `inst:gradsemiring-mass` (mass row): the gradient semiring
over the mass row `ℝ≥0` (Instance `inst:massS-latcsrng`), a `CommSemiring`
by `TrivSqZeroExt.commSemiring` at `S := ℝ≥0`. -/
instance instCommSemiringGradSemiringMass : CommSemiring (GradSemiring ℝ≥0) :=
  inferInstance

/-- Blueprint `inst:gradsemiring-log` (log row): the gradient semiring over
the log row `LogS` (Instance `inst:logS-latcsrng`), a `CommSemiring` by
`TrivSqZeroExt.commSemiring` at `S := LogS`. -/
noncomputable instance instCommSemiringGradSemiringLog : CommSemiring (GradSemiring LogS) :=
  inferInstance

end NeSyCat
