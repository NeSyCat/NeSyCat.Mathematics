/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib

/-!
# The semiring monad `MS S`

Blueprint items `def:semiring-monad` and `thm:semiring-monad-laws`
(`blueprint/src/content.tex`, §"Semiring weight monads", `[NeSy26, App. A]`).

For a commutative semiring `S`, `MS S X` is the type of finitely supported
functions `X → S`, realized as Mathlib's `Finsupp` type `X →₀ S` (used here
as background finite-support machinery: the monad structure itself is stated
and proved by hand below, not cited from an existing Mathlib instance — no
`Monad`/`bind` instance for `Finsupp` of this shape exists upstream). The
three monad laws (`ret_bind`, `bind_ret`, `bind_assoc`) are proved directly
from `Finsupp.sum`/scalar-action lemmas, matching the blueprint's proof
sketch: the two unit laws each use only a unit law of `S`, and associativity
of `bind` expands, on both sides, to a double sum over `S` rearranged by
associativity/commutativity of `+` (`Finsupp.sum_sum_index`, "addition
marginalises") together with associativity of `*` (`mul_smul`, "multiplication
chains") — `Finsupp.sum_smul_index`/`Finsupp.smul_sum` are exactly where
distributivity of `*` over `+` does the work of matching up the two
nestings, i.e. "distributivity is bind associativity".

`Tens X := MS ℝ≥0 X` instantiates the tensor monad. The `LogTens` abbrev
(`MS` at the log semiring) is deliberately **not** provided here: per the
blueprint, the log semiring itself only arrives by transporting the mass
semiring along the log isomorphism (`lem:log-iso`), which is ticket C1-T3's
job — the same deferral `NeSyCat/Monad/LatticeSemiring.lean` records for the
log lattice-semiring instance, not this one.
-/

namespace NeSyCat

/-- Blueprint `def:semiring-monad` (Semiring monad): for a commutative
semiring `S`, `MS S X` is the type of finitely supported functions
`X → S` (a finitely-supported `S`-weighted formal combination of elements of
`X`), realized as Mathlib's `Finsupp` type `X →₀ S`. -/
abbrev MS (S : Type*) [CommSemiring S] (X : Type*) := X →₀ S

variable {S : Type*} [CommSemiring S] {X Y Z : Type*}

/-- Blueprint `def:semiring-monad` (Semiring monad, unit): `ret x := δ_x`,
the indicator function that is `1` at `x` and `0` elsewhere. -/
noncomputable def ret (x : X) : MS S X := Finsupp.single x 1

/-- Blueprint `def:semiring-monad` (Semiring monad, bind): `(f bind k)(y) :=
⊕_x f(x) ⊗ k(x)(y)`, a finite sum over the (finite) support of `f`, realized
as `Finsupp.sum` applied to the pointwise `S`-scalar action `w • k x` on
`MS S Y`; `bind_apply` below unfolds this to the displayed pointwise
formula, matrix multiplication over `S`. -/
noncomputable def bind (f : MS S X) (k : X → MS S Y) : MS S Y :=
  f.sum fun x w => w • k x

/-- The `bind` of `def:semiring-monad` unfolds pointwise to the blueprint's
matrix-multiplication formula `(f bind k)(y) = Σ_x f(x) ⊗ k(x)(y)` (a finite
sum over `f`'s support, `⊗` being `S`'s multiplication). -/
theorem bind_apply (f : MS S X) (k : X → MS S Y) (y : Y) :
    bind f k y = f.sum fun x w => w * k x y := by
  simp [bind, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Blueprint `thm:semiring-monad-laws`, left unit law: `ret x bind k = k x`,
using only the unit law `1 • k x = k x` of `S`. -/
theorem ret_bind (x : X) (k : X → MS S Y) : bind (ret x) k = k x := by
  unfold bind ret
  rw [Finsupp.sum_single_index (zero_smul S (k x))]
  exact one_smul S (k x)

/-- Blueprint `thm:semiring-monad-laws`, right unit law: `f bind ret = f`,
using only the unit law `w * 1 = w` of `S` (via `Finsupp.smul_single'` and
`Finsupp.sum_single`). -/
theorem bind_ret (f : MS S X) : bind f ret = f := by
  unfold bind ret
  have hpt : (fun (x : X) (w : S) => w • Finsupp.single x (1 : S)) =
      fun (x : X) (w : S) => Finsupp.single x w := by
    funext x w
    rw [Finsupp.smul_single', mul_one]
  rw [hpt]
  exact Finsupp.sum_single f

/-- Blueprint `thm:semiring-monad-laws`, associativity: `(f bind k) bind l =
f bind (fun x => k x bind l)`. The double sum on each side is rearranged
into the other order by `Finsupp.sum_sum_index` (associativity/commutativity
of `⊕`, "addition marginalises") together with `Finsupp.sum_smul_index` and
`Finsupp.smul_sum` reduced, pointwise, to `mul_smul` (associativity of `⊗`,
"multiplication chains" — distributivity of `⊗` over `⊕` is exactly what
lets the two nestings of sums agree, "distributivity is bind
associativity"). -/
theorem bind_assoc (f : MS S X) (k : X → MS S Y) (l : Y → MS S Z) :
    bind (bind f k) l = bind f (fun x => bind (k x) l) := by
  unfold bind
  rw [Finsupp.sum_sum_index (fun y => zero_smul S (l y))
      (fun y v₁ v₂ => add_smul v₁ v₂ (l y))]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.sum_smul_index (fun y => zero_smul S (l y)), Finsupp.smul_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [mul_smul]

/-! ### The tensor-monad instantiation -/

open scoped NNReal

/-- Blueprint `thm:semiring-monad-laws` instance: the tensor monad
`Tmon := MS(mass)`, i.e. `MS` at the mass semiring `ℝ≥0`. -/
abbrev Tens (X : Type*) := MS ℝ≥0 X

end NeSyCat
