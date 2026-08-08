/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.Monad.SemiringMonad

/-!
# The distribution monad `Dist`

Blueprint item `def:dist-monad`
(`blueprint/src/content.tex`, §"Semiring weight monads", `[NeSy26, App. A]`).

The **distribution monad** `Dist X` is the mass-one submonad of the mass
semiring monad `MS ℝ≥0 X = Tens X`: those weight functions whose total mass
sums to `1`. It is realized here as a `Subtype` of `MS ℝ≥0 X`, carrying its
own `pure`/`bind` built by restricting `MS ℝ≥0`'s `ret`/`bind` to the
mass-one slice, justified by the two closure lemmas `ret_mass_one` and
`bind_mass_one` — the latter is exactly the blueprint's displayed Fubini
computation, `∑_y (ρ >>= k)(y) = ∑_y ∑_x ρ(x) k(x)(y) = ∑_x ρ(x) ∑_y k(x)(y)
= ∑_x ρ(x)·1 = 1`, proved here via `Finsupp.sum` rearrangement lemmas
(`Finsupp.sum_sum_index` for the Fubini step, `Finsupp.sum_smul_index` and
`Finsupp.mul_sum` for factoring `ρ(x)` out of the inner sum).

**Not** Mathlib's `PMF`: Mathlib's probability-mass-function type `PMF α`
carries a *countable*-support real-valued measure (`α →∞[Set.univ] ℝ≥0∞`,
built over `ENNReal` and Mathlib's `MeasureTheory` machinery), whereas `Dist`
here is the *finitely*-supported mass-one slice of the semiring monad `MS
ℝ≥0` of `NeSyCat/Monad/SemiringMonad.lean` (a `Finsupp`, `X →₀ ℝ≥0`, with no
measure-theoretic apparatus at all). The two types serve analogous
mathematical roles (a probability distribution on `X`) but are genuinely
different constructions with different carriers and different closure
properties (finite vs. countable support); `PMF` is background/comparison
only here, never substituted for `Dist`.
-/

namespace NeSyCat

open scoped NNReal

variable {X Y : Type*}

/-- Blueprint `def:dist-monad` (Distribution monad): `Dist X` is the
mass-one subset of `MS ℝ≥0 X = Tens X`, i.e. those finitely-supported
weight functions `ρ : X →₀ ℝ≥0` whose total mass `∑_x ρ(x)` (realized as
`Finsupp.sum ρ (fun _ w => w)`, the sum of all of `ρ`'s values) is exactly
`1`. -/
def Dist (X : Type*) := {ρ : MS ℝ≥0 X // ρ.sum (fun _ w => w) = 1}

/-- Blueprint `def:dist-monad` (closure under `ret`): the point mass
`ret x = δ_x` has total mass `1` — `δ_x(x) = 1` and every other value is
`0`, so the sum collapses to the single value `1` (`Finsupp.sum_single_index`,
using only that the summand function vanishes at `0`). -/
theorem ret_mass_one (x : X) : (ret x : MS ℝ≥0 X).sum (fun _ w => w) = 1 := by
  unfold ret
  exact Finsupp.sum_single_index rfl

/-- Blueprint `def:dist-monad` (closure under `bind`, the Fubini
computation): if `ρ` has mass `1` and `k x` has mass `1` for every `x`, then
`ρ >>= k` has mass `1`,
\[
  \sum_y (\rho \bind k)(y) = \sum_y\sum_x \rho(x)\,k(x)(y)
  = \sum_x \rho(x) \sum_y k(x)(y) = \sum_x \rho(x)\cdot 1 = 1.
\]
The middle step (swapping the order of the double sum) is
`Finsupp.sum_sum_index`; factoring `ρ(x)` out of the inner sum uses
`Finsupp.sum_smul_index` (unfolding the scalar action `w • k x`) together
with `Finsupp.mul_sum` (pulling the scalar `ρ(x)` out of `Finsupp.sum`). -/
theorem bind_mass_one {ρ : MS ℝ≥0 X} (hρ : ρ.sum (fun _ w => w) = 1)
    {k : X → MS ℝ≥0 Y} (hk : ∀ x, (k x).sum (fun _ w => w) = 1) :
    (bind ρ k).sum (fun _ w => w) = 1 := by
  unfold bind
  rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  have hstep : (fun x (w : ℝ≥0) => (w • k x).sum (fun _ w' => w'))
      = fun x w => w * (k x).sum (fun _ w' => w') := by
    funext x w
    rw [Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]
  rw [hstep]
  simp_rw [hk, mul_one]
  exact hρ

/-! ### `Dist`'s own monad structure, restricted from `MS ℝ≥0` -/

namespace Dist

variable {X Y : Type*}

/-- Blueprint `def:dist-monad` (`Dist`'s unit): `ret` restricted to the
mass-one subtype, well-defined by `ret_mass_one`. -/
noncomputable def pure (x : X) : Dist X := ⟨ret x, ret_mass_one x⟩

/-- Blueprint `def:dist-monad` (`Dist`'s bind): `bind` restricted to the
mass-one subtype, well-defined by `bind_mass_one`. -/
noncomputable def bind (ρ : Dist X) (k : X → Dist Y) : Dist Y :=
  ⟨NeSyCat.bind ρ.1 (fun x => (k x).1), bind_mass_one ρ.2 (fun x => (k x).2)⟩

end Dist

end NeSyCat
