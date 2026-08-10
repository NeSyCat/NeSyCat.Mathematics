/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.SemiringMonads.SemiringMonad
import NeSyCat.CategoricalLayer.SemiringMonads.LatticeSemiring

/-!
# The rational mass row, a computable reference evaluator (C3-EXEC item 3)

Blueprint items `def:rational-mass-row` and `thm:rational-mass-row-monad`
(`blueprint/src/content.tex`, §"Examples").

`NeSyCat.MS` (`SemiringMonad.lean`) is `Finsupp`-based: `ret`/`bind` there
carry the `noncomputable` marker because `Finsupp.single` and
`Finsupp.instAddCommMonoid` are themselves `noncomputable` in Mathlib,
independently of which semiring `S` or which value type `X` they are
instantiated at (kernel-verified directly: instantiating `NeSyCat.ret`/
`NeSyCat.bind` at `S := ℚ≥0` and a `DecidableEq`/`Fintype` value type does
not remove the marker, since `noncomputable` attaches to the *declaration*,
not to a particular instantiation — see `.foreman/scratch/C3-EXEC-report.md`
for the transcript). So no amount of choosing a computable scalar semiring
makes `NeSyCat.MS ℚ≥0` itself `#eval`-executable: this is a genuine,
disclosed Mathlib limitation, not something this ticket works around.

What *is* delivered here is the largest honest computable fragment: `QRow`,
a plain-FUNCTION encoding of a finite-support weighted row over a `Fintype`
value type (mirroring the `Bmon`/`BatchMonad.lean` encoding-pin device —
"when Mathlib's own encoding is unusable, use a plain function with its own
hand-proved laws" — the same move made there for a different reason). Every
`QRow` operation below is an ordinary computable `def`, no `noncomputable`
marker anywhere in this file, and `QRow.ret_bind`/`QRow.bind_ret`/
`QRow.bind_assoc` prove it satisfies the identical three monad laws
`thm:semiring-monad-laws` proves for `MS`. `.foreman/scratch/C3-EXEC-report.md`
records `#eval` evidence that a small `QRow` bind chain actually computes.
-/

namespace NeSyCat

open scoped NNRat

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Blueprint `def:rational-mass-row` (Rational mass row, carrier): a
finite-support `ℚ≥0`-weighted row over a `Fintype` value type `X`, encoded
as the plain total function `X → ℚ≥0` (no separate finiteness witness is
needed: `Fintype X` already makes every such function finitely supported).
-/
-- (A1 bijection-law companion of `QRow.bind`, content.tex def:rational-mass-row)
@[blueprint_internal]
def QRow (X : Type) [Fintype X] := X → ℚ≥0

/-- Blueprint `def:rational-mass-row` (Rational mass row, unit): `ret x`,
the row with weight `1` at `x` and `0` elsewhere — computable, unlike
`NeSyCat.ret`, since equality on `X` is decided rather than assumed
classically. -/
-- (A1 bijection-law companion of `QRow.bind`, content.tex def:rational-mass-row)
@[blueprint_internal]
def QRow.ret [DecidableEq X] (x : X) : QRow X :=
  fun y => if y = x then 1 else 0

/-- Blueprint `def:rational-mass-row` (Rational mass row, bind): `(f bind
k)(y) := Σ_x f(x) * k(x)(y)`, a `Finset.sum` over `X`'s (finite, `Fintype`)
whole carrier rather than `Finsupp.sum` over a separately-tracked support —
the same formula as `NeSyCat.bind_apply`'s displayed identity for `MS`, but
computable end to end. -/
def QRow.bind (f : QRow X) (k : X → QRow Y) : QRow Y :=
  fun y => ∑ x, f x * k x y

/-- Blueprint `thm:rational-mass-row-monad` (left unit): `QRow.bind
(QRow.ret x) k = k x`. -/
-- (A1 bijection-law companion of `QRow_monad_laws`, the one name
-- content.tex thm:rational-mass-row-monad cites)
@[blueprint_internal]
theorem QRow.ret_bind [DecidableEq X] (x : X) (k : X → QRow Y) :
    QRow.bind (QRow.ret x) k = k x := by
  funext y
  unfold QRow.bind QRow.ret
  simp [Finset.sum_ite_eq']

/-- Blueprint `thm:rational-mass-row-monad` (associativity):
`QRow.bind (QRow.bind f k) l = QRow.bind f (fun x => QRow.bind (k x) l)`.
The crux is the INTERCHANGE of the two summations, `Finset.sum_comm`,
performed in the open here: `Finset.sum_mul` distributes `l y z` into the
inner sum, `Finset.sum_comm` swaps the `y`- and `x`-summations,
`Finset.mul_sum` pulls `f x` back out, and `ring` reassociates the triple
product. `semiring_monad_laws`/`bind_assoc` prove the same law for `MS`
from the same three ingredients (distributivity, interchange,
associativity of `*`) but by a different route: there the sums run against
a tracked support and the interchange is packaged inside
`Finsupp.sum_sum_index`/`Finsupp.sum_smul_index`/`Finsupp.smul_sum`, so it
never appears as a step of its own. Not "the same shape" of proof, the
same mathematics differently assembled (content.tex says so too, after
thm:rational-mass-row-monad's proof). -/
-- (A1 bijection-law companion of `QRow_monad_laws`, the one name
-- content.tex thm:rational-mass-row-monad cites)
@[blueprint_internal]
theorem QRow.bind_assoc (f : QRow X) (k : X → QRow Y) (l : Y → QRow Z) :
    QRow.bind (QRow.bind f k) l = QRow.bind f (fun x => QRow.bind (k x) l) := by
  funext z
  unfold QRow.bind
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine congrArg Finset.univ.sum (funext fun x => ?_)
  rw [Finset.mul_sum]
  refine congrArg Finset.univ.sum (funext fun y => ?_)
  ring

/-- Blueprint `thm:rational-mass-row-monad` (Rational mass row monad
laws): `(QRow, QRow.ret, QRow.bind)` is a monad, the same three laws
`thm:semiring-monad-laws` proves for `MS`. The right unit law is folded
inline (trivial, single-purpose), matching `semiring_monad_laws`'s own
calibrated-reuse fold of the identical clause. -/
theorem QRow_monad_laws [DecidableEq X] :
    (∀ (x : X) (k : X → QRow Y), QRow.bind (QRow.ret x) k = k x) ∧
      (∀ f : QRow X, QRow.bind f QRow.ret = f) ∧
      (∀ (f : QRow X) (k : X → QRow Y) (l : Y → QRow Z),
        QRow.bind (QRow.bind f k) l = QRow.bind f (fun x => QRow.bind (k x) l)) := by
  refine ⟨QRow.ret_bind, ?_, QRow.bind_assoc⟩
  intro f
  funext y
  unfold QRow.bind QRow.ret
  simp [Finset.sum_ite_eq]

end NeSyCat
