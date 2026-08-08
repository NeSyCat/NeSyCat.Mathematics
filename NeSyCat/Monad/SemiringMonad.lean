/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib

/-!
# The semiring monad `MS S`

Blueprint items `def:semiring-monad`, `thm:semiring-monad-laws`, and
`thm:semiring-monad-commutative`
(`blueprint/src/content.tex`, §"Semiring weight monads", `[NeSy26, App. A]`).

For a semiring `S` (not assumed commutative), `MS S X` is the type of
finitely supported functions `X → S`, realized as Mathlib's `Finsupp` type
`X →₀ S` (used here as background finite-support machinery: the monad
structure itself is stated and proved by hand below, not cited from an
existing Mathlib instance — no `Monad`/`bind` instance for `Finsupp` of this
shape exists upstream). The three monad laws (`ret_bind`, `bind_ret`,
`bind_assoc`) are proved directly from `Finsupp.sum`/scalar-action lemmas,
matching the blueprint's proof sketch: the two unit laws each use only a
unit law of `S`, and associativity of `bind` expands, on both sides, to a
double sum over `S` rearranged by associativity of `+`
(`Finsupp.sum_sum_index`, "addition marginalises") together with
associativity of `*` (`mul_smul`, "multiplication chains") —
`Finsupp.sum_smul_index`/`Finsupp.smul_sum` are exactly where distributivity
of `*` over `+` does the work of matching up the two nestings, i.e.
"distributivity is bind associativity". None of the three monad laws uses
`mul_comm` at any step — this is exactly what makes them hold for a general
(possibly noncommutative) semiring, not only a commutative one: unit laws
need only unit laws, and `bind`-associativity needs distributivity,
`⊗`-associativity, and `⊕`-commutativity/associativity, never `⊗`-commutativity.

Commutativity of `S` becomes relevant only one level up, for the *monad's
own* commutativity (in the technical, monad-theoretic sense: whether the two
double-strength/interchange maps `dstL`, `dstR` — Definition below — agree).
`thm:semiring-monad-commutative` proves this is exactly `S`'s own
commutativity: `dstL = dstR` for every `X Y f g` iff `S` is commutative
(Kock; Coumans–Jacobs Lem.~23).

`Tens X := MS ℝ≥0 X` instantiates the tensor monad. The `LogTens` abbrev
(`MS` at the log semiring) is deliberately **not** provided here: per the
blueprint, the log semiring itself only arrives by transporting the mass
semiring along the log isomorphism (`lem:log-iso`), which is ticket C1-T3's
job — the same deferral `NeSyCat/Monad/LatticeSemiring.lean` records for the
log lattice-semiring instance, not this one.
-/

namespace NeSyCat

/-- Blueprint `def:semiring-monad` (Semiring monad): for a semiring `S`,
`MS S X` is the type of finitely supported functions `X → S` (a
finitely-supported `S`-weighted formal combination of elements of `X`),
realized as Mathlib's `Finsupp` type `X →₀ S`. `S` is not assumed
commutative: see the module doc comment above and
`thm:semiring-monad-commutative` for exactly where `⊗`-commutativity
becomes relevant (the monad's own commutativity, not its underlying monad
laws). -/
abbrev MS (S : Type*) [Semiring S] (X : Type*) := X →₀ S

variable {S : Type*} [Semiring S] {X Y Z : Type*}

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

/-- Blueprint `def:semiring-monad` (bind_apply): `bind` unfolds pointwise to
the blueprint's matrix-multiplication formula `(f bind k)(y) = Σ_x f(x) ⊗
k(x)(y)` (a finite sum over `f`'s support, `⊗` being `S`'s multiplication,
in this left-to-right order — no step needs `⊗` to commute). -/
theorem bind_apply (f : MS S X) (k : X → MS S Y) (y : Y) :
    bind f k y = f.sum fun x w => w * k x y := by
  simp [bind, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Blueprint `thm:semiring-monad-laws` (ret_bind): the left unit law,
`ret x bind k = k x`, using only the unit law `1 • k x = k x` of `S`. -/
theorem ret_bind (x : X) (k : X → MS S Y) : bind (ret x) k = k x := by
  unfold bind ret
  rw [Finsupp.sum_single_index (zero_smul S (k x))]
  exact one_smul S (k x)

/-- Blueprint `thm:semiring-monad-laws` (bind_ret): the right unit law,
`f bind ret = f`, using only the unit law `w * 1 = w` of `S` (via
`Finsupp.smul_single'` and `Finsupp.sum_single`). -/
theorem bind_ret (f : MS S X) : bind f ret = f := by
  unfold bind ret
  have hpt : (fun (x : X) (w : S) => w • Finsupp.single x (1 : S)) =
      fun (x : X) (w : S) => Finsupp.single x w := by
    funext x w
    rw [Finsupp.smul_single', mul_one]
  rw [hpt]
  exact Finsupp.sum_single f

/-- Blueprint `thm:semiring-monad-laws` (bind_assoc): associativity,
`(f bind k) bind l = f bind (fun x => k x bind l)`. The double sum on each
side is rearranged into the other order by `Finsupp.sum_sum_index`
(associativity/commutativity of `⊕`, "addition marginalises") together with
`Finsupp.sum_smul_index` and `Finsupp.smul_sum` reduced, pointwise, to
`mul_smul` (associativity of `⊗`, "multiplication chains" — distributivity
of `⊗` over `⊕` is exactly what lets the two nestings of sums agree,
"distributivity is bind associativity"). No step uses `⊗`-commutativity, so
this holds for a general (possibly noncommutative) semiring `S`. -/
theorem bind_assoc (f : MS S X) (k : X → MS S Y) (l : Y → MS S Z) :
    bind (bind f k) l = bind f (fun x => bind (k x) l) := by
  unfold bind
  rw [Finsupp.sum_sum_index (fun y => zero_smul S (l y))
      (fun y v₁ v₂ => add_smul v₁ v₂ (l y))]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.sum_smul_index (fun y => zero_smul S (l y)), Finsupp.smul_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [mul_smul]

/-! ### `thm:semiring-monad-commutative`: the double-strength/interchange maps

A monad `M` is *commutative* (in the technical, monad-theoretic sense) when
its two double-strength maps `M X × M Y → M (X × Y)` — bind the first
argument then the second, versus bind the second then the first — agree.
For `MS S` these are `dstL`/`dstR` below; `thm:semiring-monad-commutative`
shows they agree for every `X Y f g` iff `S` itself is commutative. This is
independent of the monad laws proved above (`ret_bind`/`bind_ret`/
`bind_assoc` hold for every semiring `S`): commutativity of `⊗` is not
needed to make `MS S` a monad, only to make that monad *commutative*. -/

/-- A small local helper: a `Finsupp.sum` guarded by `x = a`, whose summand
vanishes at `0`, collapses unconditionally to the value at `a` (whether or
not `a` is in the support — Mathlib's `Finsupp.sum_ite_eq'` leaves this
guarded by `a ∈ f.support`, which `hb` removes). Used twice in
`dstL_apply`/`dstR_apply` below, once for each nested `Finsupp.sum`. -/
private theorem sum_ite_eq_of_apply_zero {α M N : Type*} [Zero M] [AddCommMonoid N]
    [DecidableEq α] (h : α →₀ M) (a : α) (b : α → M → N) (hb : b a 0 = 0) :
    (h.sum fun x v => if x = a then b x v else 0) = b a (h a) := by
  rw [Finsupp.sum_ite_eq']
  by_cases ha : a ∈ h.support
  · rw [if_pos ha]
  · rw [if_neg ha, Finsupp.notMem_support_iff.mp ha, hb]

/-- Blueprint `thm:semiring-monad-commutative` (dstL): the left-to-right
double strength / interchange map on `MS S` — bind `f` before `g` — with
pointwise weight `f x * g y` (`dstL_apply` below). -/
noncomputable def dstL (f : MS S X) (g : MS S Y) : MS S (X × Y) :=
  bind f (fun x => bind g (fun y => ret (x, y)))

/-- Blueprint `thm:semiring-monad-commutative` (dstR): the right-to-left
double strength / interchange map on `MS S` — bind `g` before `f` — with
pointwise weight `g y * f x` (`dstR_apply` below). -/
noncomputable def dstR (f : MS S X) (g : MS S Y) : MS S (X × Y) :=
  bind g (fun y => bind f (fun x => ret (x, y)))

/-- Blueprint `thm:semiring-monad-commutative` (dstL_apply): `dstL` unfolds
pointwise to `f x * g y`, `⊗` in the order "first bound, first multiplied". -/
theorem dstL_apply (f : MS S X) (g : MS S Y) (x : X) (y : Y) :
    dstL f g (x, y) = f x * g y := by
  classical
  unfold dstL
  rw [bind_apply]
  have inner : ∀ x' : X, bind g (fun y' => ret (x', y')) (x, y) =
      if x' = x then g y else 0 := by
    intro x'
    rw [bind_apply]
    have hpt : (fun y' (v : S) => v * (ret (x', y') : MS S (X × Y)) (x, y))
        = (fun y' v => if y' = y then (if x' = x then v else 0) else 0) := by
      funext y' v
      simp only [ret, Finsupp.single_apply, Prod.mk.injEq]
      by_cases hy : y' = y <;> by_cases hx : x' = x <;> simp [hy, hx]
    rw [hpt]
    exact sum_ite_eq_of_apply_zero g y (fun _ v => if x' = x then v else 0) (by simp)
  simp_rw [inner, mul_ite, mul_zero]
  exact sum_ite_eq_of_apply_zero f x (fun _ w => w * g y) (by rw [zero_mul])

/-- Blueprint `thm:semiring-monad-commutative` (dstR_apply): `dstR` unfolds
pointwise to `g y * f x`, `⊗` in the order "first bound, first multiplied". -/
theorem dstR_apply (f : MS S X) (g : MS S Y) (x : X) (y : Y) :
    dstR f g (x, y) = g y * f x := by
  classical
  unfold dstR
  rw [bind_apply]
  have inner : ∀ y' : Y, bind f (fun x' => ret (x', y')) (x, y) =
      if y' = y then f x else 0 := by
    intro y'
    rw [bind_apply]
    have hpt : (fun x' (v : S) => v * (ret (x', y') : MS S (X × Y)) (x, y))
        = (fun x' v => if x' = x then (if y' = y then v else 0) else 0) := by
      funext x' v
      simp only [ret, Finsupp.single_apply, Prod.mk.injEq]
      by_cases hx : x' = x <;> by_cases hy : y' = y <;> simp [hx, hy]
    rw [hpt]
    exact sum_ite_eq_of_apply_zero f x (fun _ v => if y' = y then v else 0) (by simp)
  simp_rw [inner, mul_ite, mul_zero]
  exact sum_ite_eq_of_apply_zero g y (fun _ w => w * f x) (by rw [zero_mul])

/-- Blueprint `thm:semiring-monad-commutative` (Semiring monad
commutativity): `MS S` is a *commutative* monad — its two double-strength
maps `dstL`/`dstR` agree, for every `X Y f g` — if and only if `S` itself is
commutative.

Forward: `⊗` commuting makes the two orders of independent binding agree
pointwise, `f x * g y = g y * f x` (`dstL_apply`/`dstR_apply`).

Converse: testing at `X = Y = PUnit` with the two point masses
`single ⟨⟩ a`, `single ⟨⟩ b` recovers `a * b = b * a` from `dstL = dstR`
alone (even just this one instance of the right-hand side, not the full
`∀ X Y`) — so no weaker hypothesis than full commutativity of `⊗` suffices.
The monad-level and semiring-level notions of commutativity coincide
exactly: this is Kock's theorem that a commutative-monad structure on a
"weighting" monad corresponds to commutativity of the weights (Coumans--
Jacobs Lem.~23: the two double-strengths agree iff `S` is commutative).

This is exactly where `⊗`-commutativity is first needed in this file: not
for the monad laws (`ret_bind`/`bind_ret`/`bind_assoc`, proved above for a
general semiring), but for the monad's own commutativity. Downstream, it is
the monad's commutativity — not the bare monad laws — that the lifted
connectives of chapter 2 (`def:lifted-connective`) and the
order-irrelevance of independent binds in the `Do`-notation semantics
(`def:semantics`) both rely on. -/
theorem dst_comm_iff :
    (∀ a b : S, a * b = b * a) ↔
      (∀ (X Y : Type*) (f : MS S X) (g : MS S Y), dstL f g = dstR f g) := by
  constructor
  · intro hcomm X Y f g
    apply Finsupp.ext
    rintro ⟨x, y⟩
    rw [dstL_apply, dstR_apply, hcomm]
  · intro h a b
    have hpt :
        dstL (Finsupp.single (PUnit.unit) a) (Finsupp.single (PUnit.unit) b)
            (PUnit.unit, PUnit.unit) =
          dstR (Finsupp.single (PUnit.unit) a) (Finsupp.single (PUnit.unit) b)
            (PUnit.unit, PUnit.unit) := by
      rw [h]
    rwa [dstL_apply, dstR_apply, Finsupp.single_eq_same, Finsupp.single_eq_same] at hpt

/-- Blueprint `thm:semiring-monad-commutative` (dst_comm): the forward
direction of `dst_comm_iff`, specialized via a `CommSemiring` instance for
direct use (e.g. on `Tens := MS ℝ≥0`, whose weight semiring `ℝ≥0` is
commutative, or `LatCSRng`'s derived `CommSemiring` instances from
`NeSyCat/Monad/LatticeSemiring.lean`). -/
theorem dst_comm {S : Type*} [CommSemiring S] {X Y : Type*} (f : MS S X) (g : MS S Y) :
    dstL f g = dstR f g :=
  dst_comm_iff.mp mul_comm X Y f g

/-! ### The tensor-monad instantiation -/

open scoped NNReal

/-- Blueprint `thm:semiring-monad-laws` instance: the tensor monad
`Tmon := MS(mass)`, i.e. `MS` at the mass semiring `ℝ≥0`. -/
abbrev Tens (X : Type*) := MS ℝ≥0 X

end NeSyCat
