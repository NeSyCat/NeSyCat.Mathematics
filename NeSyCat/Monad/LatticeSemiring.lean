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

`LatSRng` ("lattice-semiring") is stated at its natural generality: an
arbitrary (not necessarily commutative) semiring `S` equipped with a
compatible lattice order, `⊕` and `⊗` each monotone in *both* arguments
separately. `LatCSRng` ("lattice-comm-semiring") is the commutative
refinement (adding `mul_comm`); `BLatSRng`/`BLatCSRng` are the *bounded*
variants, additionally carrying an in-carrier `⊥`/`⊤`. Plain (unbounded,
possibly noncommutative) semirings are just Mathlib's `Semiring` directly —
no `SRng` alias is introduced, since aliasing a Mathlib class only hurts
instance search for no benefit.

The library's three running instances (Boolean, mass, log) are all
commutative; Boolean is additionally bounded (`⊥ = 0`, `⊤ = 1` in-carrier),
while mass and log are not (no in-carrier `⊤` without adjoining `∞`). So
`BoolW` is built as a `BLatCSRng` (inheriting `LatCSRng`, `LatSRng`,
`CommSemiring`, `BoundedOrder` for free), while `ℝ≥0` is built only as a
`LatCSRng`.

This file delivers two of the three running instances (Boolean, mass); the
third (log) is delivered separately, in `NeSyCat/Monad/LogIso.lean`
(`instLatCSRngLogS`), by transport along the log isomorphism, see the note
below. It also proves that
`([0,1], p ⊕ q := p+q-pq, ·, 0, 1)` is *not* a semiring, witnessing the
failure of distributivity concretely.
-/

namespace NeSyCat

/-- Blueprint `def:lattice-semiring` (Lattice-semiring, general form): a
**lattice-semiring** (`LatSRng`) is a semiring `(S, ⊕, ⊗, 0, 1)` (not assumed
commutative) equipped with a lattice order `≤` on the carrier `S` (a meet
`⊓` and a join `⊔` exist for every pair of elements, with bounds `⊥`, `⊤`
existing where indicated — see `BLatSRng` below for the bounded refinement)
such that `⊕` (`+`) and `⊗` (`*`) are each monotone in *every* argument with
respect to `≤`.

Both directions of `⊗`-monotonicity (`mul_le_mul_left`, `mul_le_mul_right`)
are taken as independent fields: without `mul_comm`, neither direction of a
possibly-noncommutative `⊗` determines the other. `⊕`-monotonicity is
likewise carried in both directions (`add_le_add_left`, `add_le_add_right`)
for definitional symmetry with `⊗` — though it is worth recording precisely
what is, and is not, independent data here: because `Semiring.toAddCommMonoid`
already makes `+` commutative for *every* semiring (commutative or not),
`add_le_add_right` is always recoverable from `add_le_add_left` alone (see
`LatSRng.add_le_add_right_of_left` below); it is `mul_le_mul_right` that is
the genuinely independent piece of data distinguishing the general (possibly
noncommutative) class from the commutative refinement `LatCSRng`.

"Left"/"right" here name which side the *fixed* element sits on, matching
this file's already-established convention: `add_le_add_left`/
`mul_le_mul_left` are so named because the fixed element `c` is added/
multiplied *on the left* of the varying term (`c + a ≤ c + b`, `c * a ≤ c * b`);
`add_le_add_right`/`mul_le_mul_right` fix `c` *on the right*
(`a + c ≤ b + c`, `a * c ≤ b * c`). -/
class LatSRng (S : Type*) extends Semiring S, Lattice S where
  /-- `+` is monotone, fixed element on the left. -/
  add_le_add_left : ∀ {a b : S}, a ≤ b → ∀ c : S, c + a ≤ c + b
  /-- `+` is monotone, fixed element on the right. -/
  add_le_add_right : ∀ {a b : S}, a ≤ b → ∀ c : S, a + c ≤ b + c
  /-- `*` is monotone, fixed element on the left. -/
  mul_le_mul_left : ∀ {a b : S}, a ≤ b → ∀ c : S, c * a ≤ c * b
  /-- `*` is monotone, fixed element on the right. -/
  mul_le_mul_right : ∀ {a b : S}, a ≤ b → ∀ c : S, a * c ≤ b * c

namespace LatSRng

variable {S : Type*} [LatSRng S]

/-- Part of C1-T1's original observation, preserved as content in the
generalized class: `add_le_add_right` is derivable from `add_le_add_left`
alone, in *any* `LatSRng` — not only in the commutative refinement below —
because a semiring's addition is unconditionally commutative (`add_comm`,
from `Semiring.toAddCommMonoid`). This makes `add_le_add_right` redundant as
*mathematical content* even though it remains an explicit field of the class
(for definitional symmetry with the genuinely-independent `⊗` pair; contrast
`LatCSRng.mul_le_mul_right_of_left` below). -/
theorem add_le_add_right_of_left {a b : S} (h : a ≤ b) (c : S) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]
  exact add_le_add_left h c

end LatSRng

/-- Blueprint `def:lattice-semiring` (Commutative lattice-semiring): the
commutative refinement of `LatSRng`, adding `mul_comm`. The library's three
running instances (Boolean, mass, log) are all `LatCSRng` in this sense —
`[NeSy26, App.~A]` only ever works with the commutative case, so this is the
class the blueprint's narrative instances actually witness; the general
`LatSRng` above is this library's own generalization (natural-generality
principle), with the commutative case recovered here as a refinement, not a
separate construction. A `CommSemiring S` instance is derived immediately
below (`LatCSRng.toCommSemiring`) so downstream code can use ordinary
`CommSemiring`/`mul_comm` lemmas on any `LatCSRng` without re-deriving
commutativity by hand. -/
class LatCSRng (S : Type*) extends LatSRng S where
  /-- `*` is commutative. -/
  mul_comm : ∀ a b : S, a * b = b * a

/-- Every `LatCSRng` is in particular a `CommSemiring`, built from its
underlying `Semiring` plus its own `mul_comm` field. Kept at low priority so
it never competes with a type's own directly-declared `CommSemiring`
instance (e.g. `ℝ≥0`'s, which this instance would otherwise duplicate)
during instance search. -/
instance (priority := 100) LatCSRng.toCommSemiring
    {S : Type*} [LatCSRng S] : CommSemiring S :=
  { (inferInstance : Semiring S) with mul_comm := LatCSRng.mul_comm }

namespace LatCSRng

variable {S : Type*} [LatCSRng S]

/-- C1-T1's original observation, preserved as content: in the commutative
case, `mul_le_mul_right` is *also* derivable from `mul_le_mul_left` (via
`mul_comm`), exactly mirroring `LatSRng.add_le_add_right_of_left`'s use of
the always-available `add_comm`. So a `LatCSRng` could in principle be
axiomatized from only its two *left*-monotonicity witnesses
(`add_le_add_left`, `mul_le_mul_left`) plus `mul_comm` — both
right-monotonicity fields become theorems, not independent data. The general
`LatSRng` cannot do the analogous thing for `⊗`: without `mul_comm` in hand,
`mul_le_mul_right` is not recoverable from `mul_le_mul_left`, so it
genuinely needs both `⊗`-direction fields as independent hypotheses. -/
theorem mul_le_mul_right_of_left {a b : S} (h : a ≤ b) (c : S) : a * c ≤ b * c := by
  rw [LatCSRng.mul_comm a c, LatCSRng.mul_comm b c]
  exact LatSRng.mul_le_mul_left h c

end LatCSRng

/-- Blueprint `def:lattice-semiring` (Bounded lattice-semiring): the bounded
refinement of `LatSRng`, additionally requiring a `BoundedOrder` (an
in-carrier `⊥` and `⊤`). The mass and log instances are *not* bounded in
this sense (no in-carrier `⊤` without adjoining `∞` externally); the
Boolean instance is (`⊥ = 0 = false`, `⊤ = 1 = true`, see
`BoolW.bot_eq_zero`/`BoolW.top_eq_one` below). -/
class BLatSRng (S : Type*) extends LatSRng S, BoundedOrder S

/-- Blueprint `def:lattice-semiring` (Bounded commutative lattice-semiring):
the bounded refinement of `LatCSRng`, structured in parallel to it —
`BLatCSRng` extends `BLatSRng` and adds its own `mul_comm` field (rather
than also `extends LatCSRng`, which would create two independent `mul_comm`
fields on a diamond). A `LatCSRng S` instance is derived immediately below
(`BLatCSRng.toLatCSRng`), so every `LatCSRng`-level fact (including
`CommSemiring` via `LatCSRng.toCommSemiring`, and
`LatCSRng.mul_le_mul_right_of_left`) is available on any `BLatCSRng` for
free, transitively. -/
class BLatCSRng (S : Type*) extends BLatSRng S where
  /-- `*` is commutative. -/
  mul_comm : ∀ a b : S, a * b = b * a

/-- Every `BLatCSRng` is in particular a `LatCSRng` (dropping boundedness),
built from its underlying `LatSRng` plus its own `mul_comm` field. Kept at
low priority for the same reason as `LatCSRng.toCommSemiring`. -/
instance (priority := 100) BLatCSRng.toLatCSRng
    {S : Type*} [BLatCSRng S] : LatCSRng S :=
  { (inferInstance : LatSRng S) with mul_comm := BLatCSRng.mul_comm }

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
instance : BoundedOrder BoolW := inferInstanceAs (BoundedOrder Bool)

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

/-- `BoolW`'s bottom (`false`, `BoundedOrder.bot`) coincides with its
`0` (also `false`): the Boolean instance's bounds are in-carrier and agree
with the semiring's own additive/multiplicative units, unlike the
unbounded mass/log instances. -/
@[simp] theorem bot_eq_zero : (⊥ : BoolW) = 0 := rfl

/-- `BoolW`'s top (`true`, `BoundedOrder.top`) coincides with its `1`
(also `true`). -/
@[simp] theorem top_eq_one : (⊤ : BoolW) = 1 := rfl

/-- Blueprint `def:lattice-semiring` (Boolean instance): `⊕ = or` is exactly
the lattice join and `⊗ = and` is exactly the lattice meet, so both
directions of monotonicity for both operations, and commutativity, are all
decidable on this finite carrier; `Bool`'s existing bounds (`⊥ = false`,
`⊤ = true`) make `BoolW` the library's one *bounded* running instance. -/
instance instBLatCSRng : BLatCSRng BoolW where
  add_le_add_left h c := sup_le_sup_left h c
  add_le_add_right h c := sup_le_sup_right h c
  mul_le_mul_left h c := inf_le_inf_left c h
  mul_le_mul_right h c := inf_le_inf_right c h
  mul_comm := by decide

end BoolW

/-! ### The mass lattice-semiring instance (`ℝ≥0`)

Assembled entirely from Mathlib's existing `CommSemiring`, `Lattice`, and
order-monotonicity instances on `NNReal` — no algebraic law is reproved
here, only assembled into the `LatCSRng` bundle. The mass carrier has an
in-carrier bottom (`0`) but **no** in-carrier top: the blueprint's `⊤ = ∞`
bound only exists after adjoining `∞` externally, which is not part of this
instance, so `ℝ≥0` is built only at `LatCSRng`, not the bounded `BLatCSRng`. -/

open scoped NNReal

/-- Blueprint `def:lattice-semiring` (mass instance): on `ℝ≥0` (`⊕ = +`,
`⊗ = ·`). `NNReal`'s own `CommSemiring`/`Lattice`/order instances supply
everything except the four monotonicity fields, closed by `gcongr` (both
directions of both operations are monotone on `ℝ≥0`, uniformly). No
`BoundedOrder ℝ≥0` instance is used: `ℝ≥0` has no in-carrier top. -/
noncomputable instance instLatCSRngNNReal : LatCSRng ℝ≥0 where
  add_le_add_left h c := by gcongr
  add_le_add_right h c := by gcongr
  mul_le_mul_left h c := by gcongr
  mul_le_mul_right h c := by gcongr
  mul_comm := mul_comm

/-! The log instance (`lse`, `+`) is deliberately **not** provided here: per
the blueprint it is delivered separately, in `NeSyCat/Monad/LogIso.lean`
(`instLatCSRngLogS`), by transporting the mass instance along the log
isomorphism (`lem:log-iso`). -/

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
