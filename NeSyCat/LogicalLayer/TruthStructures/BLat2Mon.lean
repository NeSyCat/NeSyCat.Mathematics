/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib

/-!
# Two-monoid bounded lattices (`BLat2Mon`)

Blueprint items `def:blat2mon`, `def:blat2cmon`, `def:lin-blat2mon`,
`def:lin-blat2cmon`, `def:dm-structure`, `def:zero-bot`, `def:one-top`,
`def:unit-bounds`, `lem:lin-monotone`, `lem:lin-lax-duals`
(`blueprint/src/content.tex`, §"Truth-value structures", `[NeSy26, App. A]`;
vocabulary from linear logic, Girard 1987).

The lifted connective family of a truth space is *not* a semiring: it is a
bounded lattice carrying two monoids, with no distributivity assumed between
the three structures. This file isolates that shape abstractly.

**Why explicit operation fields, not `Monoid` instances.** A single carrier
here bears *two* independent monoid structures — `(oplus, dzero)` (linear
logic's `⅋`, "or-like") and `(otimes, done)` (linear logic's multiplicative
`⊗`; the field itself is named `otimes`, not `[NeSy26]`'s own `andC`
spelling — USER DECREE 2026-08-09, C2-E4c: the glyph the LaTeX side prints
and the paper's own field name are independent choices, and the field is
renamed to match the operator it denotes one-to-one). No Lean notation
glyph is shipped for either (`oplus`/`otimes` are the plain working names,
C2-E4b — see `NeSyCat/Notation.lean`). Mathlib's
`Monoid` typeclass can be registered at most once per type. So `BLat2Mon`
carries `oplus`/`dzero`/`otimes`/`done` as explicit fields (over an ambient
`[Lattice α] [BoundedOrder α]`, *not* extended — `BoolW` already carries
its own lattice/`BoundedOrder` instances, and extending here would create
diamonds), rather than deriving from two separately-registered `Monoid α`
instances (impossible) or a single `Monoid` (would conflate the two).

De Morgan structure (`DMStructure`) and the unit-bound mixins (`ZeroBot`,
`OneTop`) are likewise classes taken *on top of* an existing `BLat2Mon`
instance, matching the blueprint's own phrasing ("a DM structure *on* a
BLat2Mon"). `ZeroBot`/`OneTop` are `Prop`-classes: they assert a coincidence
between existing data (`dzero = ⊥`, `done = ⊤`), not new data.

Only `def:dm-structure` itself is in scope for this file; the further De
Morgan calculus it entails (`lem:dm-lattice-laws`, `lem:dm-dual-law`,
`lem:dm-unit-swap`, `thm:dm-presentations`, `lem:dm-maps-units`) and the
unit-bounds corollaries (`lem:dualabsorb-decomposition`, `lem:mix`,
`thm:chain-lin`) are left for later tickets.
-/

namespace NeSyCat

/-- Blueprint `def:blat2mon` (Two-monoid bounded lattice): a **BLat2Mon** is
a set carrying a bounded lattice `(⊓, ⊔, ⊥, ⊤)` (via the ambient
`[Lattice α] [BoundedOrder α]`) together with two monoid structures
`(oplus, dzero)` and `(otimes, done)`; unlike a lattice-semiring
(`NeSyCat.LatSRng`), no distributivity of any kind is assumed between the
three structures. Distilled from `[NeSy26, App. A]` (the lifted-connective
family); vocabulary from linear logic (Girard 1987). -/
class BLat2Mon (α : Type*) [Lattice α] [BoundedOrder α] where
  /-- The `oplus`-monoid multiplication (linear logic's `⅋`, "or-like"). -/
  oplus : α → α → α
  /-- The `oplus`-unit (linear logic's `⊥`, the blueprint's bold `0`). -/
  dzero : α
  /-- The `otimes`-monoid multiplication (linear logic's *multiplicative*
  conjunction `⊗`; field renamed `otimes` from `[NeSy26]`'s `andC`
  spelling, C2-E4c — see the linear-logic dictionary table in
  `blueprint/src/content.tex`, §"Truth-value structures"). -/
  otimes : α → α → α
  /-- The `otimes`-unit (linear logic's `1`, the blueprint's bold `1`). -/
  done : α
  oplus_assoc : ∀ p q r, oplus (oplus p q) r = oplus p (oplus q r)
  dzero_oplus : ∀ p, oplus dzero p = p
  oplus_dzero : ∀ p, oplus p dzero = p
  otimes_assoc : ∀ p q r, otimes (otimes p q) r = otimes p (otimes q r)
  done_otimes : ∀ p, otimes done p = p
  otimes_done : ∀ p, otimes p done = p

/-- Blueprint `def:blat2cmon` (Commutative two-monoid bounded lattice): a
**BLat2CMon** is a `BLat2Mon` whose two monoids `(oplus, dzero)` and
`(otimes, done)` are both commutative. -/
class BLat2CMon (α : Type*) [Lattice α] [BoundedOrder α] extends BLat2Mon α where
  oplus_comm : ∀ p q, oplus p q = oplus q p
  otimes_comm : ∀ p q, otimes p q = otimes q p

/-- Blueprint `def:lin-blat2mon` (Linear two-monoid lattice): a
**LinBLat2Mon** is a `BLat2Mon` in which `otimes` preserves finite joins in
each argument and `oplus` preserves finite meets in each argument: binary
(`otimes p (q ⊔ r) = otimes p q ⊔ otimes p r` and its left-argument twin,
dually for `oplus` and `⊓`) and nullary (`otimes p ⊥ = ⊥` annihilation,
`oplus p ⊤ = ⊤` absorption, both two-sided). These are exactly the four
linear distributions of linear logic (`⊗` over `⊕`, `⅋` over `&`, together
with their units), transported along the linear-logic dictionary table of
`blueprint/src/content.tex`, §"Truth-value structures" (Girard 1987). -/
class LinBLat2Mon (α : Type*) [Lattice α] [BoundedOrder α] extends BLat2Mon α where
  /-- `otimes` preserves finite joins in its right argument. -/
  otimes_sup : ∀ p q r, otimes p (q ⊔ r) = otimes p q ⊔ otimes p r
  /-- `otimes` preserves finite joins in its left argument. -/
  sup_otimes : ∀ p q r, otimes (p ⊔ q) r = otimes p r ⊔ otimes q r
  /-- `oplus` preserves finite meets in its right argument. -/
  oplus_inf : ∀ p q r, oplus p (q ⊓ r) = oplus p q ⊓ oplus p r
  /-- `oplus` preserves finite meets in its left argument. -/
  inf_oplus : ∀ p q r, oplus (p ⊓ q) r = oplus p r ⊓ oplus q r
  /-- Annihilation: `otimes` kills `⊥` on the right. -/
  otimes_bot : ∀ p, otimes p ⊥ = ⊥
  /-- Annihilation: `otimes` kills `⊥` on the left. -/
  bot_otimes : ∀ p, otimes ⊥ p = ⊥
  /-- Absorption: `oplus` saturates to `⊤` on the right. -/
  oplus_top : ∀ p, oplus p ⊤ = ⊤
  /-- Absorption: `oplus` saturates to `⊤` on the left. -/
  top_oplus : ∀ p, oplus ⊤ p = ⊤

/-- Blueprint `def:lin-blat2cmon` (Commutative linear two-monoid lattice): a
**LinBLat2CMon** is a `BLat2CMon` satisfying the `LinBLat2Mon` laws (a
commutative `LinBLat2Mon`); Lean flattens the shared `BLat2Mon` parent. -/
class LinBLat2CMon (α : Type*) [Lattice α] [BoundedOrder α]
    extends LinBLat2Mon α, BLat2CMon α

/-- Blueprint `def:dm-structure` (De Morgan structure): a **DM structure**
on a `BLat2Mon` is a map `dneg` satisfying (i) `dneg (dneg p) = p`;
(ii) `p ≤ q → dneg q ≤ dneg p`; (iii)
`dneg (otimes p q) = oplus (dneg q) (dneg p)`. Linear negation (Girard 1987), axiomatized
minimally; the equivalent presentations (antitonicity vs. the lattice
De Morgan law) are compared in `thm:dm-presentations` (out of scope here). -/
class DMStructure (α : Type*) [Lattice α] [BoundedOrder α] [BLat2Mon α] where
  dneg : α → α
  dneg_dneg : ∀ p, dneg (dneg p) = p
  dneg_antitone : ∀ p q : α, p ≤ q → dneg q ≤ dneg p
  dneg_otimes : ∀ p q, dneg (BLat2Mon.otimes p q) = BLat2Mon.oplus (dneg q) (dneg p)

/-- Blueprint `def:zero-bot` (Unit-bound mixin, ZeroBot): for a
`BLat2Mon`, **ZeroBot** demands `dzero = ⊥`. A `Prop`-class: it asserts a
coincidence between already-existing data, not new data. -/
class ZeroBot (α : Type*) [Lattice α] [BoundedOrder α] [BLat2Mon α] : Prop where
  dzero_eq_bot : (BLat2Mon.dzero : α) = ⊥

/-- Blueprint `def:one-top` (Unit-bound mixin, OneTop): for a
`BLat2Mon`, **OneTop** demands `done = ⊤`. Together, `ZeroBot` and `OneTop`
are `UnitBounds`, collapsing the four constants of the blueprint's
introduction (the "Four constants" paragraph, `blueprint/src/content.tex`)
to two. -/
class OneTop (α : Type*) [Lattice α] [BoundedOrder α] [BLat2Mon α] : Prop where
  done_eq_top : (BLat2Mon.done : α) = ⊤

/-- Blueprint `def:unit-bounds` (**UnitBounds**, the conjunction): for a
`BLat2Mon`, `UnitBounds` demands both `ZeroBot` and `OneTop`, collapsing the
four constants of the blueprint's introduction (the "Four constants"
paragraph, `blueprint/src/content.tex`) to two. A trivial alias class
(no new fields beyond its two parents) naming the conjunction the blueprint
itself names, used as a single hypothesis by `thm:chain-lin`(ii) and
`lem:mix` rather than threading `ZeroBot`/`OneTop` separately. -/
class UnitBounds (α : Type*) [Lattice α] [BoundedOrder α] [BLat2Mon α] : Prop
    extends ZeroBot α, OneTop α

section LinearLemmas

open BLat2Mon

variable {α : Type*} [Lattice α] [BoundedOrder α] [LinBLat2Mon α]

/-! ### `lem:lin-monotone`: linearity gives monotonicity

Blueprint proof: if `p ≤ q` then `q = p ⊔ q`, so
`otimes q r = otimes (p ⊔ q) r = otimes p r ⊔ otimes q r ≥ otimes p r`; the other
argument, and `oplus` (via `p = p ⊓ q` and meet-preservation), are dual. Four
argument-versions (fixed element named per the side it sits on, mirroring
`NeSyCat.LatSRng.add_le_add_left`/`add_le_add_right`). -/

/-- Blueprint `lem:lin-monotone` (`otimes` monotone, fixed element on the
left): if `p ≤ q` then `otimes r p ≤ otimes r q`. -/
theorem otimes_le_otimes_left {p q : α} (h : p ≤ q) (r : α) :
    otimes r p ≤ otimes r q := by
  calc otimes r p ≤ otimes r p ⊔ otimes r q := le_sup_left
    _ = otimes r (p ⊔ q) := (LinBLat2Mon.otimes_sup r p q).symm
    _ = otimes r q := by rw [sup_eq_right.mpr h]

/-- Blueprint `lem:lin-monotone` (`otimes` monotone, fixed element on the
right): if `p ≤ q` then `otimes p r ≤ otimes q r`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `otimes_le_otimes_left`, content.tex lem:lin-monotone)
theorem otimes_le_otimes_right {p q : α} (h : p ≤ q) (r : α) :
    otimes p r ≤ otimes q r := by
  calc otimes p r ≤ otimes p r ⊔ otimes q r := le_sup_left
    _ = otimes (p ⊔ q) r := (LinBLat2Mon.sup_otimes p q r).symm
    _ = otimes q r := by rw [sup_eq_right.mpr h]

/-- Blueprint `lem:lin-monotone` (`oplus` monotone, fixed element on the
left): if `p ≤ q` then `oplus r p ≤ oplus r q`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `otimes_le_otimes_left`, content.tex lem:lin-monotone)
theorem oplus_le_oplus_left {p q : α} (h : p ≤ q) (r : α) :
    oplus r p ≤ oplus r q := by
  calc oplus r p = oplus r (p ⊓ q) := by rw [inf_eq_left.mpr h]
    _ = oplus r p ⊓ oplus r q := LinBLat2Mon.oplus_inf r p q
    _ ≤ oplus r q := inf_le_right

/-- Blueprint `lem:lin-monotone` (`oplus` monotone, fixed element on the
right): if `p ≤ q` then `oplus p r ≤ oplus q r`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `otimes_le_otimes_left`, content.tex lem:lin-monotone)
theorem oplus_le_oplus_right {p q : α} (h : p ≤ q) (r : α) :
    oplus p r ≤ oplus q r := by
  calc oplus p r = oplus (p ⊓ q) r := by rw [inf_eq_left.mpr h]
    _ = oplus p r ⊓ oplus q r := LinBLat2Mon.inf_oplus p q r
    _ ≤ oplus q r := inf_le_right

/-! ### `lem:lin-lax-duals`: lax dual preservations

Blueprint proof: `q ⊓ r ≤ q` and `q ⊓ r ≤ r`, so monotonicity
(`lem:lin-monotone`) gives `otimes p (q ⊓ r) ≤ otimes p q` and `≤ otimes p r`,
hence `≤` their meet; dually for `oplus`. -/

/-- Blueprint `lem:lin-lax-duals` (`otimes` laxly preserves meets, right
argument): `otimes p (q ⊓ r) ≤ otimes p q ⊓ otimes p r`. -/
theorem otimes_inf_le (p q r : α) :
    otimes p (q ⊓ r) ≤ otimes p q ⊓ otimes p r :=
  le_inf (otimes_le_otimes_left inf_le_left p) (otimes_le_otimes_left inf_le_right p)

/-- Blueprint `lem:lin-lax-duals` (`otimes` laxly preserves meets, left
argument): `otimes (q ⊓ r) p ≤ otimes q p ⊓ otimes r p`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `otimes_inf_le`, content.tex lem:lin-lax-duals)
theorem inf_otimes_le (p q r : α) :
    otimes (q ⊓ r) p ≤ otimes q p ⊓ otimes r p :=
  le_inf (otimes_le_otimes_right inf_le_left p) (otimes_le_otimes_right inf_le_right p)

/-- Blueprint `lem:lin-lax-duals` (`oplus` laxly preserves joins, right
argument): `oplus p q ⊔ oplus p r ≤ oplus p (q ⊔ r)`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `otimes_inf_le`, content.tex lem:lin-lax-duals)
theorem le_oplus_sup (p q r : α) :
    oplus p q ⊔ oplus p r ≤ oplus p (q ⊔ r) :=
  sup_le (oplus_le_oplus_left le_sup_left p) (oplus_le_oplus_left le_sup_right p)

/-- Blueprint `lem:lin-lax-duals` (`oplus` laxly preserves joins, left
argument): `oplus q p ⊔ oplus r p ≤ oplus (q ⊔ r) p`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `otimes_inf_le`, content.tex lem:lin-lax-duals)
theorem le_sup_oplus (p q r : α) :
    oplus q p ⊔ oplus r p ≤ oplus (q ⊔ r) p :=
  sup_le (oplus_le_oplus_right le_sup_left p) (oplus_le_oplus_right le_sup_right p)

end LinearLemmas

end NeSyCat
