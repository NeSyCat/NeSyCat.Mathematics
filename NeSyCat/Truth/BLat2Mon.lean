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
here bears *two* independent monoid structures — `(parr, dzero)` (linear
logic's `⅋`, "or-like") and `(andC, done)` (linear logic's multiplicative
`⊗`, kept as `&`/`andC` per `[NeSy26]`'s own notation) — and Mathlib's
`Monoid` typeclass can be registered at most once per type. So `BLat2Mon`
carries `parr`/`dzero`/`andC`/`done` as explicit fields (over an ambient
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
`(parr, dzero)` and `(andC, done)`; unlike a lattice-semiring
(`NeSyCat.LatSRng`), no distributivity of any kind is assumed between the
three structures. Distilled from `[NeSy26, App. A]` (the lifted-connective
family); vocabulary from linear logic (Girard 1987). -/
class BLat2Mon (α : Type*) [Lattice α] [BoundedOrder α] where
  /-- The `⅋`-monoid multiplication (linear logic's `⅋`, "or-like"). -/
  parr : α → α → α
  /-- The `⅋`-unit (linear logic's `⊥`, the blueprint's `0̇`). -/
  dzero : α
  /-- The `&`-monoid multiplication (linear logic's *multiplicative*
  conjunction `⊗`; kept as `&`/`andC` per `[NeSy26]`'s notation, see the
  linear-logic dictionary table in `blueprint/src/content.tex`,
  §"Truth-value structures"). -/
  andC : α → α → α
  /-- The `&`-unit (linear logic's `1`, the blueprint's `1̇`). -/
  done : α
  parr_assoc : ∀ p q r, parr (parr p q) r = parr p (parr q r)
  dzero_parr : ∀ p, parr dzero p = p
  parr_dzero : ∀ p, parr p dzero = p
  andC_assoc : ∀ p q r, andC (andC p q) r = andC p (andC q r)
  done_andC : ∀ p, andC done p = p
  andC_done : ∀ p, andC p done = p

/-- Blueprint `def:blat2cmon` (Commutative two-monoid bounded lattice): a
**BLat2CMon** is a `BLat2Mon` whose two monoids `(parr, dzero)` and
`(andC, done)` are both commutative. -/
class BLat2CMon (α : Type*) [Lattice α] [BoundedOrder α] extends BLat2Mon α where
  parr_comm : ∀ p q, parr p q = parr q p
  andC_comm : ∀ p q, andC p q = andC q p

/-- Blueprint `def:lin-blat2mon` (Linear two-monoid lattice): a
**LinBLat2Mon** is a `BLat2Mon` in which `andC` preserves finite joins in
each argument and `parr` preserves finite meets in each argument: binary
(`p & (q ⊔ r) = (p & q) ⊔ (p & r)` and its left-argument twin, dually for
`⅋` and `⊓`) and nullary (`p & ⊥ = ⊥` annihilation, `p ⅋ ⊤ = ⊤` absorption,
both two-sided). These are exactly the four linear distributions of linear
logic (`⊗` over `⊕`, `⅋` over `&`, together with their units), transported
along the linear-logic dictionary table of `blueprint/src/content.tex`,
§"Truth-value structures" (Girard 1987). -/
class LinBLat2Mon (α : Type*) [Lattice α] [BoundedOrder α] extends BLat2Mon α where
  /-- `andC` preserves finite joins in its right argument. -/
  andC_sup : ∀ p q r, andC p (q ⊔ r) = andC p q ⊔ andC p r
  /-- `andC` preserves finite joins in its left argument. -/
  sup_andC : ∀ p q r, andC (p ⊔ q) r = andC p r ⊔ andC q r
  /-- `parr` preserves finite meets in its right argument. -/
  parr_inf : ∀ p q r, parr p (q ⊓ r) = parr p q ⊓ parr p r
  /-- `parr` preserves finite meets in its left argument. -/
  inf_parr : ∀ p q r, parr (p ⊓ q) r = parr p r ⊓ parr q r
  /-- Annihilation: `andC` kills `⊥` on the right. -/
  andC_bot : ∀ p, andC p ⊥ = ⊥
  /-- Annihilation: `andC` kills `⊥` on the left. -/
  bot_andC : ∀ p, andC ⊥ p = ⊥
  /-- Absorption: `parr` saturates to `⊤` on the right. -/
  parr_top : ∀ p, parr p ⊤ = ⊤
  /-- Absorption: `parr` saturates to `⊤` on the left. -/
  top_parr : ∀ p, parr ⊤ p = ⊤

/-- Blueprint `def:lin-blat2cmon` (Commutative linear two-monoid lattice): a
**LinBLat2CMon** is a `BLat2CMon` satisfying the `LinBLat2Mon` laws (a
commutative `LinBLat2Mon`); Lean flattens the shared `BLat2Mon` parent. -/
class LinBLat2CMon (α : Type*) [Lattice α] [BoundedOrder α]
    extends LinBLat2Mon α, BLat2CMon α

/-- Blueprint `def:dm-structure` (De Morgan structure): a **DM structure**
on a `BLat2Mon` is a map `dneg` satisfying (i) `dneg (dneg p) = p`;
(ii) `p ≤ q → dneg q ≤ dneg p`; (iii)
`dneg (p & q) = dneg q ⅋ dneg p`. Linear negation (Girard 1987), axiomatized
minimally; the equivalent presentations (antitonicity vs. the lattice
De Morgan law) are compared in `thm:dm-presentations` (out of scope here). -/
class DMStructure (α : Type*) [Lattice α] [BoundedOrder α] [BLat2Mon α] where
  dneg : α → α
  dneg_dneg : ∀ p, dneg (dneg p) = p
  dneg_antitone : ∀ p q : α, p ≤ q → dneg q ≤ dneg p
  dneg_andC : ∀ p q, dneg (BLat2Mon.andC p q) = BLat2Mon.parr (dneg q) (dneg p)

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
`andC q r = andC (p ⊔ q) r = andC p r ⊔ andC q r ≥ andC p r`; the other
argument, and `parr` (via `p = p ⊓ q` and meet-preservation), are dual. Four
argument-versions (fixed element named per the side it sits on, mirroring
`NeSyCat.LatSRng.add_le_add_left`/`add_le_add_right`). -/

/-- Blueprint `lem:lin-monotone` (`andC` monotone, fixed element on the
left): if `p ≤ q` then `andC r p ≤ andC r q`. -/
theorem andC_le_andC_left {p q : α} (h : p ≤ q) (r : α) :
    andC r p ≤ andC r q := by
  calc andC r p ≤ andC r p ⊔ andC r q := le_sup_left
    _ = andC r (p ⊔ q) := (LinBLat2Mon.andC_sup r p q).symm
    _ = andC r q := by rw [sup_eq_right.mpr h]

/-- Blueprint `lem:lin-monotone` (`andC` monotone, fixed element on the
right): if `p ≤ q` then `andC p r ≤ andC q r`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andC_le_andC_left`, content.tex lem:lin-monotone)
theorem andC_le_andC_right {p q : α} (h : p ≤ q) (r : α) :
    andC p r ≤ andC q r := by
  calc andC p r ≤ andC p r ⊔ andC q r := le_sup_left
    _ = andC (p ⊔ q) r := (LinBLat2Mon.sup_andC p q r).symm
    _ = andC q r := by rw [sup_eq_right.mpr h]

/-- Blueprint `lem:lin-monotone` (`parr` monotone, fixed element on the
left): if `p ≤ q` then `parr r p ≤ parr r q`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andC_le_andC_left`, content.tex lem:lin-monotone)
theorem parr_le_parr_left {p q : α} (h : p ≤ q) (r : α) :
    parr r p ≤ parr r q := by
  calc parr r p = parr r (p ⊓ q) := by rw [inf_eq_left.mpr h]
    _ = parr r p ⊓ parr r q := LinBLat2Mon.parr_inf r p q
    _ ≤ parr r q := inf_le_right

/-- Blueprint `lem:lin-monotone` (`parr` monotone, fixed element on the
right): if `p ≤ q` then `parr p r ≤ parr q r`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andC_le_andC_left`, content.tex lem:lin-monotone)
theorem parr_le_parr_right {p q : α} (h : p ≤ q) (r : α) :
    parr p r ≤ parr q r := by
  calc parr p r = parr (p ⊓ q) r := by rw [inf_eq_left.mpr h]
    _ = parr p r ⊓ parr q r := LinBLat2Mon.inf_parr p q r
    _ ≤ parr q r := inf_le_right

/-! ### `lem:lin-lax-duals`: lax dual preservations

Blueprint proof: `q ⊓ r ≤ q` and `q ⊓ r ≤ r`, so monotonicity
(`lem:lin-monotone`) gives `andC p (q ⊓ r) ≤ andC p q` and `≤ andC p r`,
hence `≤` their meet; dually for `parr`. -/

/-- Blueprint `lem:lin-lax-duals` (`andC` laxly preserves meets, right
argument): `andC p (q ⊓ r) ≤ andC p q ⊓ andC p r`. -/
theorem andC_inf_le (p q r : α) :
    andC p (q ⊓ r) ≤ andC p q ⊓ andC p r :=
  le_inf (andC_le_andC_left inf_le_left p) (andC_le_andC_left inf_le_right p)

/-- Blueprint `lem:lin-lax-duals` (`andC` laxly preserves meets, left
argument): `andC (q ⊓ r) p ≤ andC q p ⊓ andC r p`. -/
-- blueprint: internal (A1 bijection-law companion of `andC_inf_le`, content.tex lem:lin-lax-duals)
theorem inf_andC_le (p q r : α) :
    andC (q ⊓ r) p ≤ andC q p ⊓ andC r p :=
  le_inf (andC_le_andC_right inf_le_left p) (andC_le_andC_right inf_le_right p)

/-- Blueprint `lem:lin-lax-duals` (`parr` laxly preserves joins, right
argument): `parr p q ⊔ parr p r ≤ parr p (q ⊔ r)`. -/
-- blueprint: internal (A1 bijection-law companion of `andC_inf_le`, content.tex lem:lin-lax-duals)
theorem le_parr_sup (p q r : α) :
    parr p q ⊔ parr p r ≤ parr p (q ⊔ r) :=
  sup_le (parr_le_parr_left le_sup_left p) (parr_le_parr_left le_sup_right p)

/-- Blueprint `lem:lin-lax-duals` (`parr` laxly preserves joins, left
argument): `parr q p ⊔ parr r p ≤ parr (q ⊔ r) p`. -/
-- blueprint: internal (A1 bijection-law companion of `andC_inf_le`, content.tex lem:lin-lax-duals)
theorem le_sup_parr (p q r : α) :
    parr q p ⊔ parr r p ≤ parr (q ⊔ r) p :=
  sup_le (parr_le_parr_right le_sup_left p) (parr_le_parr_right le_sup_right p)

end LinearLemmas

end NeSyCat
