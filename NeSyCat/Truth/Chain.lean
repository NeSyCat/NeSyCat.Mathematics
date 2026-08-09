/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.Truth.BLat2Mon

/-!
# Chains are linear, unit-bound decompositions, and MIX

Blueprint items `thm:chain-lin`, `def:chain-lin-unitbounds` (C2-E4a/A1
peer-split of the former single `thm:chain-lin` env: part (i) keeps that
label as a `theorem`, part (ii) is the new `definition`-kind label, its
principal declaration `LinBLat2Mon.ofChain` being a `def`-valued
constructor, not a Prop-valued theorem), `lem:dualabsorb-decomposition`,
`lem:mix` (`blueprint/src/content.tex`, §"Truth-value structures") — the
library's own development; the MIX vocabulary is from linear logic
(Girard 1987), and `[NeSy26, App. A]` is cited by the blueprint only on
the concrete row lemmas, not on these.

## `thm:chain-lin`

The blueprint's carrier for part (i) is "a lattice, **not necessarily
bounded**, carrying two monoid structures ... whose order is a chain" —
and part (i)'s proof never actually uses any monoid law (associativity,
units) either, only that a *binary operation* is monotone in each
argument. So part (i) is stated at its own honest maximal generality: raw
binary-operation lemmas over a bare `[LinearOrder α]` with *no*
`BoundedOrder` and *no* `BLat2Mon` in sight (`chain_binop_sup_right`,
`chain_binop_sup_left`, `chain_binop_inf_right`, `chain_binop_inf_left`) —
these instantiate directly at the unbounded chains the "not necessarily
bounded" clause is *for* (`ℝ≥0`, `LogS`, ...), which have no
`BoundedOrder` instance at all. The `BLat2Mon`-context lemmas
(`chain_andC_sup`, `chain_sup_andC`, `chain_parr_inf`, `chain_inf_parr`)
are one-line corollaries specializing the raw operation `f` to `andC`/
`parr`; they exist only because `LinBLat2Mon.ofChain`
(`def:chain-lin-unitbounds`, which *does* need the bound and
`UnitBounds`) wants its four binary fields already in `BLat2Mon`-native
shape, not to add anything past the raw lemmas.

The monotonicity hypotheses ("suppose `andC` and `parr` are monotone in each
argument") are taken as plain function arguments to each lemma, not as a new
typeclass — a chain's `BLat2Mon` need not already be `LinBLat2Mon` (that is
exactly the fact being established), so there is no home for such a class
short of `LinBLat2Mon` itself.

**The instance-diamond wrinkle.** `BLat2Mon` demands `[Lattice α]` as a free
instance argument, not a derived one; on a concrete chain carrier `α` this is
resolved by ordinary instance search at each application site, not baked in
as `LinearOrder.toLattice` by this file's definitions. For `unitInterval`,
Lean resolves `Lattice unitInterval` to `Set.Icc.lattice` (built from
`Real.lattice` via the ambient `Subtype`/`Icc` order), a *different* instance
path than `LinearOrder.toLattice unitInterval` — but the two are
*definitionally equal* (`(inferInstance : Lattice unitInterval) =
LinearOrder.toLattice := rfl` typechecks), so the lemmas below apply to
`unitInterval` without any diamond: whichever `Lattice α` instance ordinary
search finds at the call site is what gets used, and it agrees with the one
implicitly present in the `[LinearOrder α]` hypothesis on any concrete chain
where the two are defeq (as they are here).

## `lem:dualabsorb-decomposition` and `lem:mix`

Both unit-bound mixins turn out to be equivalent, *as universally quantified
statements*, to an inequality form and an absorption form; the blueprint's
"iff ... iff ..." routes both outer equivalences through the mixin equation
as a pivot (not through a direct, pointwise implication between the two
outer forms — no such pointwise implication holds without going through the
unit, since e.g. `∀ p q, p AndC q ≤ p` alone says nothing about `≤ q`). This
file accordingly proves two `Iff`s per side, both anchored at the mixin
equation (`done = ⊤` for (i), `dzero = ⊥` for (ii)), matching the blueprint's
own proof structure (`taking p = done`/`taking q = dzero`) exactly.
-/

namespace NeSyCat

open BLat2Mon

section RawChain

/-! ### `thm:chain-lin`(i), raw form: no monoid, no bound, just a chain

The blueprint's part (i) hypothesis is exactly "a lattice, not necessarily
bounded, ... whose order is a chain, and [a binary operation] monotone in
each argument" — captured here with no `BoundedOrder` and no `BLat2Mon` at
all, just a bare explicit `f : α → α → α`. This is the honest maximal
statement: it instantiates directly at unbounded chains such as
`NeSyCat.MassS` (`ℝ≥0`) or `NeSyCat.LogS`, which the blueprint's clause is
for and which carry no `BoundedOrder` instance. -/

variable {α : Type*} [LinearOrder α]

/-- Blueprint `thm:chain-lin` (i, raw join, right argument): "a lattice, not
necessarily bounded, ... whose order is a chain", for any binary operation
`f` monotone with a fixed left element, `f` preserves finite joins in its
right argument. Proof: on a chain `q ⊔ r ∈ {q, r}`; say `q ≤ r`, so
`q ⊔ r = r` and monotonicity gives `f p q ≤ f p r`, hence
`f p q ⊔ f p r = f p r` too. -/
theorem chain_binop_sup_right (f : α → α → α)
    (hf : ∀ {x y : α}, x ≤ y → ∀ r : α, f r x ≤ f r y)
    (p q r : α) : f p (q ⊔ r) = f p q ⊔ f p r := by
  rcases le_total q r with h | h
  · rw [sup_eq_right.mpr h, sup_eq_right.mpr (hf h p)]
  · rw [sup_eq_left.mpr h, sup_eq_left.mpr (hf h p)]

/-- Blueprint `thm:chain-lin` (i, raw join, left argument): dually, for any
binary operation `f` monotone with a fixed right element, `f` preserves
finite joins in its left argument. -/
-- blueprint: internal (A1 bijection-law companion of `chain_andC_sup`, content.tex thm:chain-lin)
theorem chain_binop_sup_left (f : α → α → α)
    (hf : ∀ {x y : α}, x ≤ y → ∀ r : α, f x r ≤ f y r)
    (p q r : α) : f (p ⊔ q) r = f p r ⊔ f q r := by
  rcases le_total p q with h | h
  · rw [sup_eq_right.mpr h, sup_eq_right.mpr (hf h r)]
  · rw [sup_eq_left.mpr h, sup_eq_left.mpr (hf h r)]

/-- Blueprint `thm:chain-lin` (i, raw meet, right argument): dually to
`chain_binop_sup_right`, for any binary operation `f` monotone with a fixed
left element, `f` preserves finite meets in its right argument. -/
-- blueprint: internal (A1 bijection-law companion of `chain_andC_sup`, content.tex thm:chain-lin)
theorem chain_binop_inf_right (f : α → α → α)
    (hf : ∀ {x y : α}, x ≤ y → ∀ r : α, f r x ≤ f r y)
    (p q r : α) : f p (q ⊓ r) = f p q ⊓ f p r := by
  rcases le_total q r with h | h
  · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hf h p)]
  · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hf h p)]

/-- Blueprint `thm:chain-lin` (i, raw meet, left argument): dually to
`chain_binop_sup_left`, for any binary operation `f` monotone with a fixed
right element, `f` preserves finite meets in its left argument. -/
-- blueprint: internal (A1 bijection-law companion of `chain_andC_sup`, content.tex thm:chain-lin)
theorem chain_binop_inf_left (f : α → α → α)
    (hf : ∀ {x y : α}, x ≤ y → ∀ r : α, f x r ≤ f y r)
    (p q r : α) : f (p ⊓ q) r = f p r ⊓ f q r := by
  rcases le_total p q with h | h
  · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hf h r)]
  · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hf h r)]

end RawChain

section Chain

variable {α : Type*} [LinearOrder α] [BoundedOrder α] [BLat2Mon α]

/-! ### `thm:chain-lin`(i), `BLat2Mon`-context corollaries

One-line specializations of the raw lemmas above at `f := andC`/`parr`,
kept (name and statement unchanged from before this rider) because
`LinBLat2Mon.ofChain` below wants its four binary fields already in this
shape. -/

/-- Blueprint `thm:chain-lin` (i, `andC`-join, right argument): a corollary
of `chain_binop_sup_right` at `f := andC`. -/
-- blueprint: internal (A1 companion: BLat2Mon-context corollary of
-- chain_binop_sup_right, content.tex thm:chain-lin)
theorem chain_andC_sup
    (andC_mono_left : ∀ {x y : α}, x ≤ y → ∀ r : α, andC r x ≤ andC r y)
    (p q r : α) : andC p (q ⊔ r) = andC p q ⊔ andC p r :=
  chain_binop_sup_right andC andC_mono_left p q r

/-- Blueprint `thm:chain-lin` (i, `andC`-join, left argument): a corollary
of `chain_binop_sup_left` at `f := andC`. -/
-- blueprint: internal (A1 bijection-law companion of `chain_andC_sup`, content.tex thm:chain-lin)
theorem chain_sup_andC
    (andC_mono_right : ∀ {x y : α}, x ≤ y → ∀ r : α, andC x r ≤ andC y r)
    (p q r : α) : andC (p ⊔ q) r = andC p r ⊔ andC q r :=
  chain_binop_sup_left andC andC_mono_right p q r

/-- Blueprint `thm:chain-lin` (i, `parr`-meet, right argument): a corollary
of `chain_binop_inf_right` at `f := parr`. -/
-- blueprint: internal (A1 bijection-law companion of `chain_andC_sup`, content.tex thm:chain-lin)
theorem chain_parr_inf
    (parr_mono_left : ∀ {x y : α}, x ≤ y → ∀ r : α, parr r x ≤ parr r y)
    (p q r : α) : parr p (q ⊓ r) = parr p q ⊓ parr p r :=
  chain_binop_inf_right parr parr_mono_left p q r

/-- Blueprint `thm:chain-lin` (i, `parr`-meet, left argument): a corollary
of `chain_binop_inf_left` at `f := parr`. -/
-- blueprint: internal (A1 bijection-law companion of `chain_andC_sup`, content.tex thm:chain-lin)
theorem chain_inf_parr
    (parr_mono_right : ∀ {x y : α}, x ≤ y → ∀ r : α, parr x r ≤ parr y r)
    (p q r : α) : parr (p ⊓ q) r = parr p r ⊓ parr q r :=
  chain_binop_inf_left parr parr_mono_right p q r

/-- Blueprint `def:chain-lin-unitbounds`: on a chain (`[LinearOrder α]`)
whose `andC` and `parr` are monotone in each argument (`thm:chain-lin`),
and which is bounded with `UnitBounds` (Definition~`def:unit-bounds`),
the full `LinBLat2Mon` structure is present — `thm:chain-lin`'s four
binary laws are `chain_andC_sup`, `chain_sup_andC`, `chain_parr_inf`,
`chain_inf_parr`; this definition's own nullary laws follow from the
unit bounds by the same monotonicity: annihilation
`andC p ⊥ = ⊥` from `p ≤ ⊤ = done` and `andC_done`/`bot_le`, and dually for
`bot_andC`; absorption `parr p ⊤ = ⊤` from `⊥ = dzero ≤ p` and
`dzero_parr`/`le_top`, and dually for `top_parr`. -/
@[reducible] def LinBLat2Mon.ofChain [UnitBounds α]
    (andC_mono_left : ∀ {x y : α}, x ≤ y → ∀ r : α, andC r x ≤ andC r y)
    (andC_mono_right : ∀ {x y : α}, x ≤ y → ∀ r : α, andC x r ≤ andC y r)
    (parr_mono_left : ∀ {x y : α}, x ≤ y → ∀ r : α, parr r x ≤ parr r y)
    (parr_mono_right : ∀ {x y : α}, x ≤ y → ∀ r : α, parr x r ≤ parr y r) :
    LinBLat2Mon α where
  andC_sup := chain_andC_sup andC_mono_left
  sup_andC := chain_sup_andC andC_mono_right
  parr_inf := chain_parr_inf parr_mono_left
  inf_parr := chain_inf_parr parr_mono_right
  andC_bot p := by
    apply le_antisymm _ bot_le
    calc andC p ⊥ ≤ andC ⊤ ⊥ := andC_mono_right le_top ⊥
      _ = andC done ⊥ := by rw [OneTop.done_eq_top]
      _ = ⊥ := done_andC ⊥
  bot_andC p := by
    apply le_antisymm _ bot_le
    calc andC ⊥ p ≤ andC ⊥ ⊤ := andC_mono_left le_top ⊥
      _ = andC ⊥ done := by rw [OneTop.done_eq_top]
      _ = ⊥ := andC_done ⊥
  parr_top p := by
    apply le_antisymm le_top
    calc (⊤ : α) = parr dzero ⊤ := (dzero_parr ⊤).symm
      _ = parr ⊥ ⊤ := by rw [ZeroBot.dzero_eq_bot]
      _ ≤ parr p ⊤ := parr_mono_right bot_le ⊤
  top_parr p := by
    apply le_antisymm le_top
    calc (⊤ : α) = parr ⊤ dzero := (parr_dzero ⊤).symm
      _ = parr ⊤ ⊥ := by rw [ZeroBot.dzero_eq_bot]
      _ ≤ parr ⊤ p := parr_mono_left bot_le ⊤

end Chain

/-! ### `lem:dualabsorb-decomposition`: unit bounds via mixed absorption -/

section DualAbsorb

variable {α : Type*} [Lattice α] [BoundedOrder α] [LinBLat2Mon α]

/-- Blueprint `lem:dualabsorb-decomposition` (i, inequality form): `done = ⊤`
iff `andC` is everywhere below the meet. Proof: forward, monotonicity gives
`andC p q ≤ andC p ⊤ = andC p done = p` and dually `≤ q`; backward, taking
`p := done` gives `q = done AndC q ≤ done ⊓ q ≤ done` for all `q`, so
`⊤ ≤ done`. -/
theorem done_eq_top_iff_andC_le_inf :
    (done : α) = ⊤ ↔ ∀ p q : α, andC p q ≤ p ⊓ q := by
  constructor
  · intro h p q
    apply le_inf
    · calc andC p q ≤ andC p ⊤ := andC_le_andC_left le_top p
        _ = andC p done := by rw [h]
        _ = p := andC_done p
    · calc andC p q ≤ andC ⊤ q := andC_le_andC_right le_top q
        _ = andC done q := by rw [h]
        _ = q := done_andC q
  · intro h
    have key : ∀ q : α, q ≤ done := fun q => by
      calc q = andC done q := (done_andC q).symm
        _ ≤ done ⊓ q := h done q
        _ ≤ done := inf_le_left
    exact le_antisymm le_top (key ⊤)

/-- Blueprint `lem:dualabsorb-decomposition` (i, absorption form): `done = ⊤`
iff the mixed absorption `p ⊔ (andC p q) = p` holds for all `p, q`. Forward
via `done_eq_top_iff_andC_le_inf`; backward, taking `p := done` gives
`done ⊔ q = done` for all `q` (via `done_andC`), so `q ≤ done`, hence
`⊤ ≤ done`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `done_eq_top_iff_andC_le_inf`, content.tex lem:dualabsorb-decomposition)
theorem done_eq_top_iff_sup_andC_absorb :
    (done : α) = ⊤ ↔ ∀ p q : α, p ⊔ andC p q = p := by
  constructor
  · intro h p q
    exact sup_eq_left.mpr ((done_eq_top_iff_andC_le_inf.mp h p q).trans inf_le_left)
  · intro h
    have key : ∀ q : α, q ≤ done := fun q => by
      have hq : done ⊔ andC done q = done := h done q
      rw [done_andC] at hq
      exact sup_eq_left.mp hq
    exact le_antisymm le_top (key ⊤)

/-- Blueprint `lem:dualabsorb-decomposition` (ii, inequality form): dually,
`dzero = ⊥` iff `parr` is everywhere above the join. -/
-- blueprint: internal (A1 bijection-law companion of
-- `done_eq_top_iff_andC_le_inf`, content.tex lem:dualabsorb-decomposition)
theorem dzero_eq_bot_iff_sup_le_parr :
    (dzero : α) = ⊥ ↔ ∀ p q : α, p ⊔ q ≤ parr p q := by
  constructor
  · intro h p q
    apply sup_le
    · calc p = parr p dzero := (parr_dzero p).symm
        _ = parr p ⊥ := by rw [h]
        _ ≤ parr p q := parr_le_parr_left bot_le p
    · calc q = parr dzero q := (dzero_parr q).symm
        _ = parr ⊥ q := by rw [h]
        _ ≤ parr p q := parr_le_parr_right bot_le q
  · intro h
    have key : ∀ p : α, dzero ≤ p := fun p => by
      have hp : p ⊔ dzero ≤ parr p dzero := h p dzero
      rw [parr_dzero] at hp
      exact sup_eq_left.mp (le_antisymm hp le_sup_left)
    exact le_antisymm (key ⊥) bot_le

/-- Blueprint `lem:dualabsorb-decomposition` (ii, absorption form): dually,
`dzero = ⊥` iff the mixed absorption `p ⊓ (parr p q) = p` holds. -/
-- blueprint: internal (A1 bijection-law companion of
-- `done_eq_top_iff_andC_le_inf`, content.tex lem:dualabsorb-decomposition)
theorem dzero_eq_bot_iff_inf_parr_absorb :
    (dzero : α) = ⊥ ↔ ∀ p q : α, p ⊓ parr p q = p := by
  constructor
  · intro h p q
    exact inf_eq_left.mpr (le_sup_left.trans (dzero_eq_bot_iff_sup_le_parr.mp h p q))
  · intro h
    have key : ∀ p : α, dzero ≤ p := fun p => by
      have hp : dzero ⊓ parr dzero p = dzero := h dzero p
      rw [dzero_parr] at hp
      exact inf_eq_left.mp hp
    exact le_antisymm (key ⊥) bot_le

end DualAbsorb

/-! ### `lem:mix`: the four-connective chain -/

section Mix

variable {α : Type*} [Lattice α] [BoundedOrder α] [LinBLat2Mon α] [UnitBounds α]

/-- Blueprint `lem:mix` (outer-left inequality): `andC p q ≤ p ⊓ q`, from
`done_eq_top_iff_andC_le_inf` applied to `UnitBounds`' `done = ⊤`. -/
-- blueprint: internal (A1 bijection-law companion of `mix_chain`, content.tex lem:mix)
theorem andC_le_inf (p q : α) : andC p q ≤ p ⊓ q :=
  done_eq_top_iff_andC_le_inf.mp OneTop.done_eq_top p q

/-- Blueprint `lem:mix` (outer-right inequality): `p ⊔ q ≤ parr p q`, from
`dzero_eq_bot_iff_sup_le_parr` applied to `UnitBounds`' `dzero = ⊥`. -/
-- blueprint: internal (A1 bijection-law companion of `mix_chain`, content.tex lem:mix)
theorem sup_le_parr (p q : α) : p ⊔ q ≤ parr p q :=
  dzero_eq_bot_iff_sup_le_parr.mp ZeroBot.dzero_eq_bot p q

/-- Blueprint `lem:mix` (the four-connective chain, MIX): in a `LinBLat2Mon`
with `UnitBounds`, the four binary connectives form a chain
`andC p q ≤ p ⊓ q ≤ p ⊔ q ≤ parr p q`; the outer inequalities are
`andC_le_inf`/`sup_le_parr` and the middle one is `inf_le_sup` from the
ambient lattice. -/
theorem mix_chain (p q : α) :
    andC p q ≤ p ⊓ q ∧ p ⊓ q ≤ p ⊔ q ∧ p ⊔ q ≤ parr p q :=
  ⟨andC_le_inf p q, inf_le_sup, sup_le_parr p q⟩

/-- Blueprint `lem:mix` (MIX, the named corollary [Girard 1987]): `andC p q ≤
parr p q`, factoring through the lattice as `mix_chain`. -/
-- blueprint: internal (A1 bijection-law companion of `mix_chain`, content.tex lem:mix)
theorem andC_le_parr (p q : α) : andC p q ≤ parr p q :=
  (andC_le_inf p q).trans (inf_le_sup.trans (sup_le_parr p q))

end Mix

end NeSyCat
