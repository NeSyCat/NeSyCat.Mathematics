/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.LogicalLayer.TruthStructures.BLat2Mon

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
(`chain_otimes_sup`, `chain_sup_otimes`, `chain_oplus_inf`, `chain_inf_oplus`)
are one-line corollaries specializing the raw operation `f` to `otimes`/
`oplus`; they exist only because `LinBLat2Mon.ofChain`
(`def:chain-lin-unitbounds`, which *does* need the bound and
`UnitBounds`) wants its four binary fields already in `BLat2Mon`-native
shape, not to add anything past the raw lemmas.

The monotonicity hypotheses ("suppose `otimes` and `oplus` are monotone in each
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
unit, since e.g. `∀ p q, p Otimes q ≤ p` alone says nothing about `≤ q`). This
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
-- blueprint: internal (A1 bijection-law companion of `chain_otimes_sup`, content.tex thm:chain-lin)
theorem chain_binop_sup_left (f : α → α → α)
    (hf : ∀ {x y : α}, x ≤ y → ∀ r : α, f x r ≤ f y r)
    (p q r : α) : f (p ⊔ q) r = f p r ⊔ f q r := by
  rcases le_total p q with h | h
  · rw [sup_eq_right.mpr h, sup_eq_right.mpr (hf h r)]
  · rw [sup_eq_left.mpr h, sup_eq_left.mpr (hf h r)]

/-- Blueprint `thm:chain-lin` (i, raw meet, right argument): dually to
`chain_binop_sup_right`, for any binary operation `f` monotone with a fixed
left element, `f` preserves finite meets in its right argument. -/
-- blueprint: internal (A1 bijection-law companion of `chain_otimes_sup`, content.tex thm:chain-lin)
theorem chain_binop_inf_right (f : α → α → α)
    (hf : ∀ {x y : α}, x ≤ y → ∀ r : α, f r x ≤ f r y)
    (p q r : α) : f p (q ⊓ r) = f p q ⊓ f p r := by
  rcases le_total q r with h | h
  · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hf h p)]
  · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hf h p)]

/-- Blueprint `thm:chain-lin` (i, raw meet, left argument): dually to
`chain_binop_sup_left`, for any binary operation `f` monotone with a fixed
right element, `f` preserves finite meets in its left argument. -/
-- blueprint: internal (A1 bijection-law companion of `chain_otimes_sup`, content.tex thm:chain-lin)
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

One-line specializations of the raw lemmas above at `f := otimes`/`oplus`,
kept (name and statement unchanged from before this rider) because
`LinBLat2Mon.ofChain` below wants its four binary fields already in this
shape. -/

/-- Blueprint `thm:chain-lin` (i, `otimes`-join, right argument): a corollary
of `chain_binop_sup_right` at `f := otimes`. -/
-- blueprint: internal (A1 companion: BLat2Mon-context corollary of
-- chain_binop_sup_right, content.tex thm:chain-lin)
theorem chain_otimes_sup
    (otimes_mono_left : ∀ {x y : α}, x ≤ y → ∀ r : α, otimes r x ≤ otimes r y)
    (p q r : α) : otimes p (q ⊔ r) = otimes p q ⊔ otimes p r :=
  chain_binop_sup_right otimes otimes_mono_left p q r

/-- Blueprint `thm:chain-lin` (i, `otimes`-join, left argument): a corollary
of `chain_binop_sup_left` at `f := otimes`. -/
-- blueprint: internal (A1 bijection-law companion of `chain_otimes_sup`, content.tex thm:chain-lin)
theorem chain_sup_otimes
    (otimes_mono_right : ∀ {x y : α}, x ≤ y → ∀ r : α, otimes x r ≤ otimes y r)
    (p q r : α) : otimes (p ⊔ q) r = otimes p r ⊔ otimes q r :=
  chain_binop_sup_left otimes otimes_mono_right p q r

/-- Blueprint `thm:chain-lin` (i, `oplus`-meet, right argument): a corollary
of `chain_binop_inf_right` at `f := oplus`. -/
-- blueprint: internal (A1 bijection-law companion of `chain_otimes_sup`, content.tex thm:chain-lin)
theorem chain_oplus_inf
    (oplus_mono_left : ∀ {x y : α}, x ≤ y → ∀ r : α, oplus r x ≤ oplus r y)
    (p q r : α) : oplus p (q ⊓ r) = oplus p q ⊓ oplus p r :=
  chain_binop_inf_right oplus oplus_mono_left p q r

/-- Blueprint `thm:chain-lin` (i, `oplus`-meet, left argument): a corollary
of `chain_binop_inf_left` at `f := oplus`. -/
-- blueprint: internal (A1 bijection-law companion of `chain_otimes_sup`, content.tex thm:chain-lin)
theorem chain_inf_oplus
    (oplus_mono_right : ∀ {x y : α}, x ≤ y → ∀ r : α, oplus x r ≤ oplus y r)
    (p q r : α) : oplus (p ⊓ q) r = oplus p r ⊓ oplus q r :=
  chain_binop_inf_left oplus oplus_mono_right p q r

/-- Blueprint `def:chain-lin-unitbounds`: on a chain (`[LinearOrder α]`)
whose `otimes` and `oplus` are monotone in each argument (`thm:chain-lin`),
and which is bounded with `UnitBounds` (Definition~`def:unit-bounds`),
the full `LinBLat2Mon` structure is present — `thm:chain-lin`'s four
binary laws are `chain_otimes_sup`, `chain_sup_otimes`, `chain_oplus_inf`,
`chain_inf_oplus`; this definition's own nullary laws follow from the
unit bounds by the same monotonicity: annihilation
`otimes p ⊥ = ⊥` from `p ≤ ⊤ = done` and `otimes_done`/`bot_le`, and dually for
`bot_otimes`; absorption `oplus p ⊤ = ⊤` from `⊥ = dzero ≤ p` and
`dzero_oplus`/`le_top`, and dually for `top_oplus`. -/
@[reducible] def LinBLat2Mon.ofChain [UnitBounds α]
    (otimes_mono_left : ∀ {x y : α}, x ≤ y → ∀ r : α, otimes r x ≤ otimes r y)
    (otimes_mono_right : ∀ {x y : α}, x ≤ y → ∀ r : α, otimes x r ≤ otimes y r)
    (oplus_mono_left : ∀ {x y : α}, x ≤ y → ∀ r : α, oplus r x ≤ oplus r y)
    (oplus_mono_right : ∀ {x y : α}, x ≤ y → ∀ r : α, oplus x r ≤ oplus y r) :
    LinBLat2Mon α where
  otimes_sup := chain_otimes_sup otimes_mono_left
  sup_otimes := chain_sup_otimes otimes_mono_right
  oplus_inf := chain_oplus_inf oplus_mono_left
  inf_oplus := chain_inf_oplus oplus_mono_right
  otimes_bot p := by
    apply le_antisymm _ bot_le
    calc otimes p ⊥ ≤ otimes ⊤ ⊥ := otimes_mono_right le_top ⊥
      _ = otimes done ⊥ := by rw [OneTop.done_eq_top]
      _ = ⊥ := done_otimes ⊥
  bot_otimes p := by
    apply le_antisymm _ bot_le
    calc otimes ⊥ p ≤ otimes ⊥ ⊤ := otimes_mono_left le_top ⊥
      _ = otimes ⊥ done := by rw [OneTop.done_eq_top]
      _ = ⊥ := otimes_done ⊥
  oplus_top p := by
    apply le_antisymm le_top
    calc (⊤ : α) = oplus dzero ⊤ := (dzero_oplus ⊤).symm
      _ = oplus ⊥ ⊤ := by rw [ZeroBot.dzero_eq_bot]
      _ ≤ oplus p ⊤ := oplus_mono_right bot_le ⊤
  top_oplus p := by
    apply le_antisymm le_top
    calc (⊤ : α) = oplus ⊤ dzero := (oplus_dzero ⊤).symm
      _ = oplus ⊤ ⊥ := by rw [ZeroBot.dzero_eq_bot]
      _ ≤ oplus ⊤ p := oplus_mono_left bot_le ⊤

end Chain

/-! ### `lem:dualabsorb-decomposition`: unit bounds via mixed absorption -/

section DualAbsorb

variable {α : Type*} [Lattice α] [BoundedOrder α] [LinBLat2Mon α]

/-- Blueprint `lem:dualabsorb-decomposition` (i, inequality form): `done = ⊤`
iff `otimes` is everywhere below the meet. Proof: forward, monotonicity gives
`otimes p q ≤ otimes p ⊤ = otimes p done = p` and dually `≤ q`; backward, taking
`p := done` gives `q = done Otimes q ≤ done ⊓ q ≤ done` for all `q`, so
`⊤ ≤ done`. -/
theorem done_eq_top_iff_otimes_le_inf :
    (done : α) = ⊤ ↔ ∀ p q : α, otimes p q ≤ p ⊓ q := by
  constructor
  · intro h p q
    apply le_inf
    · calc otimes p q ≤ otimes p ⊤ := otimes_le_otimes_left le_top p
        _ = otimes p done := by rw [h]
        _ = p := otimes_done p
    · calc otimes p q ≤ otimes ⊤ q := otimes_le_otimes_right le_top q
        _ = otimes done q := by rw [h]
        _ = q := done_otimes q
  · intro h
    have key : ∀ q : α, q ≤ done := fun q => by
      calc q = otimes done q := (done_otimes q).symm
        _ ≤ done ⊓ q := h done q
        _ ≤ done := inf_le_left
    exact le_antisymm le_top (key ⊤)

/-- Blueprint `lem:dualabsorb-decomposition` (i, absorption form): `done = ⊤`
iff the mixed absorption `p ⊔ (otimes p q) = p` holds for all `p, q`. Forward
via `done_eq_top_iff_otimes_le_inf`; backward, taking `p := done` gives
`done ⊔ q = done` for all `q` (via `done_otimes`), so `q ≤ done`, hence
`⊤ ≤ done`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `done_eq_top_iff_otimes_le_inf`, content.tex lem:dualabsorb-decomposition)
theorem done_eq_top_iff_sup_otimes_absorb :
    (done : α) = ⊤ ↔ ∀ p q : α, p ⊔ otimes p q = p := by
  constructor
  · intro h p q
    exact sup_eq_left.mpr ((done_eq_top_iff_otimes_le_inf.mp h p q).trans inf_le_left)
  · intro h
    have key : ∀ q : α, q ≤ done := fun q => by
      have hq : done ⊔ otimes done q = done := h done q
      rw [done_otimes] at hq
      exact sup_eq_left.mp hq
    exact le_antisymm le_top (key ⊤)

/-- Blueprint `lem:dualabsorb-decomposition` (ii, inequality form): dually,
`dzero = ⊥` iff `oplus` is everywhere above the join. -/
-- blueprint: internal (A1 bijection-law companion of
-- `done_eq_top_iff_otimes_le_inf`, content.tex lem:dualabsorb-decomposition)
theorem dzero_eq_bot_iff_sup_le_oplus :
    (dzero : α) = ⊥ ↔ ∀ p q : α, p ⊔ q ≤ oplus p q := by
  constructor
  · intro h p q
    apply sup_le
    · calc p = oplus p dzero := (oplus_dzero p).symm
        _ = oplus p ⊥ := by rw [h]
        _ ≤ oplus p q := oplus_le_oplus_left bot_le p
    · calc q = oplus dzero q := (dzero_oplus q).symm
        _ = oplus ⊥ q := by rw [h]
        _ ≤ oplus p q := oplus_le_oplus_right bot_le q
  · intro h
    have key : ∀ p : α, dzero ≤ p := fun p => by
      have hp : p ⊔ dzero ≤ oplus p dzero := h p dzero
      rw [oplus_dzero] at hp
      exact sup_eq_left.mp (le_antisymm hp le_sup_left)
    exact le_antisymm (key ⊥) bot_le

/-- Blueprint `lem:dualabsorb-decomposition` (ii, absorption form): dually,
`dzero = ⊥` iff the mixed absorption `p ⊓ (oplus p q) = p` holds. -/
-- blueprint: internal (A1 bijection-law companion of
-- `done_eq_top_iff_otimes_le_inf`, content.tex lem:dualabsorb-decomposition)
theorem dzero_eq_bot_iff_inf_oplus_absorb :
    (dzero : α) = ⊥ ↔ ∀ p q : α, p ⊓ oplus p q = p := by
  constructor
  · intro h p q
    exact inf_eq_left.mpr (le_sup_left.trans (dzero_eq_bot_iff_sup_le_oplus.mp h p q))
  · intro h
    have key : ∀ p : α, dzero ≤ p := fun p => by
      have hp : dzero ⊓ oplus dzero p = dzero := h dzero p
      rw [dzero_oplus] at hp
      exact inf_eq_left.mp hp
    exact le_antisymm (key ⊥) bot_le

end DualAbsorb

/-! ### `lem:mix`: the four-connective chain -/

section Mix

variable {α : Type*} [Lattice α] [BoundedOrder α] [LinBLat2Mon α] [UnitBounds α]

/-- Blueprint `lem:mix` (outer-left inequality): `otimes p q ≤ p ⊓ q`, from
`done_eq_top_iff_otimes_le_inf` applied to `UnitBounds`' `done = ⊤`. -/
-- blueprint: internal (A1 bijection-law companion of `mix_chain`, content.tex lem:mix)
theorem otimes_le_inf (p q : α) : otimes p q ≤ p ⊓ q :=
  done_eq_top_iff_otimes_le_inf.mp OneTop.done_eq_top p q

/-- Blueprint `lem:mix` (outer-right inequality): `p ⊔ q ≤ oplus p q`, from
`dzero_eq_bot_iff_sup_le_oplus` applied to `UnitBounds`' `dzero = ⊥`. -/
-- blueprint: internal (A1 bijection-law companion of `mix_chain`, content.tex lem:mix)
theorem sup_le_oplus (p q : α) : p ⊔ q ≤ oplus p q :=
  dzero_eq_bot_iff_sup_le_oplus.mp ZeroBot.dzero_eq_bot p q

/-- Blueprint `lem:mix` (the four-connective chain, MIX): in a `LinBLat2Mon`
with `UnitBounds`, the four binary connectives form a chain
`otimes p q ≤ p ⊓ q ≤ p ⊔ q ≤ oplus p q`; the outer inequalities are
`otimes_le_inf`/`sup_le_oplus` and the middle one is `inf_le_sup` from the
ambient lattice. -/
theorem mix_chain (p q : α) :
    otimes p q ≤ p ⊓ q ∧ p ⊓ q ≤ p ⊔ q ∧ p ⊔ q ≤ oplus p q :=
  ⟨otimes_le_inf p q, inf_le_sup, sup_le_oplus p q⟩

/-- Blueprint `lem:mix` (MIX, the named corollary [Girard 1987]): `otimes p q ≤
oplus p q`, factoring through the lattice as `mix_chain`. -/
-- blueprint: internal (A1 bijection-law companion of `mix_chain`, content.tex lem:mix)
theorem otimes_le_oplus (p q : α) : otimes p q ≤ oplus p q :=
  (otimes_le_inf p q).trans (inf_le_sup.trans (sup_le_oplus p q))

end Mix

end NeSyCat
