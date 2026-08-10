/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.LogicalLayer.TruthStructures.BLat2Mon
import NeSyCat.LogicalLayer.TruthStructures.Chain
import NeSyCat.LogicalLayer.TruthStructures.DeMorgan
import NeSyCat.LogicalLayer.TruthSpaces.Lifted

/-!
# The mass completion `[0,∞]`

Blueprint items `inst:mass-completion-latcsrng`, `inst:mass-completion-linblat2cmon`,
`thm:mass-completion-not-unitbounds`, `thm:mass-submeet-fails`, `thm:mass-mix-fails`,
`thm:no-dm-mass-completion`, `lem:mass-completion-bounds`
(`blueprint/src/content.tex`, §"Completions") -- the library's own development,
closing the forward pointers left by `inst:massS-latcsrng`, `thm:no-dm-mass`, and
`def:order-family`'s bounds clause.

## The carrier

`[0,∞] := ℝ≥0∞` (Mathlib `ENNReal`), used directly -- no fresh type synonym is
needed here (unlike `LogS`/`LogSInf`), since `ℝ≥0∞` already carries exactly the
`CommSemiring`/`CompleteLinearOrder` structure the blueprint's row wants, with no
competing instance to avoid.

## Two independent structures on one carrier

`ℝ≥0∞` carries TWO separate pieces of blueprint structure, proved independently:

1. `instBLatCSRngENNReal : BLatCSRng ℝ≥0∞` (`inst:mass-completion-latcsrng`) --
   the SEMIRING row (the completion of `inst:massS-latcsrng`, the weight carrier
   for the monad `MS`), `⊕ = +`, `⊗ = ·`, monotone, bounded (`⊥=0`, `⊤=∞`).
2. `instLinBLat2CMonENNReal : LinBLat2CMon ℝ≥0∞` (`inst:mass-completion-linblat2cmon`)
   -- the TRUTH-STRUCTURE row (`BLat2Mon`'s `otimes`/`oplus`/`done`/`dzero`),
   `otimes := (·*·)`, `done := 1`, `oplus := (·+·)`, `dzero := 0`. This is a
   DIFFERENT class from (1): it lives on the two-monoid-lattice hierarchy of
   `NeSyCat/LogicalLayer/TruthStructures/BLat2Mon.lean`, the one `unitInterval`
   and `BoolW` also instantiate.

The four linear laws of `LinBLat2Mon` (`otimes_sup`/`sup_otimes`/`oplus_inf`/`inf_oplus`)
are NOT proved by hand: `ℝ≥0∞` is a `LinearOrder`, `*` and `+` are each monotone in
both arguments, so `NeSyCat/LogicalLayer/TruthStructures/Chain.lean`'s raw chain
lemmas (`thm:chain-lin`(i)'s own generality, no bound and no `UnitBounds` needed)
apply directly. The nullary laws (annihilation, absorption) are the ordinary
`mul_zero`/`zero_mul`/`add_top`/`top_add` facts of `ℝ≥0∞` -- so `LinBLat2Mon.ofChain`
is NOT used either: `ofChain` demands `UnitBounds` to derive exactly these nullary
laws from the unit bounds, and `UnitBounds` FAILS here (`done = 1 ≠ ⊤`,
`thm:mass-completion-not-unitbounds`), so the annihilation/absorption facts are
supplied directly from `ℝ≥0∞`'s own arithmetic instead.

## The convention, stated as a choice

`0 * ∞ = ∞ * 0 = 0` on `ℝ≥0∞` (Mathlib's own convention, inherited unchanged):
annihilation by `0` beats absorption by `∞`. This is not forced by the order or
the lattice structure; it is the semiring's own choice of how `*` extends to the
top element, and it is what makes `instBLatCSRngENNReal`'s `mul_zero`/`zero_mul`
(hence `LinBLat2CMon`'s `otimes_bot`/`bot_otimes`) hold unconditionally.

## `thm:mass-completion-not-unitbounds`: the regime boundary

`ZeroBot ℝ≥0∞` holds (`dzero = 0 = ⊥`) but `OneTop ℝ≥0∞` fails (`done = 1 ≠ ⊤ = ∞`,
`not_oneTop_ennreal`): `UnitBounds` splits. This is the exact sense in which
`UnitBounds` is a boundary between REGIMES, not between having linear-logic
structure at all: `ℝ≥0∞` is a full `LinBLat2CMon` (all four linear laws hold)
with units strictly below the lattice bounds on one side.

## `thm:mass-submeet-fails`/`thm:mass-mix-fails`: the separating counterexamples

`lem:mix`'s two clauses each need ONLY one half of `UnitBounds`
(`otimes_le_inf` needs `OneTop`, `sup_le_oplus` needs `ZeroBot`) --
`otimes_not_le_inf_ennreal`/`otimes_not_le_oplus_ennreal` are exactly the
witnesses that `OneTop` cannot be dropped from `otimes_le_inf`/`mix_chain`: at
`p = q = 3`, `otimes p q = 9`, `p ⊓ q = 3`, `oplus p q = 6`, so `9 ≤ 3` and
`9 ≤ 6` both fail. The witness `p = q = 3` is chosen in the PROOF only (the
Lean statement, like the blueprint statement, is the bare negated universal --
the anatomy law).

## `thm:no-dm-mass-completion`: the De Morgan question resolves

Unlike `thm:no-dm-mass` (no `BoundedOrder ℝ≥0`, so not even statable as `¬
DMStructure`), `ℝ≥0∞` genuinely has bounds, and its order is self-dual (e.g. via
the reciprocal `p ↦ 1/p`, `0 ↦ ∞`, `∞ ↦ 0`). But no antitone involution can
satisfy the De Morgan law (iii) for `(otimes, oplus) = (·, +)`: two GENERAL facts
about any `DMStructure` (`dneg_bot`/`dneg_dzero`,
`NeSyCat/LogicalLayer/TruthStructures/DeMorgan.lean`, needing no `UnitBounds`)
force `dneg ⊥ = ⊤` and `dneg dzero = done`; since `dzero = ⊥` here (`ZeroBot`),
these collide at `dneg 0`, forcing `done = ⊤`, i.e. `1 = ∞` -- false. So a
`DMStructure` compatible with `(·,+)` would force EXACTLY the `UnitBounds`
equality `thm:mass-completion-not-unitbounds` already refutes: the De Morgan
question and the regime-boundary question resolve by the same mechanism.
-/

namespace NeSyCat

open scoped NNReal ENNReal
open BLat2Mon

/-! ### `inst:mass-completion-latcsrng`: the semiring row -/

/-- Blueprint `inst:mass-completion-latcsrng` (Mass completion, semiring row):
`ℝ≥0∞` (`⊕ = +`, `⊗ = ·`), monotone in both arguments (`gcongr`, `ℝ≥0∞`'s
existing order-compatible semiring instances) and bounded (`⊥ = 0`, `⊤ = ∞`,
inherited from `ℝ≥0∞`'s `CompleteLinearOrder`, auto-filled by the `BLatSRng`
parent). Mathlib's `0 * ∞ = 0` convention (annihilation beats absorption, see
the module doc comment) makes every field below unconditional. -/
noncomputable instance instBLatCSRngENNReal : BLatCSRng ℝ≥0∞ where
  add_le_add_left _ c := by gcongr
  add_le_add_right _ c := by gcongr
  mul_le_mul_left _ c := by gcongr
  mul_le_mul_right _ c := by gcongr
  mul_comm := mul_comm

/-! ### `inst:mass-completion-linblat2cmon`: the truth-structure row -/

/-- Blueprint `inst:mass-completion-linblat2cmon` (Mass completion, truth
structure): `otimes := (·*·)`, `done := 1`, `oplus := (·+·)`, `dzero := 0` is a
`LinBLat2CMon ℝ≥0∞`. Monoid/commutativity laws are `ℝ≥0∞`'s own `CommSemiring`
facts. The four linear laws come from `NeSyCat/LogicalLayer/TruthStructures/Chain.lean`'s
raw chain lemmas (`ℝ≥0∞` is a `LinearOrder`, `*`/`+` each monotone in both
arguments, `gcongr`) -- no bound and no `UnitBounds` needed for THIS part,
matching `thm:chain-lin`(i)'s own generality. The nullary laws are `ℝ≥0∞`'s own
`mul_zero`/`zero_mul`/`add_top`/`top_add`. -/
noncomputable instance instLinBLat2CMonENNReal : LinBLat2CMon ℝ≥0∞ where
  oplus := (· + ·)
  dzero := 0
  otimes := (· * ·)
  done := 1
  oplus_assoc := add_assoc
  dzero_oplus := zero_add
  oplus_dzero := add_zero
  otimes_assoc := mul_assoc
  done_otimes := one_mul
  otimes_done := mul_one
  oplus_comm := add_comm
  otimes_comm := mul_comm
  otimes_sup p q r := chain_binop_sup_right (· * ·) (fun _ _ => by gcongr) p q r
  sup_otimes p q r := chain_binop_sup_left (· * ·) (fun _ _ => by gcongr) p q r
  oplus_inf p q r := chain_binop_inf_right (· + ·) (fun _ _ => by gcongr) p q r
  inf_oplus p q r := chain_binop_inf_left (· + ·) (fun _ _ => by gcongr) p q r
  otimes_bot := mul_zero
  bot_otimes := zero_mul
  oplus_top := add_top
  top_oplus := top_add

/-- Blueprint `inst:mass-completion-linblat2cmon` (`ZeroBot` half): `dzero = 0
= ⊥` by construction. Companion of `instLinBLat2CMonENNReal`, not separately
cited (the env's own statement covers it). -/
-- (A1 bijection-law companion of
-- `instLinBLat2CMonENNReal`, content.tex inst:mass-completion-linblat2cmon)
@[blueprint_internal]
instance instZeroBotENNReal : ZeroBot ℝ≥0∞ where
  dzero_eq_bot := rfl

/-! ### `thm:mass-completion-not-unitbounds` -/

/-- Blueprint `thm:mass-completion-not-unitbounds` (the regime boundary):
`OneTop` fails for the mass completion's truth structure, `done = 1 ≠ ⊤ = ∞`.
Together with `instZeroBotENNReal` (`ZeroBot` holds), `UnitBounds` splits: a
full `LinBLat2CMon` exists here without its units coinciding with the lattice
bounds. -/
theorem not_oneTop_ennreal : ¬ OneTop ℝ≥0∞ := by
  intro h
  have h1 := h.done_eq_top
  change (1 : ℝ≥0∞) = ⊤ at h1
  simp at h1

/-! ### `thm:mass-submeet-fails`/`thm:mass-mix-fails`: the separating
counterexamples -/

/-- Blueprint `thm:mass-submeet-fails` (⊗-amplification kills the sub-meet
law): on the mass completion, `otimes` is not everywhere below the meet.
Witness (proof only, per the anatomy law): `p = q = 3` gives
`otimes p q = 9 > 3 = p ⊓ q`. -/
theorem otimes_not_le_inf_ennreal : ¬ ∀ p q : ℝ≥0∞, otimes p q ≤ p ⊓ q := by
  intro h
  have h39 := h 3 3
  norm_num [otimes] at h39

/-- Blueprint `thm:mass-mix-fails` (MIX fails): on the mass completion,
`otimes` is not everywhere below `oplus`. Witness (proof only): `p = q = 3`
gives `otimes p q = 9`, `oplus p q = 6`, and `9 ≰ 6`. -/
theorem otimes_not_le_oplus_ennreal : ¬ ∀ p q : ℝ≥0∞, otimes p q ≤ oplus p q := by
  intro h
  have h96 := h 3 3
  norm_num [otimes, oplus] at h96

/-! ### `thm:no-dm-mass-completion` -/

/-- Blueprint `thm:no-dm-mass-completion` (No De Morgan structure on the mass
completion): no antitone involution `dneg` on `ℝ≥0∞` satisfies the De Morgan
law for `(otimes, oplus) = (·, +)`. Proof: package `dneg` as a `DMStructure`
against the ambient `instLinBLat2CMonENNReal`, then combine two GENERAL
`DMStructure` facts (`dneg_bot : dneg ⊥ = ⊤`, `dneg_dzero : dneg dzero =
done`, neither needing `UnitBounds`) at the point `dzero = ⊥` (`ZeroBot`):
they collide, forcing `done = ⊤`, i.e. `(1:ℝ≥0∞) = ⊤`, which is false. -/
theorem no_dm_ennreal :
    ¬ ∃ dneg : ℝ≥0∞ → ℝ≥0∞, (∀ p, dneg (dneg p) = p) ∧ Antitone dneg ∧
      (∀ p q, dneg (p * q) = dneg q + dneg p) := by
  rintro ⟨dneg, hinv, hanti, hand⟩
  letI : DMStructure ℝ≥0∞ := ⟨dneg, hinv, fun _ _ h => hanti h, hand⟩
  have h1 : dneg (⊥ : ℝ≥0∞) = ⊤ := dneg_bot
  have h2 : dneg (dzero : ℝ≥0∞) = done := dneg_dzero
  change dneg (0 : ℝ≥0∞) = 1 at h2
  rw [show (⊥ : ℝ≥0∞) = 0 from rfl] at h1
  rw [h1] at h2
  simp at h2

/-! ### `lem:mass-completion-bounds`: discharging `def:order-family`'s bounds
clause -/

/-- Blueprint `lem:mass-completion-bounds` (the mass row's order-family
bounds, now concrete): on the completed carrier `ℝ≥0∞`, `def:order-family`'s
generic bounds instantiate to `⊥ = (∞,0)` and `⊤ = (0,∞)`, discharging
`lem:lifted-mass`'s deferred bounds clause -- the two-slot readout of
`orderBot`/`orderTop` (`NeSyCat/LogicalLayer/TruthSpaces/Lifted.lean`),
generic under `[BoundedOrder S]`, at `S := ℝ≥0∞`. -/
theorem lifted_mass_bounds :
    twoSlot (orderBot : MS ℝ≥0∞ BoolW) = (⊤, ⊥) ∧
      twoSlot (orderTop : MS ℝ≥0∞ BoolW) = (⊥, ⊤) :=
  ⟨twoSlot_orderBot, twoSlot_orderTop⟩

end NeSyCat
