/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.Truth.TruthSpace
import NeSyCat.Truth.UnitInterval
import NeSyCat.Monad.LogIso

/-!
# The lifted-connective routing engine, its mass/log instances, and the order family

Blueprint items `lem:lifted-mass`, `lem:lifted-log`, `lem:lifted-prob-readout`,
and `def:order-family` (`blueprint/src/content.tex`, §"Truth spaces and
lifted connectives", `[NeSy26, App. A]`).

## The routing engine (`lift₂_apply`/`twoSlot_lift₂`), built once

Every binary lifted connective's `twoSlot` readout is an instance of the
*same* four-term routing computation: each of the four Boolean argument
pairs `(i, j)` contributes the product `wᵢvⱼ` into whichever output slot
`op i j` selects. This is proved once, at a general `[Semiring S]`
(`lift₂_apply`/`twoSlot_lift₂`, via `bind_apply_boolW` +
`Finsupp.single_apply`), and the mass/log instances below
(`lem:lifted-mass`/`lem:lifted-log`) are obtained purely by substituting
the concrete `BoolW` truth table of `∧`/`∨` into the four `if`-conditions
and letting `S`'s own arithmetic (`ℝ≥0`'s `+`/`*`, resp. `lse`/`logMul` via
`lem:log-iso`'s bridging lemmas) simplify the result — no sum manipulation
is repeated per carrier.

## `def:order-family`

The order family on `MS S BoolW ≅ S²` (slot `0` reversed) is *exactly* the
componentwise order on `Sᵒᵈ × S` — `OrderDual` does all the work, so no
bespoke order relation is defined: `orderedTwoSlot : MS S BoolW ≃ Sᵒᵈ × S`
is `twoSlot` composed with `OrderDual.toDual` on the first factor, and the
order family's meet/join/bounds are transported through it as plain
functions (`orderMeet`/`orderJoin`/`orderBot`/`orderTop`), never as new
`Lattice`/`BoundedOrder` instances on `MS S BoolW` itself (the hard rail
against instance pollution on Mathlib-shaped carriers).

## `lem:lifted-prob-readout`

Stated as readout *homomorphy*: the `Dist`-restricted lifted connectives
(`andD`/`parrD`/`negD`, whose mass-one closure is a two-line Fubini
argument reusing `NeSyCat/Monad/Dist.lean`'s `bind_mass_one`/`ret_mass_one`
exactly as chapter 1 does) commute with `distReadout` onto the *stipulated*
`unitInterval` family of `NeSyCat/Truth/UnitInterval.lean` (`&`, `⅋`,
`unitInterval.symm`) — the "derived, not stipulated" content of the
blueprint item, in homomorphism form rather than as raw `ℝ≥0`
truncated-subtraction formulas.
-/

namespace NeSyCat

open scoped NNReal

variable {S : Type*} [Semiring S]

/-! ### The routing engine, once -/

/-- The routing engine (pointwise form): the coefficient of `lift₂ op w v`
at any output point `c` is the sum, over the four Boolean argument pairs
`(i, j)`, of `wᵢvⱼ` restricted to those pairs with `op i j = c`. Proved via
`bind_apply_boolW` (twice, unfolding `lift₂_eq`'s bind chain) and
`Finsupp.single_apply` (unfolding `Ret`); the arithmetic identity across
the sixteen sign patterns of the four `if`-conditions is `noncomm_ring`
(no commutativity of `S`'s `*` is used — only distributivity, matching
`NeSyCat/Monad/SemiringMonad.lean`'s "distributivity is bind
associativity" theme one level up). -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex
-- def:lifted-connective)
theorem lift₂_apply (op : BoolW → BoolW → BoolW) (w v : MS S BoolW) (c : BoolW) :
    (lift₂ op w v) c =
      (if op 0 0 = c then w 0 * v 0 else 0) + (if op 0 1 = c then w 0 * v 1 else 0) +
        (if op 1 0 = c then w 1 * v 0 else 0) + (if op 1 1 = c then w 1 * v 1 else 0) := by
  rw [lift₂_eq, bind_apply_boolW, bind_apply_boolW, bind_apply_boolW]
  unfold ret
  rw [Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> noncomm_ring

/-- Blueprint `lem:lifted-mass`/`lem:lifted-log` (the general routing
engine, `twoSlot` form): the two-coordinate readout of a binary lifted
connective, in terms of the four Boolean argument-pair contributions —
`lift₂_apply` at `c = 0` and `c = 1`. Proved once at general `[Semiring S]`;
every mass/log coordinate formula below is a substitution instance. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem twoSlot_lift₂ (op : BoolW → BoolW → BoolW) (w v : MS S BoolW) :
    twoSlot (lift₂ op w v) =
      ((if op 0 0 = 0 then w 0 * v 0 else 0) + (if op 0 1 = 0 then w 0 * v 1 else 0) +
          (if op 1 0 = 0 then w 1 * v 0 else 0) + (if op 1 1 = 0 then w 1 * v 1 else 0),
        (if op 0 0 = 1 then w 0 * v 0 else 0) + (if op 0 1 = 1 then w 0 * v 1 else 0) +
          (if op 1 0 = 1 then w 1 * v 0 else 0) + (if op 1 1 = 1 then w 1 * v 1 else 0)) := by
  ext
  · exact lift₂_apply op w v 0
  · exact lift₂_apply op w v 1

/-- The unary routing engine (pointwise form), dual to `lift₂_apply`. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex
-- def:lifted-connective)
theorem lift₁_apply (op : BoolW → BoolW) (w : MS S BoolW) (c : BoolW) :
    (lift₁ op w) c = (if op 0 = c then w 0 else 0) + (if op 1 = c then w 1 else 0) := by
  rw [lift₁_eq, bind_apply_boolW]
  unfold ret
  rw [Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> noncomm_ring

/-- The unary routing engine, `twoSlot` form. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem twoSlot_lift₁ (op : BoolW → BoolW) (w : MS S BoolW) :
    twoSlot (lift₁ op w) =
      ((if op 0 = 0 then w 0 else 0) + (if op 1 = 0 then w 1 else 0),
        (if op 0 = 1 then w 0 else 0) + (if op 1 = 1 then w 1 else 0)) := by
  ext
  · exact lift₁_apply op w 0
  · exact lift₁_apply op w 1

/-! ### The general (`[Semiring S]`) coordinate formulas, proved once -/

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
private theorem BoolW_and_table :
    ((0 : BoolW) * 0 = 0) ∧ ((0 : BoolW) * 1 = 0) ∧ ((1 : BoolW) * 0 = 0) ∧
      ((1 : BoolW) * 1 = 1) :=
  ⟨by decide, by decide, by decide, by decide⟩

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
private theorem BoolW_or_table :
    ((0 : BoolW) + 0 = 0) ∧ ((0 : BoolW) + 1 = 1) ∧ ((1 : BoolW) + 0 = 1) ∧
      ((1 : BoolW) + 1 = 1) :=
  ⟨by decide, by decide, by decide, by decide⟩

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
private theorem BoolW_not_table : (negOp (0 : BoolW) = 1) ∧ (negOp (1 : BoolW) = 0) :=
  ⟨by decide, by decide⟩

/-- The `\&`-lift's coordinate formula, at a general `[Semiring S]`: `w \& v
= (w₀v₀+w₀v₁+w₁v₀, w₁v₁)` — the entry with `∧(1,1)=1` collects `w₁v₁` into
slot `1`, the three entries with `∧ = 0` sum into slot `0` (the routing
engine `twoSlot_lift₂` specialized at `op := ∧`, then `BoolW_and_table`
resolves all four `if`-conditions). Proved once; `lem:lifted-mass` and
`lem:lifted-log` are the `S := ℝ≥0`/`S := LogS` instances below, with no
sum manipulation repeated per carrier. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_andM (w v : MS S BoolW) :
    twoSlot (andM w v) = (w 0 * v 0 + w 0 * v 1 + w 1 * v 0, w 1 * v 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := BoolW_and_table
  unfold andM
  rw [twoSlot_lift₂]
  simp [h00, h01, h10, h11, BoolW_zero_ne_one, BoolW_zero_ne_one.symm]

/-- The `⅋`-lift's coordinate formula, dually: `w ⅋ v = (w₀v₀,
w₀v₁+w₁v₀+w₁v₁)`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_parrM (w v : MS S BoolW) :
    twoSlot (parrM w v) = (w 0 * v 0, w 0 * v 1 + w 1 * v 0 + w 1 * v 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := BoolW_or_table
  unfold parrM
  rw [twoSlot_lift₂]
  simp [h00, h01, h10, h11, BoolW_zero_ne_one, BoolW_zero_ne_one.symm]

/-- The `¬`-lift's coordinate formula: `¬w = (w₁, w₀)`, the swap. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_negM (w : MS S BoolW) : twoSlot (negM w) = (w 1, w 0) := by
  obtain ⟨h0, h1⟩ := BoolW_not_table
  unfold negM
  rw [twoSlot_lift₁, h0, h1]
  simp [BoolW_zero_ne_one, BoolW_zero_ne_one.symm]

/-- The units' coordinate formula: `Ret(0) = (1, 0)`, the `⅋`-identity
(certain False), and `Ret(1) = (0, 1)`, the `\&`-identity (certain True) —
the unique solutions of `e ⅋ w = w`/`e \& w = w`, found here directly from
`ret`'s two-point support (`Finsupp.single_eq_same`/`_eq_of_ne`). Erratum
note: the blueprint's own "Erratum, corrected upstream" paragraph
(`blueprint/src/content.tex`, §"Truth spaces and lifted connectives",
just after `lem:lifted-mass`) records that the source's original table
had these two cells transposed; this is the corrected form. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_ret_zero : twoSlot (ret (0 : BoolW) : MS S BoolW) = (1, 0) := by
  simp [ret, Finsupp.single_eq_same, Finsupp.single_eq_of_ne BoolW_zero_ne_one.symm]

-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_ret_one : twoSlot (ret (1 : BoolW) : MS S BoolW) = (0, 1) := by
  simp [ret, Finsupp.single_eq_same, Finsupp.single_eq_of_ne BoolW_zero_ne_one]

/-! ### `lem:lifted-mass`: the `S := ℝ≥0` instances (direct substitutions) -/

/-- Blueprint `lem:lifted-mass` (`\&`-lift, mass coordinates), the `S :=
ℝ≥0` instance of `twoSlot_andM`. -/
theorem twoSlot_andM_mass (w v : MS ℝ≥0 BoolW) :
    twoSlot (andM w v) = (w 0 * v 0 + w 0 * v 1 + w 1 * v 0, w 1 * v 1) :=
  twoSlot_andM w v

/-- Blueprint `lem:lifted-mass` (`⅋`-lift, mass coordinates), the `S :=
ℝ≥0` instance of `twoSlot_parrM`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_parrM_mass (w v : MS ℝ≥0 BoolW) :
    twoSlot (parrM w v) = (w 0 * v 0, w 0 * v 1 + w 1 * v 0 + w 1 * v 1) :=
  twoSlot_parrM w v

/-- Blueprint `lem:lifted-mass` (`¬`-lift, mass coordinates), the `S := ℝ≥0`
instance of `twoSlot_negM`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_negM_mass (w : MS ℝ≥0 BoolW) : twoSlot (negM w) = (w 1, w 0) :=
  twoSlot_negM w

/-- Blueprint `lem:lifted-mass` (units), the `S := ℝ≥0` instances of
`twoSlot_ret_zero`/`twoSlot_ret_one`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_ret_zero_mass : twoSlot (ret (0 : BoolW) : MS ℝ≥0 BoolW) = (1, 0) :=
  twoSlot_ret_zero

-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_ret_one_mass : twoSlot (ret (1 : BoolW) : MS ℝ≥0 BoolW) = (0, 1) :=
  twoSlot_ret_one

/-! ### `lem:lifted-log`: the `S := LogS` instances -/

/-- Blueprint `lem:lifted-log` (`\&`-lift, log coordinates): applying
`Lemma lem:log-iso`'s bridging identities (`logS_mul_eq_logMul`,
"products becoming sums", and `logS_add_eq_lse`, "sums becoming `lse`")
coordinatewise to `twoSlot_andM`'s formula recovers the blueprint's display
`a \& b = (lse(lse(a₀+b₀, a₀+b₁), a₁+b₀), a₁+b₁)`, where the inner `+` is
`logMul` (log-space "multiplication is addition") and the outer `lse` is
`LogS`'s own `⊕` (associative, so the ternary `lse(x,y,z)` display is the
two binary applications shown). -/
theorem twoSlot_andM_log (a b : MS LogS BoolW) :
    twoSlot (andM a b) =
      (lse (lse (logMul (a 0) (b 0)) (logMul (a 0) (b 1))) (logMul (a 1) (b 0)),
        logMul (a 1) (b 1)) := by
  rw [twoSlot_andM, logS_mul_eq_logMul, logS_mul_eq_logMul, logS_mul_eq_logMul,
    logS_mul_eq_logMul, logS_add_eq_lse, logS_add_eq_lse]

/-- Blueprint `lem:lifted-log` (`⅋`-lift, log coordinates), dually. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_log`, content.tex lem:lifted-log)
theorem twoSlot_parrM_log (a b : MS LogS BoolW) :
    twoSlot (parrM a b) =
      (logMul (a 0) (b 0),
        lse (lse (logMul (a 0) (b 1)) (logMul (a 1) (b 0))) (logMul (a 1) (b 1))) := by
  rw [twoSlot_parrM, logS_mul_eq_logMul, logS_mul_eq_logMul, logS_mul_eq_logMul,
    logS_mul_eq_logMul, logS_add_eq_lse, logS_add_eq_lse]

/-- Blueprint `lem:lifted-log` (`¬`-lift, log coordinates): the swap, as at
mass — the `S := LogS` instance of `twoSlot_negM`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_log`, content.tex lem:lifted-log)
theorem twoSlot_negM_log (a : MS LogS BoolW) : twoSlot (negM a) = (a 1, a 0) :=
  twoSlot_negM a

/-- Blueprint `lem:lifted-log` (units): `Ret(0) = (0, -∞)`, `Ret(1) =
(-∞, 0)` — the log-space images of `twoSlot_ret_zero`/`twoSlot_ret_one`
under `lem:log-iso`'s `1 ↦ 0`/`0 ↦ -∞` correspondence
(`logS_one_eq_zero`/`logS_zero_eq_bot`). -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_log`, content.tex lem:lifted-log)
theorem twoSlot_ret_zero_log :
    twoSlot (ret (0 : BoolW) : MS LogS BoolW) = (((0 : ℝ) : LogS), ⊥) := by
  rw [twoSlot_ret_zero, logS_one_eq_zero, logS_zero_eq_bot]
  rfl

-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_log`, content.tex lem:lifted-log)
theorem twoSlot_ret_one_log :
    twoSlot (ret (1 : BoolW) : MS LogS BoolW) = (⊥, ((0 : ℝ) : LogS)) := by
  rw [twoSlot_ret_one, logS_one_eq_zero, logS_zero_eq_bot]
  rfl

/-! ### `def:order-family` -/

variable [Lattice S]

/-- Blueprint `def:order-family` (Order family, PINNED encoding):
`MS S BoolW ≃ Sᵒᵈ × S`, `twoSlot` composed with `OrderDual.toDual` on the
first factor — the order family's `w ≤ v :⟺ w₁ ≤ v₁ ∧ w₀ ≥ v₀`
(componentwise, slot `0` reversed) is then *exactly* the product order on
`Sᵒᵈ × S`, so no bespoke order relation is defined: `OrderDual` supplies
it, together with the `Lattice (Sᵒᵈ × S)` instance Mathlib derives for
free. -/
noncomputable def orderedTwoSlot : MS S BoolW ≃ Sᵒᵈ × S :=
  twoSlot.trans (OrderDual.toDual.prodCongr (Equiv.refl S))

omit [Lattice S] in
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[simp] theorem orderedTwoSlot_apply (w : MS S BoolW) :
    orderedTwoSlot w = (OrderDual.toDual (w 0), w 1) :=
  rfl

omit [Lattice S] in
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[simp] theorem orderedTwoSlot_symm_apply (p : Sᵒᵈ × S) :
    orderedTwoSlot.symm p = twoSlot.symm (OrderDual.ofDual p.1, p.2) :=
  rfl

/-- Blueprint `def:order-family` (meet `∧`, transported through
`orderedTwoSlot` rather than registered as a new `Lattice (MS S BoolW)`
instance — the hard rail against instance pollution on Mathlib-shaped
carriers). -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def orderMeet (w v : MS S BoolW) : MS S BoolW :=
  orderedTwoSlot.symm (orderedTwoSlot w ⊓ orderedTwoSlot v)

/-- Blueprint `def:order-family` (join `∨`), dually. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def orderJoin (w v : MS S BoolW) : MS S BoolW :=
  orderedTwoSlot.symm (orderedTwoSlot w ⊔ orderedTwoSlot v)

/-- Blueprint `def:order-family` (meet coordinates): `w ∧ v = (w₀ ⊔ v₀,
w₁ ⊓ v₁)` — slot `0` dualized (a join in `S`, since meet in `Sᵒᵈ`
corresponds to join in `S`), slot `1` a plain meet in `S`. At `S := ℝ≥0`
or `LogS` (both `LinearOrder`s) this is verbatim the blueprint's
`w ∧ v = (max w₀ v₀, min w₁ v₁)`, `∧`/`⊔`/`⊓` here denoting the general
lattice operations. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_orderMeet (w v : MS S BoolW) :
    twoSlot (orderMeet w v) = (w 0 ⊔ v 0, w 1 ⊓ v 1) := by
  unfold orderMeet
  simp [orderedTwoSlot, Equiv.trans_apply]

/-- Blueprint `def:order-family` (join coordinates): `w ∨ v = (w₀ ⊓ v₀,
w₁ ⊔ v₁)`, dually. -/
-- blueprint: internal (A1 bijection-law companion of
-- `twoSlot_andM_mass`, content.tex lem:lifted-mass)
theorem twoSlot_orderJoin (w v : MS S BoolW) :
    twoSlot (orderJoin w v) = (w 0 ⊓ v 0, w 1 ⊔ v 1) := by
  unfold orderJoin
  simp [orderedTwoSlot, Equiv.trans_apply]

variable [BoundedOrder S]

/-- Blueprint `def:order-family` (bottom, "where it exists"): `⊥ =
(⊤ₛ, ⊥ₛ)`, transported through `orderedTwoSlot`. Stated only under
`[BoundedOrder S]`, matching the blueprint's own qualifier — `ℝ≥0`/`LogS`
have no in-carrier `⊤`, so no completion is invented for the mass/log
rows here (`lem:lifted-mass`'s honesty note). -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def orderBot : MS S BoolW := orderedTwoSlot.symm ⊥

/-- Blueprint `def:order-family` (top, "where it exists"): `⊤ =
(⊥ₛ, ⊤ₛ)`, dually. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def orderTop : MS S BoolW := orderedTwoSlot.symm ⊤

-- blueprint: internal (A1 bijection-law companion of
-- `orderedTwoSlot`, content.tex def:order-family)
theorem twoSlot_orderBot : twoSlot (orderBot : MS S BoolW) = (⊤, ⊥) := by
  unfold orderBot
  rw [orderedTwoSlot_symm_apply, Equiv.apply_symm_apply]
  rfl

-- blueprint: internal (A1 bijection-law companion of
-- `orderedTwoSlot`, content.tex def:order-family)
theorem twoSlot_orderTop : twoSlot (orderTop : MS S BoolW) = (⊥, ⊤) := by
  unfold orderTop
  rw [orderedTwoSlot_symm_apply, Equiv.apply_symm_apply]
  rfl

/-! ### `lem:lifted-prob-readout`: `Dist` closure and readout homomorphisms -/

/-- `Dist` (mass-one) closure of `lift₂`, for *any* binary Boolean
operation: the Fubini-style two-line argument of `NeSyCat/Monad/Dist.lean`
applied twice, via `lift₂_eq`'s bind chain and `bind_mass_one`/
`ret_mass_one` — exactly chapter 1's technique, reused rather than
reproved. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex
-- def:lifted-connective)
theorem lift₂_mass_one {a b : MS ℝ≥0 BoolW} (ha : a.sum (fun _ w => w) = 1)
    (hb : b.sum (fun _ w => w) = 1) (op : BoolW → BoolW → BoolW) :
    (lift₂ op a b).sum (fun _ w => w) = 1 := by
  rw [lift₂_eq]
  exact bind_mass_one ha fun x => bind_mass_one hb fun y => ret_mass_one _

/-- `Dist` (mass-one) closure of `lift₁`, dually. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex
-- def:lifted-connective)
theorem lift₁_mass_one {a : MS ℝ≥0 BoolW} (ha : a.sum (fun _ w => w) = 1)
    (op : BoolW → BoolW) : (lift₁ op a).sum (fun _ w => w) = 1 := by
  rw [lift₁_eq]
  exact bind_mass_one ha fun x => ret_mass_one _

/-- Blueprint `lem:lifted-prob-readout` (the `Dist`-restricted `\&`-lift). -/
-- blueprint: internal (A1 bijection-law companion of
-- `distReadout_andD`, content.tex lem:lifted-prob-readout)
noncomputable def andD (p q : Dist BoolW) : Dist BoolW :=
  ⟨andM p.1 q.1, lift₂_mass_one p.2 q.2 _⟩

/-- Blueprint `lem:lifted-prob-readout` (the `Dist`-restricted `⅋`-lift). -/
-- blueprint: internal (A1 bijection-law companion of
-- `distReadout_andD`, content.tex lem:lifted-prob-readout)
noncomputable def parrD (p q : Dist BoolW) : Dist BoolW :=
  ⟨parrM p.1 q.1, lift₂_mass_one p.2 q.2 _⟩

/-- Blueprint `lem:lifted-prob-readout` (the `Dist`-restricted `¬`-lift). -/
-- blueprint: internal (A1 bijection-law companion of
-- `distReadout_andD`, content.tex lem:lifted-prob-readout)
noncomputable def negD (p : Dist BoolW) : Dist BoolW :=
  ⟨negM p.1, lift₁_mass_one p.2 _⟩

/-- Blueprint `lem:lifted-prob-readout` (`\&` readout homomorphism):
`distReadout (p andD q) = distReadout p \& distReadout q`, where `\&` is
`unitInterval`'s own stipulated multiplication
(`NeSyCat/Truth/UnitInterval.lean`'s `instBLat2Mon`) — the *derived* lifted
`\&`, read out through the mass-one slice, coincides with the *stipulated*
`unitInterval` connective. Proved from `twoSlot_andM`'s second coordinate
(`w₁v₁`) via `NNReal.coe_mul`. -/
theorem distReadout_andD (p q : Dist BoolW) :
    distReadout (andD p q) = BLat2Mon.andC (distReadout p) (distReadout q) := by
  have hval : (andD p q).1 1 = p.1 1 * q.1 1 :=
    congrArg Prod.snd (twoSlot_andM_mass p.1 q.1)
  apply Subtype.ext
  change ((andD p q).1 1 : ℝ) = _
  rw [hval]
  push_cast
  rfl

/-- Blueprint `lem:lifted-prob-readout` (`⅋` readout homomorphism):
`distReadout (p parrD q) = distReadout p ⅋ distReadout q`, where `⅋` is
`unitInterval`'s stipulated (`σ`-conjugate) `parr`
(`NeSyCat/Truth/UnitInterval.lean`) — its real value `p+q-pq`
(`unitInterval.coe_parr`) matches the lifted family's `⅋`-slot exactly.
This is the blueprint's headline content: the `[0,1]` family is *derived*
from binding two independent truth values and pushing forward along the
Boolean operation, not stipulated. -/
-- blueprint: internal (A1 bijection-law companion of
-- `distReadout_andD`, content.tex lem:lifted-prob-readout)
theorem distReadout_parrD (p q : Dist BoolW) :
    distReadout (parrD p q) = BLat2Mon.parr (distReadout p) (distReadout q) := by
  have hmass_p := p.2
  have hmass_q := q.2
  rw [massSum_eq] at hmass_p hmass_q
  have hval : (parrD p q).1 1 = p.1 0 * q.1 1 + p.1 1 * q.1 0 + p.1 1 * q.1 1 :=
    congrArg Prod.snd (twoSlot_parrM_mass p.1 q.1)
  apply Subtype.ext
  change ((parrD p q).1 1 : ℝ) = _
  rw [hval, unitInterval.coe_parr]
  have hp : (p.1 0 : ℝ) + (p.1 1 : ℝ) = 1 := by exact_mod_cast hmass_p
  have hq : (q.1 0 : ℝ) + (q.1 1 : ℝ) = 1 := by exact_mod_cast hmass_q
  push_cast [distReadout_apply_coe]
  nlinarith [hp, hq]

/-- Blueprint `lem:lifted-prob-readout` (`¬` readout homomorphism):
`distReadout (negD p) = unitInterval.symm (distReadout p)`, i.e.
`1 - distReadout p` — the swap of `twoSlot_negM`, read through the
mass-one constraint. -/
-- blueprint: internal (A1 bijection-law companion of
-- `distReadout_andD`, content.tex lem:lifted-prob-readout)
theorem distReadout_negD (p : Dist BoolW) :
    distReadout (negD p) = unitInterval.symm (distReadout p) := by
  have hmass := p.2
  rw [massSum_eq] at hmass
  have hval : (negD p).1 1 = p.1 0 := congrArg Prod.snd (twoSlot_negM_mass p.1)
  apply Subtype.ext
  change ((negD p).1 1 : ℝ) = _
  rw [hval, unitInterval.coe_symm_eq]
  have hp : (p.1 0 : ℝ) + (p.1 1 : ℝ) = 1 := by exact_mod_cast hmass
  push_cast [distReadout_apply_coe]
  linarith

end NeSyCat
