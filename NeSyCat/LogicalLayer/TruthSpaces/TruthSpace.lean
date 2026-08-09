/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.CategoricalLayer.SemiringMonads.SemiringMonad
import NeSyCat.CategoricalLayer.SemiringMonads.Dist
import NeSyCat.CategoricalLayer.SemiringMonads.LatticeSemiring

/-!
# Truth spaces and lifted connectives: the workhorse machinery

Blueprint items `abbr:truth-space`, `def:lifted-connective`,
`lem:lifted-connective-strength`, and `def:two-slot`/`def:dist-readout`
(formerly a single combined `lem:truth-space-instances`, since split into
the two readout-equivalence definitions)
(`blueprint/src/content.tex`, §"Truth spaces and lifted connectives",
`[NeSy26, App. A]`).

## `abbr:truth-space` (formerly `def:truth-space`, C2-E4a-fix F-4:
re-kinded to Abbreviation since `TruthSpace` is an `abbrev`)

The **truth space** of a semiring monad `MS S` is `MS S BoolW`, the monad
applied to the Boolean carrier (`abbr:truth-space` — `TruthSpace` below).
The `Idmon` clause of the blueprint item (`Idmon BoolS = BoolS`) is the
trivial reading of the identity monad and needs no separate Lean object:
`BoolW` itself
(`NeSyCat/CategoricalLayer/SemiringMonads/LatticeSemiring.lean`) already
witnesses it.

## `def:lifted-connective` and `lem:lifted-connective-strength` (PINNED)

The blueprint *defines* the lifted connective `*_{MS S}` as an iterated
bind chain (`w₁ bind λu₁. ⋯ wₙ bind λuₙ. Ret(*(u₁,…,uₙ))`) and then shows,
as a corollary, that this equals `dst(w₁,…,wₙ) bind (Ret ∘ *)` via the
`n`-ary tensorial strength `dst`. Here the roles are inverted for Lean
convenience (a deliberate, disclosed encoding choice, matching the
`.foreman/C2-T3-spec.md` pin): `dstN` (the strength) and `lift` (built
*from* `dstN`) are the primitive definitions, so the strength form is
`lift`'s literal unfolding (`lift_eq_dstN_bind`, the
`lem:lifted-connective-strength` witness, near-`rfl`); the blueprint's own
*original* iterated-bind description becomes three arity-specific LEMMAS
(`lift_zero`, `lift_one`, `lift_two`, covering every arity actually used
downstream: nullary, unary `¬`, binary `∧,∨,oplus,otimes`).

`dstN` is built by structural recursion on `n` via `Fin.cons`/`Fin.tail`,
pairing the arguments left-to-right (`w 0` bound outermost) exactly as the
blueprint's own bind chain does.

## `def:two-slot` and `def:dist-readout` (formerly `lem:truth-space-instances`)

The four truth spaces of the paper and their readouts, encoded as
equivalences (never as new `Lattice`/`Monoid`-style instances on `MS S
BoolW`, per the hard rail against instance pollution on Mathlib-shaped
carriers):

* `Idmon BoolS = BoolS`: the identity case, `BoolW` itself, no Lean object;
* `Tmon BoolS ≅ MassS²`/`LTmon BoolS ≅ LogS²`: both are the *same* general
  equivalence `twoSlot : MS S BoolW ≃ S × S` (`w ↦ (w 0, w 1)`), instantiated
  at `S := ℝ≥0` and `S := LogS` respectively (the latter is, up to the
  monad isomorphism `logTensEquiv` of `NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean`, "the
  image of the `Tmon` readout" the blueprint describes: `LogTens BoolW` is
  `MS LogS BoolW` by definition of `LogTens`, so `twoSlot` at `S := LogS`
  applies to it directly, with no further wrapping needed);
* `Dmon BoolS ≅ ProbS`: `distReadout : Dist BoolW ≃ unitInterval`, routing
  through the mass-one constraint of `def:dist-monad` to eliminate the
  redundant coefficient `p(0) = 1 - p(1)` (a single-stage construction
  rather than the two-stage "restrict `twoSlot`, then reparametrize"
  route sketched as a possibility in `.foreman/C2-T3-spec.md` — disclosed
  deviation, chosen because it avoids naming an intermediate mass-one
  subtype of `ℝ≥0 × ℝ≥0` that is used nowhere else).
-/

namespace NeSyCat

open scoped NNReal

/-- Blueprint `abbr:truth-space` (Truth space): for a semiring monad `MS S`,
the truth space is `MS S BoolW`, the monad applied to the Boolean carrier
(Boolean `0` read as False, `1` as True). The `Idmon` clause of the
blueprint item is the trivial reading `Idmon BoolS = BoolS`, needing no
separate Lean object beyond `BoolW` itself. -/
abbrev TruthSpace (S : Type*) [Semiring S] := MS S BoolW

/-! ### Two-point support facts about `BoolW`

`BoolW` has exactly the two elements `0` (`false`) and `1` (`true`); every
`Finsupp`/bind computation over it collapses to a two-term
expression. These facts underlie `twoSlot`, `distReadout`, and (in
`NeSyCat/LogicalLayer/TruthSpaces/Lifted.lean`) the general lifted-connective routing engine. -/

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem BoolW_zero_ne_one : (0 : BoolW) ≠ (1 : BoolW) := by decide

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem BoolW_eq_zero_or_one (a : BoolW) : a = 0 ∨ a = 1 := by
  cases a
  · left; rfl
  · right; rfl

variable {S : Type*} [Semiring S] {X Y Z : Type*}

/-- A `Finsupp.sum` over the two-point carrier `BoolW` collapses to the sum
of its two values, for any summand `g` that is additive in its second
argument and vanishes at `0` (matching `Finsupp.sum_add_index'`'s own
hypotheses). The two-point analogue of "addition marginalises"
(`NeSyCat/CategoricalLayer/SemiringMonads/SemiringMonad.lean`'s module doc comment), specialized to
the carrier every truth-space computation runs over. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem sum_boolW {N : Type*} [AddCommMonoid N] (w : MS S BoolW) (g : BoolW → S → N)
    (hg0 : ∀ b, g b 0 = 0) (hadd : ∀ b (s₁ s₂ : S), g b (s₁ + s₂) = g b s₁ + g b s₂) :
    w.sum g = g 0 (w 0) + g 1 (w 1) := by
  have hw : w = Finsupp.single 0 (w 0) + Finsupp.single 1 (w 1) := by
    apply Finsupp.ext
    intro a
    rcases BoolW_eq_zero_or_one a with rfl | rfl
    · simp [Finsupp.add_apply, Finsupp.single_eq_same]
    · simp [Finsupp.add_apply, Finsupp.single_eq_same]
  conv_lhs => rw [hw]
  rw [Finsupp.sum_add_index' hg0 hadd, Finsupp.sum_single_index (hg0 0),
    Finsupp.sum_single_index (hg0 1)]

/-- `bind` on a `BoolW`-domain unfolds to the two-term weighted sum
`w 0 * k 0 y + w 1 * k 1 y` at every output point `y` — `bind_apply`
(`NeSyCat/CategoricalLayer/SemiringMonads/SemiringMonad.lean`) specialized via `sum_boolW`. The
starting point for the general lifted-connective routing engine in
`NeSyCat/LogicalLayer/TruthSpaces/Lifted.lean`. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem bind_apply_boolW (w : MS S BoolW) (k : BoolW → MS S Y) (y : Y) :
    bind w k y = w 0 * k 0 y + w 1 * k 1 y := by
  rw [bind_apply]
  exact sum_boolW w (fun x wx => wx * k x y) (fun _ => by rw [zero_mul])
    fun _ _ _ => by rw [add_mul]

/-- The total mass of a `BoolW`-weighted vector is the sum of its two
coefficients — the two-point specialization of `Dist`'s mass functional
(`NeSyCat/CategoricalLayer/SemiringMonads/Dist.lean`) used by `distReadout` below to unwind the
mass-one constraint. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem massSum_eq (w : MS S BoolW) : w.sum (fun _ v => v) = w 0 + w 1 :=
  sum_boolW w (fun _ v => v) (fun _ => rfl) fun _ _ _ => rfl

/-! ### `dstN`: the `n`-ary tensorial strength (PINNED as the primitive) -/

/-- Blueprint `def:lifted-connective` (`n`-ary tensorial strength `dst`,
PINNED as the primitive): `dstN w` pairs `n` independent monad values into
one value of the product type, by structural recursion on `n` via
`Fin.cons`/`Fin.tail` — `w 0` bound outermost, matching the blueprint's own
left-to-right bind order. The base case (`n = 0`) returns the point mass at
the unique function `Fin 0 → X` (`![]`). -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex def:lifted-connective)
noncomputable def dstN {W : Type*} : ∀ {n : ℕ}, (Fin n → MS S W) → MS S (Fin n → W)
  | 0, _ => ret ![]
  | (_ + 1), w => bind (w 0) fun x => bind (dstN (Fin.tail w)) fun v => ret (Fin.cons x v)

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem dstN_zero {W : Type*} (w : Fin 0 → MS S W) : dstN w = ret ![] := rfl

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem dstN_succ {W : Type*} {n : ℕ} (w : Fin (n + 1) → MS S W) :
    dstN w = bind (w 0) fun x => bind (dstN (Fin.tail w)) fun v => ret (Fin.cons x v) := rfl

/-- `dstN` at arity `1` telescopes to a single bind — the `n = 1` instance
of the blueprint's iterated-bind description of `dst`, used by `lift_one`
and, one level deeper, by `dstN_two`. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem dstN_one {W : Type*} (w : Fin 1 → MS S W) :
    dstN w = bind (w 0) fun x => ret ![x] := by
  have htail : (Fin.tail w : Fin 0 → MS S W) = ![] := by funext i; exact i.elim0
  rw [dstN_succ, htail]
  congr 1
  funext x
  rw [dstN_zero, ret_bind]
  rfl

/-- `dstN` at arity `2` telescopes to two nested binds — the `n = 2`
instance of the blueprint's iterated-bind description of `dst`, feeding
`lift_two` and, downstream (`NeSyCat/LogicalLayer/TruthSpaces/Lifted.lean`), every binary
lifted connective's routing formula. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem dstN_two {W : Type*} (w : Fin 2 → MS S W) :
    dstN w = bind (w 0) fun x => bind (w 1) fun y => ret ![x, y] := by
  rw [dstN_succ]
  congr 1
  funext x
  have htail1 : (Fin.tail w) 0 = w 1 := rfl
  rw [dstN_one, htail1, bind_assoc]
  congr 1
  funext y
  rw [ret_bind]
  rfl

/-! ### `lift`: the lifted connective (defined via strength) -/

/-- Blueprint `def:lifted-connective` (Lifted connective, defined via
strength): `lift op w := dstN w bind (Ret ∘ op)` — the strength form IS the
Lean primitive (a deliberate, disclosed pin: see the module doc comment),
so `lem:lifted-connective-strength` (`lift_eq_dstN_bind` below) is
near-`rfl`, and the blueprint's own iterated-bind definition instead
appears as the arity lemmas `lift_zero`/`lift_one`/`lift_two`. -/
noncomputable def lift {n : ℕ} {W B : Type*} (op : (Fin n → W) → B) (w : Fin n → MS S W) :
    MS S B :=
  bind (dstN w) (ret ∘ op)

/-- Blueprint `lem:lifted-connective-strength` (Lifted connective via
strength): `lift op w = dstN w bind (Ret ∘ op)`, i.e. exactly `lift`'s own
definition — the strength-form primitive was chosen so this corollary is
the trivial unfolding, with the blueprint's original iterated-bind
definition recovered instead as `lift_zero`/`lift_one`/`lift_two`. -/
theorem lift_eq_dstN_bind {n : ℕ} {W B : Type*} (op : (Fin n → W) → B) (w : Fin n → MS S W) :
    lift op w = bind (dstN w) (ret ∘ op) :=
  rfl

/-- Blueprint `def:lifted-connective` (nullary case, matching the
blueprint's own iterated-bind description at `n = 0`): `lift op w = Ret
(op ![])`. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex def:lifted-connective)
theorem lift_zero {W B : Type*} (op : (Fin 0 → W) → B) (w : Fin 0 → MS S W) :
    lift op w = ret (op ![]) := by
  rw [lift_eq_dstN_bind, dstN_zero, ret_bind]
  rfl

/-- Blueprint `def:lifted-connective` (unary case, matching the blueprint's
own iterated-bind description at `n = 1`): `lift op w = w 0 bind λx. Ret
(op ![x])`. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex def:lifted-connective)
theorem lift_one {W B : Type*} (op : (Fin 1 → W) → B) (w : Fin 1 → MS S W) :
    lift op w = bind (w 0) fun x => ret (op ![x]) := by
  rw [lift_eq_dstN_bind, dstN_one, bind_assoc]
  congr 1
  funext x
  rw [ret_bind]
  rfl

/-- Blueprint `def:lifted-connective` (binary case, matching the
blueprint's own iterated-bind description at `n = 2`, the arity used by
`∧, ∨, oplus, otimes`): `lift op ![a, b] = a bind λx. b bind λy. Ret (op ![x,y])`. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex def:lifted-connective)
theorem lift_two {W B : Type*} (op : (Fin 2 → W) → B) (w : Fin 2 → MS S W) :
    lift op w = bind (w 0) fun x => bind (w 1) fun y => ret (op ![x, y]) := by
  rw [lift_eq_dstN_bind, dstN_two, bind_assoc]
  congr 1
  funext x
  rw [bind_assoc]
  congr 1
  funext y
  rw [ret_bind]
  rfl

/-! ### `lift₂`/`lift₁`: ergonomic wrappers at the arities actually used -/

/-- Binary specialization of `lift` (ergonomic wrapper, not a new concept):
`lift₂ op a b` lifts a binary Boolean operation `op` against two
independent truth-space values. Named per `.foreman/C2-T3-spec.md`'s own
suggestion; `lift₂_eq` below recovers the plain two-argument bind chain. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex
-- def:lifted-connective)
noncomputable def lift₂ (op : BoolW → BoolW → BoolW) (a b : MS S BoolW) : MS S BoolW :=
  lift (fun w => op (w 0) (w 1)) ![a, b]

/-- Unary specialization of `lift`: `lift₁ op a` lifts a unary Boolean
operation `op` (used for `¬`) against one truth-space value. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex
-- def:lifted-connective)
noncomputable def lift₁ (op : BoolW → BoolW) (a : MS S BoolW) : MS S BoolW :=
  lift (fun w => op (w 0)) ![a]

/-- `lift₂`'s plain bind-chain form, via `lift_two`: `lift₂ op a b = a bind
λx. b bind λy. Ret (op x y)`. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex
-- def:lifted-connective)
theorem lift₂_eq (op : BoolW → BoolW → BoolW) (a b : MS S BoolW) :
    lift₂ op a b = bind a fun x => bind b fun y => ret (op x y) := by
  unfold lift₂
  rw [lift_two]
  simp

/-- `lift₁`'s plain bind-chain form, via `lift_one`: `lift₁ op a = a bind
λx. Ret (op x)`. -/
-- blueprint: internal (A1 bijection-law companion of `lift`, content.tex
-- def:lifted-connective)
theorem lift₁_eq (op : BoolW → BoolW) (a : MS S BoolW) :
    lift₁ op a = bind a fun x => ret (op x) := by
  unfold lift₁
  rw [lift_one]
  simp

/-- Blueprint `def:lifted-connective` (the `otimes`-lift, "certain conjunction"):
the lifted family's multiplicative connective, `lift₂` of `BoolW`'s own `⊗
= ∧` (`NeSyCat/CategoricalLayer/SemiringMonads/LatticeSemiring.lean`). -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def otimesM (a b : MS S BoolW) : MS S BoolW := lift₂ (· * ·) a b

/-- Blueprint `def:lifted-connective` (the `oplus`-lift, "certain disjunction"):
the lifted family's additive connective, `lift₂` of `BoolW`'s own
`⊕ = ∨`. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def oplusM (a b : MS S BoolW) : MS S BoolW := lift₂ (· + ·) a b

/-- Boolean negation on `BoolW`, stated via a `BoolW`-native `ite` rather
than `Bool.not`/`!` (a disclosed encoding choice): composing `!` — which
needs a `BoolW`-to-`Bool` coercion at elaboration time — with `lift₁`'s
routing machinery reproducibly desynchronizes the `Decidable`-equality
instance baked into a downstream `ite` from the one a fresh statement
about `!x` elaborates, causing spurious `rw`/`motive`-not-type-correct
failures several layers down (`NeSyCat/LogicalLayer/TruthSpaces/Lifted.lean`'s
`twoSlot_negM`); the `ite` form is decided by `BoolW`'s own `DecidableEq`
throughout, with no such boundary to cross. Agrees with `!x` pointwise
(`negOp_eq_not` below) — a genuine Boolean negation, not a weaker
substitute. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
def negOp (x : BoolW) : BoolW := if x = 0 then 1 else 0

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem negOp_eq_not (x : BoolW) : negOp x = !x := by
  unfold negOp
  rcases BoolW_eq_zero_or_one x with rfl | rfl <;> decide

/-- Blueprint `def:lifted-connective` (the `¬`-lift, lifted negation): the
lifted family's unary connective, `lift₁` of Boolean negation (`negOp`,
pointwise equal to `!·` — see `negOp_eq_not`). -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def negM (a : MS S BoolW) : MS S BoolW := lift₁ negOp a

/-! ### `twoSlot`: the workhorse readout equivalence -/

/-- Blueprint `def:two-slot` (the `twoSlot` workhorse):
`MS S BoolW ≃ S × S` via `w ↦ (w 0, w 1)` (slot `0` the weight *against*,
slot `1` the weight *for*), instantiated at `S := ℝ≥0` for the `Tmon`
readout and at `S := LogS` for the `LTmon` readout (`LogTens BoolW = MS
LogS BoolW` by definition, so this equivalence applies to it directly).
Inverse: `single 0 a + single 1 b`, justified by `BoolW`'s exactly-two-point
support (`sum_boolW`'s underlying two-point `Finsupp.ext` argument). -/
noncomputable def twoSlot : MS S BoolW ≃ S × S where
  toFun w := (w 0, w 1)
  invFun p := Finsupp.single 0 p.1 + Finsupp.single 1 p.2
  left_inv w := by
    apply Finsupp.ext
    intro a
    rcases BoolW_eq_zero_or_one a with rfl | rfl
    · simp [Finsupp.add_apply, Finsupp.single_eq_same]
    · simp [Finsupp.add_apply, Finsupp.single_eq_same]
  right_inv p := by
    ext
    · simp [Finsupp.add_apply, Finsupp.single_eq_same]
    · simp [Finsupp.add_apply, Finsupp.single_eq_same]

-- blueprint: internal (A1 bijection-law companion of `twoSlot`, content.tex def:two-slot)
@[simp] theorem twoSlot_apply (w : MS S BoolW) : twoSlot w = (w 0, w 1) := rfl

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[simp] theorem twoSlot_symm_apply (p : S × S) :
    twoSlot.symm p = Finsupp.single 0 p.1 + Finsupp.single 1 p.2 :=
  rfl

/-! ### `distReadout`: the probability readout -/

/-- Blueprint `def:dist-readout` (`Dmon` readout, forward
direction): a `Dist BoolW` value's `1`-coefficient is the point in
`unitInterval`, nonnegative (from `ℝ≥0`) and `≤ 1` by the mass-one
constraint (`d.2`, via `massSum_eq`: `d.1 0 + d.1 1 = 1` forces
`d.1 1 ≤ 1`). -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def distReadoutToFun (d : Dist BoolW) : unitInterval :=
  ⟨(d.1 1 : ℝ), (d.1 1).2, by
    have hmass := d.2
    rw [massSum_eq] at hmass
    have h1 : d.1 1 ≤ 1 := by
      calc d.1 1 ≤ d.1 0 + d.1 1 := le_add_self
        _ = 1 := hmass
    exact_mod_cast h1⟩

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[simp] theorem distReadoutToFun_coe (d : Dist BoolW) :
    (distReadoutToFun d : ℝ) = (d.1 1 : ℝ) :=
  rfl

/-- Blueprint `def:dist-readout` (`Dmon` readout, inverse
direction): a point `p ∈ [0,1]` is completed to the mass-one pair
`(1 - p, p)` — the redundant `p(0)` coefficient of `def:dist-monad`
reconstructed from `p(1) = p`. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def distReadoutInvFun (p : unitInterval) : Dist BoolW :=
  ⟨Finsupp.single 0 ⟨1 - (p : ℝ), by linarith [p.2.2]⟩ + Finsupp.single 1 ⟨(p : ℝ), p.2.1⟩, by
    rw [massSum_eq]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne BoolW_zero_ne_one, Finsupp.single_eq_of_ne BoolW_zero_ne_one.symm,
      add_zero, zero_add]
    apply Subtype.ext
    change (1 - (p : ℝ)) + (p : ℝ) = (1 : ℝ)
    ring⟩

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[simp] theorem distReadoutInvFun_apply_zero (p : unitInterval) :
    (distReadoutInvFun p).1 0 = ⟨1 - (p : ℝ), by linarith [p.2.2]⟩ := by
  simp [distReadoutInvFun, Finsupp.add_apply, Finsupp.single_eq_same]

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[simp] theorem distReadoutInvFun_apply_one (p : unitInterval) :
    (distReadoutInvFun p).1 1 = ⟨(p : ℝ), p.2.1⟩ := by
  simp [distReadoutInvFun, Finsupp.add_apply, Finsupp.single_eq_same]

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem distReadout_left_inv (d : Dist BoolW) : distReadoutInvFun (distReadoutToFun d) = d := by
  apply Subtype.ext
  apply Finsupp.ext
  intro a
  rcases BoolW_eq_zero_or_one a with rfl | rfl
  · rw [distReadoutInvFun_apply_zero]
    have hmass := d.2
    rw [massSum_eq] at hmass
    apply Subtype.ext
    change (1 : ℝ) - (distReadoutToFun d : ℝ) = (d.1 0 : ℝ)
    rw [distReadoutToFun_coe]
    have hcast : (d.1 0 : ℝ) + (d.1 1 : ℝ) = 1 := by exact_mod_cast hmass
    linarith
  · rw [distReadoutInvFun_apply_one]
    apply Subtype.ext
    rw [distReadoutToFun_coe]
    rfl

-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
theorem distReadout_right_inv (p : unitInterval) : distReadoutToFun (distReadoutInvFun p) = p := by
  apply Subtype.ext
  rw [distReadoutToFun_coe, distReadoutInvFun_apply_one]
  rfl

/-- Blueprint `def:dist-readout` (`Dmon BoolS ≅ ProbS`):
`p ↦ p(1)` is an equivalence `Dist BoolW ≃ unitInterval`, forgetting the
redundant coefficient `p(0) = 1 - p(1)` forced by the mass-one constraint
of `def:dist-monad`. Single-stage construction (see the module doc
comment for the disclosed deviation from the two-stage route sketched in
`.foreman/C2-T3-spec.md`). -/
noncomputable def distReadout : Dist BoolW ≃ unitInterval where
  toFun := distReadoutToFun
  invFun := distReadoutInvFun
  left_inv := distReadout_left_inv
  right_inv := distReadout_right_inv

-- blueprint: internal (A1 bijection-law companion of `distReadout`, content.tex def:dist-readout)
@[simp] theorem distReadout_apply_coe (d : Dist BoolW) :
    (distReadout d : ℝ) = (d.1 1 : ℝ) :=
  rfl

end NeSyCat
