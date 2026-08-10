/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.StatisticalLayer.BridgesNormalization.Tilt

/-!
# The chain bound: how wrong can it get

Blueprint items `thm:chain-bound-sandwich` and `thm:chain-bound`
(`blueprint/src/content.tex`, §"Bridges and normalization"), the library's
former standing open problem, resolved here (C3-CB): if every bind `k_i` of
a pull-out chain `Φ` (`PulloutChain`, `thm:pullout`) has its per-index mass
sandwiched, `m_i ≤ Z(k_i(x)) ≤ M_i` for all `x` (`HasMassBounds`), then at
every outcome `y` the two truth values satisfy `|log t_Tmon − log t_Dmon| ≤
Σ_i log(M_i/m_i)`, with equality exactly when every `M_i = m_i`.

Split into two blueprint theorems at C3-E12's CB-RESTRUCT (USER DECREE
2026-08-10): `thm:chain-bound-sandwich` (`chain_bound_sandwich`) is the
hypothesis-free multiplicative sandwich promoted to its own cited
principal, and `thm:chain-bound` (`chain_bound`) is the log form below it,
citing the sandwich by `\uses`. No Lean change from the restructure: both
declarations already existed (`chain_bound_sandwich` was previously an
unmarked internal companion of `chain_bound`).

The proof route is a division-free multiplicative sandwich pushed through
the chain by structural induction (`chain_bound_sandwich`): writing
`lbProd`/`ubProd` for the products `Π_i m_i`/`Π_i M_i`,

  `Π m_i · dec(Φ_Tmon)(y) ≤ Π M_i · Φ_Dmon(y)`   and
  `Π m_i · Φ_Dmon(y) ≤ Π M_i · dec(Φ_Tmon)(y)`.

Stated this way the sandwich needs NO positivity hypotheses: every
degenerate case collapses under the ambient `0⁻¹ = 0` convention of `dec`
(`def:dec-enc-mass`). Non-bind factors preserve the sandwich exactly (a
pure map reindexes fiber sums, `lem:pure-maps`; a tensor factor multiplies
both sides by one common factor, `lem:tensor`/`lem:units`); a bind factor
widens it by exactly `[m_i, M_i]` (`bind_layer_sandwich`, a three-step
estimate on the matrix-multiplication form of bind, `lem:bind-matrix-mult`
via `dec_mul_Z`/`Z_bind`). The blueprint's log form follows by taking
logarithms (`log_ratio_sum`) under the statement's own tacit positivity
(`0 < m_i ≤ M_i` and `t_Dmon(y) > 0`; positivity of `t_Tmon(y)` is then
derivable, not assumed).

The equality clause: if every `M_i = m_i` the bounds force every bind to
be mass preserving (`allMassPreserving_of_bounds_eq`), so `thm:pullout`
gives `t_Tmon = t_Dmon` and both sides of the bound vanish. Conversely,
attaining the bound at an outcome with `t_Dmon(y) > 0` forces every
inequality of the sandwich chain to be an equality; termwise extraction
(`Finset.sum_eq_sum_iff_of_le`) then pins `Z(k_i) = m_i` and `Z(k_i) =
M_i` simultaneously at a witness index of positive weight
(`bind_layer_eq_upper`/`bind_layer_eq_lower`), hence `M_i = m_i`, and
hands the attained sandwich equality down the chain
(`chain_bound_eq_upper`/`chain_bound_eq_lower`).
-/

namespace NeSyCat

open scoped NNReal

variable {X Y Z' : Type*}

/-! ### Bound lists and their products -/

/-- The per-bind mass-bound hypothesis of `thm:chain-bound`: one pair
`(m_i, M_i)` per `bindStep` of the chain, outermost bind first, with
`m_i ≤ Z(k_i(x)) ≤ M_i` for every `x`; non-bind factors consume no pair. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
def PulloutChain.HasMassBounds : {W : Type} → PulloutChain W → List (ℝ≥0 × ℝ≥0) → Prop
  | _, .base _, bs => bs = []
  | _, .pureMap _ rest, bs => rest.HasMassBounds bs
  | _, .unitIns _ rest, bs => rest.HasMassBounds bs
  | _, .strengthStep _ rest, bs => rest.HasMassBounds bs
  | _, .bindStep _ _, [] => False
  | _, .bindStep k rest, b :: bs =>
      (∀ x, b.1 ≤ Z (k x) ∧ Z (k x) ≤ b.2) ∧ rest.HasMassBounds bs

/-- `Π_i m_i`, the product of the lower mass bounds. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
def lbProd (bs : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 := (bs.map Prod.fst).prod

/-- `Π_i M_i`, the product of the upper mass bounds. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
def ubProd (bs : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 := (bs.map Prod.snd).prod

-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem lbProd_nil : lbProd ([] : List (ℝ≥0 × ℝ≥0)) = 1 := rfl

-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem ubProd_nil : ubProd ([] : List (ℝ≥0 × ℝ≥0)) = 1 := rfl

-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem lbProd_cons (b : ℝ≥0 × ℝ≥0) (bs : List (ℝ≥0 × ℝ≥0)) :
    lbProd (b :: bs) = b.1 * lbProd bs := by
  simp [lbProd]

-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem ubProd_cons (b : ℝ≥0 × ℝ≥0) (bs : List (ℝ≥0 × ℝ≥0)) :
    ubProd (b :: bs) = b.2 * ubProd bs := by
  simp [ubProd]

-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem lbProd_pos {bs : List (ℝ≥0 × ℝ≥0)} (hb : ∀ b ∈ bs, 0 < b.1) :
    0 < lbProd bs := by
  induction bs with
  | nil => exact one_pos
  | cons b bs ih =>
      rw [lbProd_cons]
      exact mul_pos (hb b (by simp)) (ih fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))

-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem ubProd_pos {bs : List (ℝ≥0 × ℝ≥0)} (hb : ∀ b ∈ bs, 0 < b.2) :
    0 < ubProd bs := by
  induction bs with
  | nil => exact one_pos
  | cons b bs ih =>
      rw [ubProd_cons]
      exact mul_pos (hb b (by simp)) (ih fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))

/-! ### `Finsupp` plumbing -/

/-- `mapDomain` applied at a point, as a `Finset` fiber sum over any
superset of the support: `(mapDomain h p)(y) = Σ_{x ∈ s} [h x = y]·p(x)`. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem mapDomain_apply_sum [DecidableEq Y] (h : X → Y) (p : Tens X) {s : Finset X}
    (hs : p.support ⊆ s) (y : Y) :
    Finsupp.mapDomain h p y = ∑ x ∈ s, if h x = y then p x else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply,
    Finsupp.sum_of_support_subset p hs _ (fun i _ => by simp)]
  exact Finset.sum_congr rfl fun x _ => Finsupp.single_apply

/-- The two-sided sandwich `L·p ≤ U·q`, `L·q ≤ U·p` survives multiplying
both members by one common factor `r`, the tensor-factor step of
`chain_bound_sandwich`. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem sandwich_mul_right {L U p q r : ℝ≥0} (h : L * p ≤ U * q) :
    L * (p * r) ≤ U * (q * r) := by
  calc L * (p * r) = L * p * r := by ring
    _ ≤ U * q * r := mul_le_mul_left h r
    _ = U * (q * r) := by ring

/-- Cancelling one common nonzero factor `r` out of an attained sandwich
equality `L·(v·r) = U·(w·r)`, the tensor-factor step of the equality
converse. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem eq_of_mul_mul_right_cancel {L U v w r : ℝ≥0} (hr : r ≠ 0)
    (h : L * (v * r) = U * (w * r)) : L * v = U * w := by
  have h' : L * v * r = U * w * r := by
    calc L * v * r = L * (v * r) := by ring
      _ = U * (w * r) := h
      _ = U * w * r := by ring
  exact mul_right_cancel₀ hr h'

/-! ### One bind layer -/

section BindLayer

variable {B C : Type} (a : LogTens B) (q : Tens B) (k : B → LogTens C)

/-- The numerator of `dec (bind a k)` at `y`, as a `Finset` sum over any
superset of the support, with the per-index mass split off each term
(`dec_mul_Z`): `(ofLogTens (bind a k))(y) = Σ_x A(x)·(dec(k x)(y)·Z(k x))`. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem bind_num_eq_sum {s : Finset B} (hs : (ofLogTens a).support ⊆ s) (y : C) :
    ofLogTens (bind a k) y
      = ∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)) := by
  have h1 : (ofLogTens a).sum (fun x w => w * ofLogTens (k x) y)
      = ∑ x ∈ s, ofLogTens a x * ofLogTens (k x) y :=
    Finsupp.sum_of_support_subset _ hs _ (fun _ _ => zero_mul _)
  rw [ofLogTens_bind, bind_apply, h1]
  exact Finset.sum_congr rfl fun x _ => by rw [dec_mul_Z]

/-- The mass of `bind a k` as a `Finset` sum over any superset of the
support (`Z_bind` extended off the support). -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem Z_bind_eq_sum {s : Finset B} (hs : (ofLogTens a).support ⊆ s) :
    Z (bind a k) = ∑ x ∈ s, ofLogTens a x * Z (k x) := by
  rw [Z_bind]
  exact Finsupp.sum_of_support_subset _ hs _ (fun i _ => zero_mul _)

/-- The mass of `a` as a `Finset` sum over any superset of the support. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem Z_eq_finset_sum {s : Finset B} (hs : (ofLogTens a).support ⊆ s) :
    Z a = ∑ x ∈ s, ofLogTens a x :=
  Finsupp.sum_of_support_subset _ hs _ (fun i _ => rfl)

/-- The `Dmon`-side bind at `y` as a `Finset` sum over any superset of the
support. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem bind_dec_eq_sum {s : Finset B} (hs : q.support ⊆ s) (y : C) :
    bind q (fun x => dec (k x)) y = ∑ x ∈ s, q x * dec (k x) y := by
  rw [bind_apply]
  exact Finsupp.sum_of_support_subset _ hs _ (fun i _ => zero_mul _)

/-- One bind layer of the division-free sandwich: if `m ≤ Z(k x) ≤ M` for
every `x`, and `dec(a)` and `q` satisfy the two-sided pointwise sandwich
`L·dec(a) ≤ U·q` and `L·q ≤ U·dec(a)`, then the widened pair `(mL, MU)`
sandwiches `dec(bind a k)` against `bind q (k ⨟ dec)` the same two-sided
way. No positivity is assumed: every degenerate case collapses under the
`0⁻¹ = 0` convention. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem bind_layer_sandwich {m M L U : ℝ≥0}
    (hk : ∀ x, m ≤ Z (k x) ∧ Z (k x) ≤ M)
    (hA : ∀ x, L * dec a x ≤ U * q x)
    (hB : ∀ x, L * q x ≤ U * dec a x)
    (y : C) :
    m * L * dec (bind a k) y ≤ M * U * bind q (fun x => dec (k x)) y ∧
      m * L * bind q (fun x => dec (k x)) y ≤ M * U * dec (bind a k) y := by
  classical
  set s : Finset B := (ofLogTens a).support ∪ q.support with hs_def
  have hsubA : (ofLogTens a).support ⊆ s := Finset.subset_union_left
  have hsubq : q.support ⊆ s := Finset.subset_union_right
  have hDv := bind_dec_eq_sum q k hsubq y
  have hTv : dec (bind a k) y
      = (∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)))
        / (∑ x ∈ s, ofLogTens a x * Z (k x)) := by
    rw [dec_apply, bind_num_eq_sum a k hsubA y, Z_bind_eq_sum a k hsubA]
  have hZR := Z_eq_finset_sum a hsubA
  set N : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)) with hN_def
  set Zb : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * Z (k x) with hZb_def
  set ZR : ℝ≥0 := ∑ x ∈ s, ofLogTens a x with hZR_def
  set Dv : ℝ≥0 := ∑ x ∈ s, q x * dec (k x) y with hDv_def
  set SAg : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * dec (k x) y with hSAg_def
  clear_value N Zb ZR Dv SAg
  -- termwise estimates
  have hterm1 : ∀ x, ofLogTens a x * (dec (k x) y * Z (k x))
      ≤ M * (ofLogTens a x * dec (k x) y) := fun x =>
    calc ofLogTens a x * (dec (k x) y * Z (k x))
        = ofLogTens a x * dec (k x) y * Z (k x) := by ring
      _ ≤ ofLogTens a x * dec (k x) y * M := mul_le_mul_right (hk x).2 _
      _ = M * (ofLogTens a x * dec (k x) y) := by ring
  have hterm1' : ∀ x, m * (ofLogTens a x * dec (k x) y)
      ≤ ofLogTens a x * (dec (k x) y * Z (k x)) := fun x =>
    calc m * (ofLogTens a x * dec (k x) y)
        = ofLogTens a x * dec (k x) y * m := by ring
      _ ≤ ofLogTens a x * dec (k x) y * Z (k x) := mul_le_mul_right (hk x).1 _
      _ = ofLogTens a x * (dec (k x) y * Z (k x)) := by ring
  have hterm3 : ∀ x, m * ofLogTens a x ≤ ofLogTens a x * Z (k x) := fun x =>
    calc m * ofLogTens a x = ofLogTens a x * m := by ring
      _ ≤ ofLogTens a x * Z (k x) := mul_le_mul_right (hk x).1 _
  have hterm3' : ∀ x, ofLogTens a x * Z (k x) ≤ M * ofLogTens a x := fun x =>
    calc ofLogTens a x * Z (k x) ≤ ofLogTens a x * M := mul_le_mul_right (hk x).2 _
      _ = M * ofLogTens a x := by ring
  -- the aggregated estimates
  have est1 : N ≤ M * SAg := by
    rw [hN_def, hSAg_def, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hterm1 x
  have est1' : m * SAg ≤ N := by
    rw [hN_def, hSAg_def, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hterm1' x
  have hLSAg : L * SAg = ∑ x ∈ s, ZR * (L * dec a x * dec (k x) y) := by
    rw [hSAg_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show ofLogTens a x = dec a x * Z a from (dec_mul_Z a x).symm, hZR]
    ring
  have hUDv : ZR * (U * Dv) = ∑ x ∈ s, ZR * (U * q x * dec (k x) y) := by
    rw [hDv_def, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have est2 : L * SAg ≤ ZR * (U * Dv) := by
    rw [hLSAg, hUDv]
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul_right (mul_le_mul_left (hA x) _) _
  have hLDvZR : L * Dv * ZR = ∑ x ∈ s, L * q x * (dec (k x) y * ZR) := by
    rw [hDv_def, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hUSAg : U * SAg = ∑ x ∈ s, U * dec a x * (dec (k x) y * ZR) := by
    rw [hSAg_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show ofLogTens a x = dec a x * Z a from (dec_mul_Z a x).symm, hZR]
    ring
  have est2' : L * Dv * ZR ≤ U * SAg := by
    rw [hLDvZR, hUSAg]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_left (hB x) _
  have est3 : m * ZR ≤ Zb := by
    rw [hZR_def, hZb_def, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hterm3 x
  have est3' : Zb ≤ M * ZR := by
    rw [hZR_def, hZb_def, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hterm3' x
  rw [hTv, hDv]
  constructor
  · -- upper: m·L·(N/Zb) ≤ M·U·Dv
    rw [← mul_div_assoc]
    refine NNReal.div_le_of_le_mul ?_
    calc m * L * N ≤ m * L * (M * SAg) := mul_le_mul_right est1 _
      _ = m * M * (L * SAg) := by ring
      _ ≤ m * M * (ZR * (U * Dv)) := mul_le_mul_right est2 _
      _ = M * U * Dv * (m * ZR) := by ring
      _ ≤ M * U * Dv * Zb := mul_le_mul_right est3 _
  · -- lower: m·L·Dv ≤ M·U·(N/Zb)
    by_cases hZb0 : Zb = 0
    · rw [hZb0, div_zero, mul_zero]
      by_cases hm0 : m = 0
      · rw [hm0, zero_mul, zero_mul]
      · by_cases hL0 : L = 0
        · rw [hL0, mul_zero, zero_mul]
        · -- m, L ≠ 0 and Zb = 0 force Dv = 0
          have hall : ∀ x ∈ s, ofLogTens a x * Z (k x) = 0 :=
            Finset.sum_eq_zero_iff.mp (by rw [← hZb_def]; exact hZb0)
          have hq0 : ∀ x ∈ s, q x = 0 := by
            intro x hx
            have hw : Z (k x) ≠ 0 :=
              (lt_of_lt_of_le (pos_iff_ne_zero.mpr hm0) (hk x).1).ne'
            have hAx : ofLogTens a x = 0 := by
              rcases mul_eq_zero.mp (hall x hx) with h | h
              · exact h
              · exact absurd h hw
            have hpx : dec a x = 0 := by rw [dec_apply, hAx, zero_div]
            have hle := hB x
            rw [hpx, mul_zero] at hle
            rcases mul_eq_zero.mp (le_antisymm hle zero_le) with h | h
            · exact absurd h hL0
            · exact h
          have hDv0 : Dv = 0 := by
            rw [hDv_def]
            exact Finset.sum_eq_zero fun x hx => by rw [hq0 x hx, zero_mul]
          rw [hDv0, mul_zero]
    · rw [← mul_div_assoc, le_div_iff₀ (pos_iff_ne_zero.mpr hZb0)]
      calc m * L * Dv * Zb ≤ m * L * Dv * (M * ZR) := mul_le_mul_right est3' _
        _ = m * M * (L * Dv * ZR) := by ring
        _ ≤ m * M * (U * SAg) := mul_le_mul_right est2' _
        _ = M * U * (m * SAg) := by ring
        _ ≤ M * U * N := mul_le_mul_right est1' _

/-- The upper attainment analysis for one bind layer: if the widened upper
bound `mL·dec(bind a k)(y) = MU·(bind q (k ⨟ dec))(y)` is attained at an
outcome of positive `Dmon` weight, every estimate of the sandwich chain is
forced tight, so `Z(k) = m` and `Z(k) = M` hold simultaneously at a
witness index of positive weight, giving `M = m` and handing the attained
sandwich equality `L·dec(a) = U·q` down to that witness. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem bind_layer_eq_upper {m M L U : ℝ≥0}
    (hm : m ≠ 0) (hM : m ≤ M) (hL : L ≠ 0) (hU : U ≠ 0)
    (hk : ∀ x, m ≤ Z (k x) ∧ Z (k x) ≤ M)
    (hA : ∀ x, L * dec a x ≤ U * q x)
    (hB : ∀ x, L * q x ≤ U * dec a x)
    (y : C) (hD : 0 < bind q (fun x => dec (k x)) y)
    (heq : m * L * dec (bind a k) y = M * U * bind q (fun x => dec (k x)) y) :
    M = m ∧ ∃ x, q x ≠ 0 ∧ L * dec a x = U * q x := by
  classical
  set s : Finset B := (ofLogTens a).support ∪ q.support with hs_def
  have hsubA : (ofLogTens a).support ⊆ s := Finset.subset_union_left
  have hsubq : q.support ⊆ s := Finset.subset_union_right
  have hDv := bind_dec_eq_sum q k hsubq y
  have hTv : dec (bind a k) y
      = (∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)))
        / (∑ x ∈ s, ofLogTens a x * Z (k x)) := by
    rw [dec_apply, bind_num_eq_sum a k hsubA y, Z_bind_eq_sum a k hsubA]
  have hZR := Z_eq_finset_sum a hsubA
  set N : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)) with hN_def
  set Zb : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * Z (k x) with hZb_def
  set ZR : ℝ≥0 := ∑ x ∈ s, ofLogTens a x with hZR_def
  set Dv : ℝ≥0 := ∑ x ∈ s, q x * dec (k x) y with hDv_def
  set SAg : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * dec (k x) y with hSAg_def
  clear_value N Zb ZR Dv SAg
  rw [hDv] at hD
  rw [hTv, hDv] at heq
  have hM0 : M ≠ 0 := fun h0 => hm (le_antisymm (h0 ▸ hM) zero_le)
  have hDvne : Dv ≠ 0 := hD.ne'
  have hRHS : M * U * Dv ≠ 0 := mul_ne_zero (mul_ne_zero hM0 hU) hDvne
  have hTne : N / Zb ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at heq
    exact hRHS heq.symm
  have hZbne : Zb ≠ 0 := fun h0 => hTne (by rw [h0, div_zero])
  -- termwise estimates (as in the sandwich)
  have hterm1 : ∀ x, ofLogTens a x * (dec (k x) y * Z (k x))
      ≤ M * (ofLogTens a x * dec (k x) y) := fun x =>
    calc ofLogTens a x * (dec (k x) y * Z (k x))
        = ofLogTens a x * dec (k x) y * Z (k x) := by ring
      _ ≤ ofLogTens a x * dec (k x) y * M := mul_le_mul_right (hk x).2 _
      _ = M * (ofLogTens a x * dec (k x) y) := by ring
  have hterm3 : ∀ x, m * ofLogTens a x ≤ ofLogTens a x * Z (k x) := fun x =>
    calc m * ofLogTens a x = ofLogTens a x * m := by ring
      _ ≤ ofLogTens a x * Z (k x) := mul_le_mul_right (hk x).1 _
  have est1 : N ≤ M * SAg := by
    rw [hN_def, hSAg_def, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hterm1 x
  have hLSAg : L * SAg = ∑ x ∈ s, ZR * (L * dec a x * dec (k x) y) := by
    rw [hSAg_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show ofLogTens a x = dec a x * Z a from (dec_mul_Z a x).symm, hZR]
    ring
  have hUDv : ZR * (U * Dv) = ∑ x ∈ s, ZR * (U * q x * dec (k x) y) := by
    rw [hDv_def, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have est2 : L * SAg ≤ ZR * (U * Dv) := by
    rw [hLSAg, hUDv]
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul_right (mul_le_mul_left (hA x) _) _
  have est3 : m * ZR ≤ Zb := by
    rw [hZR_def, hZb_def, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hterm3 x
  have est3' : Zb ≤ M * ZR := by
    rw [hZR_def, hZb_def, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc ofLogTens a x * Z (k x) ≤ ofLogTens a x * M := mul_le_mul_right (hk x).2 _
      _ = M * ofLogTens a x := by ring
  have hZRne : ZR ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at est3'
    exact hZbne (le_antisymm est3' zero_le)
  -- clear the denominator
  have heq' : m * L * N = M * U * Dv * Zb := by
    calc m * L * N = m * L * (N / Zb * Zb) := by rw [div_mul_cancel₀ N hZbne]
      _ = m * L * (N / Zb) * Zb := by ring
      _ = M * U * Dv * Zb := by rw [heq]
  -- force every estimate tight
  have eq1 : m * L * N = m * L * (M * SAg) := by
    refine le_antisymm (mul_le_mul_right est1 _) ?_
    rw [heq']
    calc m * L * (M * SAg) = m * M * (L * SAg) := by ring
      _ ≤ m * M * (ZR * (U * Dv)) := mul_le_mul_right est2 _
      _ = M * U * Dv * (m * ZR) := by ring
      _ ≤ M * U * Dv * Zb := mul_le_mul_right est3 _
  have hNeq : N = M * SAg := mul_left_cancel₀ (mul_ne_zero hm hL) eq1
  have eq2 : m * M * (L * SAg) = m * M * (ZR * (U * Dv)) := by
    refine le_antisymm (mul_le_mul_right est2 _) ?_
    calc m * M * (ZR * (U * Dv)) = M * U * Dv * (m * ZR) := by ring
      _ ≤ M * U * Dv * Zb := mul_le_mul_right est3 _
      _ = m * L * N := heq'.symm
      _ = m * L * (M * SAg) := eq1
      _ = m * M * (L * SAg) := by ring
  have hSeq : L * SAg = ZR * (U * Dv) := mul_left_cancel₀ (mul_ne_zero hm hM0) eq2
  have eq3 : M * U * Dv * (m * ZR) = M * U * Dv * Zb := by
    refine le_antisymm (mul_le_mul_right est3 _) ?_
    calc M * U * Dv * Zb = m * L * N := heq'.symm
      _ = m * L * (M * SAg) := eq1
      _ = m * M * (L * SAg) := by ring
      _ ≤ m * M * (ZR * (U * Dv)) := mul_le_mul_right est2 _
      _ = M * U * Dv * (m * ZR) := by ring
  have hZeq : m * ZR = Zb := mul_left_cancel₀ hRHS eq3
  -- termwise equalities
  have T1 : ∀ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x))
      = M * (ofLogTens a x * dec (k x) y) := by
    have hsum : (∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)))
        = ∑ x ∈ s, M * (ofLogTens a x * dec (k x) y) := by
      rw [← hN_def, hNeq, hSAg_def, Finset.mul_sum]
    exact fun x hx =>
      (Finset.sum_eq_sum_iff_of_le fun x _ => hterm1 x).mp hsum x hx
  have T2 : ∀ x ∈ s, ZR * (L * dec a x * dec (k x) y)
      = ZR * (U * q x * dec (k x) y) := by
    have hsum : (∑ x ∈ s, ZR * (L * dec a x * dec (k x) y))
        = ∑ x ∈ s, ZR * (U * q x * dec (k x) y) := by
      rw [← hLSAg, ← hUDv, hSeq]
    exact fun x hx =>
      (Finset.sum_eq_sum_iff_of_le fun x _ =>
        mul_le_mul_right (mul_le_mul_left (hA x) _) _).mp hsum x hx
  have T3 : ∀ x ∈ s, m * ofLogTens a x = ofLogTens a x * Z (k x) := by
    have hsum : (∑ x ∈ s, m * ofLogTens a x)
        = ∑ x ∈ s, ofLogTens a x * Z (k x) := by
      rw [← Finset.mul_sum, ← hZR_def, ← hZb_def, hZeq]
    exact fun x hx =>
      (Finset.sum_eq_sum_iff_of_le fun x _ => hterm3 x).mp hsum x hx
  -- the witness index
  have hDvsum : (∑ x ∈ s, q x * dec (k x) y) ≠ 0 := by
    rw [← hDv_def]; exact hDvne
  obtain ⟨x₀, hx₀s, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hDvsum
  have hq₀ : q x₀ ≠ 0 := fun h0 => hx₀ (by rw [h0, zero_mul])
  have hg₀ : dec (k x₀) y ≠ 0 := fun h0 => hx₀ (by rw [h0, mul_zero])
  have hp₀ : dec a x₀ ≠ 0 := by
    intro h0
    have hle := hB x₀
    rw [h0, mul_zero] at hle
    exact mul_ne_zero hL hq₀ (le_antisymm hle zero_le)
  have hA₀ : ofLogTens a x₀ ≠ 0 := by
    rw [← dec_mul_Z a x₀]
    exact mul_ne_zero hp₀ (by rw [hZR]; exact hZRne)
  -- Z(k x₀) = m and Z(k x₀) = M
  have hw_m : Z (k x₀) = m := by
    have h' : ofLogTens a x₀ * m = ofLogTens a x₀ * Z (k x₀) := by
      calc ofLogTens a x₀ * m = m * ofLogTens a x₀ := by ring
        _ = ofLogTens a x₀ * Z (k x₀) := T3 x₀ hx₀s
    exact (mul_left_cancel₀ hA₀ h').symm
  have hw_M : Z (k x₀) = M := by
    have h' : ofLogTens a x₀ * dec (k x₀) y * Z (k x₀)
        = ofLogTens a x₀ * dec (k x₀) y * M := by
      calc ofLogTens a x₀ * dec (k x₀) y * Z (k x₀)
          = ofLogTens a x₀ * (dec (k x₀) y * Z (k x₀)) := by ring
        _ = M * (ofLogTens a x₀ * dec (k x₀) y) := T1 x₀ hx₀s
        _ = ofLogTens a x₀ * dec (k x₀) y * M := by ring
    exact mul_left_cancel₀ (mul_ne_zero hA₀ hg₀) h'
  have hat : L * dec a x₀ = U * q x₀ :=
    mul_right_cancel₀ hg₀ (mul_left_cancel₀ hZRne (T2 x₀ hx₀s))
  exact ⟨hw_M.symm.trans hw_m, x₀, hq₀, hat⟩

/-- The lower attainment analysis for one bind layer, the mirror of
`bind_layer_eq_upper`: attaining `mL·(bind q (k ⨟ dec))(y) =
MU·dec(bind a k)(y)` at an outcome of positive `Dmon` weight forces
`M = m` and hands the attained lower sandwich equality `L·q = U·dec(a)`
down to a witness index of positive weight. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem bind_layer_eq_lower {m M L U : ℝ≥0}
    (hm : m ≠ 0) (hM : m ≤ M) (hL : L ≠ 0) (hU : U ≠ 0)
    (hk : ∀ x, m ≤ Z (k x) ∧ Z (k x) ≤ M)
    (_hA : ∀ x, L * dec a x ≤ U * q x)
    (hB : ∀ x, L * q x ≤ U * dec a x)
    (y : C) (hD : 0 < bind q (fun x => dec (k x)) y)
    (heq : m * L * bind q (fun x => dec (k x)) y = M * U * dec (bind a k) y) :
    M = m ∧ ∃ x, q x ≠ 0 ∧ L * q x = U * dec a x := by
  classical
  set s : Finset B := (ofLogTens a).support ∪ q.support with hs_def
  have hsubA : (ofLogTens a).support ⊆ s := Finset.subset_union_left
  have hsubq : q.support ⊆ s := Finset.subset_union_right
  have hDv := bind_dec_eq_sum q k hsubq y
  have hTv : dec (bind a k) y
      = (∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)))
        / (∑ x ∈ s, ofLogTens a x * Z (k x)) := by
    rw [dec_apply, bind_num_eq_sum a k hsubA y, Z_bind_eq_sum a k hsubA]
  have hZR := Z_eq_finset_sum a hsubA
  set N : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)) with hN_def
  set Zb : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * Z (k x) with hZb_def
  set ZR : ℝ≥0 := ∑ x ∈ s, ofLogTens a x with hZR_def
  set Dv : ℝ≥0 := ∑ x ∈ s, q x * dec (k x) y with hDv_def
  set SAg : ℝ≥0 := ∑ x ∈ s, ofLogTens a x * dec (k x) y with hSAg_def
  clear_value N Zb ZR Dv SAg
  rw [hDv] at hD
  rw [hTv, hDv] at heq
  have hM0 : M ≠ 0 := fun h0 => hm (le_antisymm (h0 ▸ hM) zero_le)
  have hDvne : Dv ≠ 0 := hD.ne'
  have hLHS : m * L * Dv ≠ 0 := mul_ne_zero (mul_ne_zero hm hL) hDvne
  have hTne : N / Zb ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at heq
    exact hLHS heq
  have hZbne : Zb ≠ 0 := fun h0 => hTne (by rw [h0, div_zero])
  -- termwise estimates
  have hterm1' : ∀ x, m * (ofLogTens a x * dec (k x) y)
      ≤ ofLogTens a x * (dec (k x) y * Z (k x)) := fun x =>
    calc m * (ofLogTens a x * dec (k x) y)
        = ofLogTens a x * dec (k x) y * m := by ring
      _ ≤ ofLogTens a x * dec (k x) y * Z (k x) := mul_le_mul_right (hk x).1 _
      _ = ofLogTens a x * (dec (k x) y * Z (k x)) := by ring
  have hterm3' : ∀ x, ofLogTens a x * Z (k x) ≤ M * ofLogTens a x := fun x =>
    calc ofLogTens a x * Z (k x) ≤ ofLogTens a x * M := mul_le_mul_right (hk x).2 _
      _ = M * ofLogTens a x := by ring
  have est1' : m * SAg ≤ N := by
    rw [hN_def, hSAg_def, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hterm1' x
  have hLDvZR : L * Dv * ZR = ∑ x ∈ s, L * q x * (dec (k x) y * ZR) := by
    rw [hDv_def, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hUSAg : U * SAg = ∑ x ∈ s, U * dec a x * (dec (k x) y * ZR) := by
    rw [hSAg_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show ofLogTens a x = dec a x * Z a from (dec_mul_Z a x).symm, hZR]
    ring
  have est2' : L * Dv * ZR ≤ U * SAg := by
    rw [hLDvZR, hUSAg]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_left (hB x) _
  have est3' : Zb ≤ M * ZR := by
    rw [hZR_def, hZb_def, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hterm3' x
  have hZRne : ZR ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at est3'
    exact hZbne (le_antisymm est3' zero_le)
  -- clear the denominator
  have heq' : m * L * Dv * Zb = M * U * N := by
    calc m * L * Dv * Zb = M * U * (N / Zb) * Zb := by rw [heq]
      _ = M * U * (N / Zb * Zb) := by ring
      _ = M * U * N := by rw [div_mul_cancel₀ N hZbne]
  -- force every estimate tight
  have eq1 : m * L * Dv * Zb = m * L * Dv * (M * ZR) := by
    refine le_antisymm (mul_le_mul_right est3' _) ?_
    rw [heq']
    calc m * L * Dv * (M * ZR) = m * M * (L * Dv * ZR) := by ring
      _ ≤ m * M * (U * SAg) := mul_le_mul_right est2' _
      _ = M * U * (m * SAg) := by ring
      _ ≤ M * U * N := mul_le_mul_right est1' _
  have hZbeq : Zb = M * ZR := mul_left_cancel₀ hLHS eq1
  have eq2 : m * M * (L * Dv * ZR) = m * M * (U * SAg) := by
    refine le_antisymm (mul_le_mul_right est2' _) ?_
    calc m * M * (U * SAg) = M * U * (m * SAg) := by ring
      _ ≤ M * U * N := mul_le_mul_right est1' _
      _ = m * L * Dv * Zb := heq'.symm
      _ = m * L * Dv * (M * ZR) := eq1
      _ = m * M * (L * Dv * ZR) := by ring
  have hSeq : L * Dv * ZR = U * SAg := mul_left_cancel₀ (mul_ne_zero hm hM0) eq2
  have eq3 : M * U * (m * SAg) = M * U * N := by
    refine le_antisymm (mul_le_mul_right est1' _) ?_
    calc M * U * N = m * L * Dv * Zb := heq'.symm
      _ = m * L * Dv * (M * ZR) := eq1
      _ = m * M * (L * Dv * ZR) := by ring
      _ ≤ m * M * (U * SAg) := mul_le_mul_right est2' _
      _ = M * U * (m * SAg) := by ring
  have hNeq : m * SAg = N := mul_left_cancel₀ (mul_ne_zero hM0 hU) eq3
  -- termwise equalities
  have J1 : ∀ x ∈ s, ofLogTens a x * Z (k x) = M * ofLogTens a x := by
    have hsum : (∑ x ∈ s, ofLogTens a x * Z (k x))
        = ∑ x ∈ s, M * ofLogTens a x := by
      rw [← hZb_def, hZbeq, hZR_def, Finset.mul_sum]
    exact fun x hx =>
      (Finset.sum_eq_sum_iff_of_le fun x _ => hterm3' x).mp hsum x hx
  have J2 : ∀ x ∈ s, L * q x * (dec (k x) y * ZR)
      = U * dec a x * (dec (k x) y * ZR) := by
    have hsum : (∑ x ∈ s, L * q x * (dec (k x) y * ZR))
        = ∑ x ∈ s, U * dec a x * (dec (k x) y * ZR) := by
      rw [← hLDvZR, ← hUSAg, hSeq]
    exact fun x hx =>
      (Finset.sum_eq_sum_iff_of_le fun x _ =>
        mul_le_mul_left (hB x) _).mp hsum x hx
  have J3 : ∀ x ∈ s, m * (ofLogTens a x * dec (k x) y)
      = ofLogTens a x * (dec (k x) y * Z (k x)) := by
    have hsum : (∑ x ∈ s, m * (ofLogTens a x * dec (k x) y))
        = ∑ x ∈ s, ofLogTens a x * (dec (k x) y * Z (k x)) := by
      rw [← Finset.mul_sum, ← hSAg_def, ← hN_def, hNeq]
    exact fun x hx =>
      (Finset.sum_eq_sum_iff_of_le fun x _ => hterm1' x).mp hsum x hx
  -- the witness index
  have hDvsum : (∑ x ∈ s, q x * dec (k x) y) ≠ 0 := by
    rw [← hDv_def]; exact hDvne
  obtain ⟨x₀, hx₀s, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hDvsum
  have hq₀ : q x₀ ≠ 0 := fun h0 => hx₀ (by rw [h0, zero_mul])
  have hg₀ : dec (k x₀) y ≠ 0 := fun h0 => hx₀ (by rw [h0, mul_zero])
  have hp₀ : dec a x₀ ≠ 0 := by
    intro h0
    have hle := hB x₀
    rw [h0, mul_zero] at hle
    exact mul_ne_zero hL hq₀ (le_antisymm hle zero_le)
  have hA₀ : ofLogTens a x₀ ≠ 0 := by
    rw [← dec_mul_Z a x₀]
    exact mul_ne_zero hp₀ (by rw [hZR]; exact hZRne)
  -- Z(k x₀) = M and Z(k x₀) = m
  have hw_M : Z (k x₀) = M := by
    have h' : ofLogTens a x₀ * Z (k x₀) = ofLogTens a x₀ * M := by
      calc ofLogTens a x₀ * Z (k x₀) = M * ofLogTens a x₀ := J1 x₀ hx₀s
        _ = ofLogTens a x₀ * M := by ring
    exact mul_left_cancel₀ hA₀ h'
  have hw_m : Z (k x₀) = m := by
    have h' : ofLogTens a x₀ * dec (k x₀) y * m
        = ofLogTens a x₀ * dec (k x₀) y * Z (k x₀) := by
      calc ofLogTens a x₀ * dec (k x₀) y * m
          = m * (ofLogTens a x₀ * dec (k x₀) y) := by ring
        _ = ofLogTens a x₀ * (dec (k x₀) y * Z (k x₀)) := J3 x₀ hx₀s
        _ = ofLogTens a x₀ * dec (k x₀) y * Z (k x₀) := by ring
    exact (mul_left_cancel₀ (mul_ne_zero hA₀ hg₀) h').symm
  have hat : L * q x₀ = U * dec a x₀ :=
    mul_right_cancel₀ (mul_ne_zero hg₀ hZRne) (J2 x₀ hx₀s)
  exact ⟨hw_M.symm.trans hw_m, x₀, hq₀, hat⟩

end BindLayer

/-! ### The chain sandwich -/

/-- Blueprint `thm:chain-bound-sandwich` (The chain sandwich): the
division-free multiplicative sandwich, by structural induction on the
chain: under the per-bind mass bounds (`HasMassBounds`), at every
outcome `y`, `Π m_i · dec(Φ_Tmon)(y) ≤ Π M_i · Φ_Dmon(y)` and
`Π m_i · Φ_Dmon(y) ≤ Π M_i · dec(Φ_Tmon)(y)`. No positivity
hypotheses: degenerate cases collapse under the `0⁻¹ = 0` convention.
Promoted from an unmarked internal companion of `chain_bound` to its
own cited principal at C3-E12's CB-RESTRUCT (USER DECREE 2026-08-10);
`chain_bound` (the log form below) now `\uses` this theorem.

Proof steps are named after the mathematics, and `content.tex`'s
`thm:chain-bound-sandwich` proof cites those names, together with the
induction's own case labels, in its `% lean-step:` tags (FORMALIZE.md's
step-tag convention): `empty_bounds` for the base case, `tmon_reading` /
`dmon_reading` / `fiber_sum_carries` for the pure-map step,
`tmon_reading` / `dmon_reading` and `sandwich_mul_right` for the unit and
strength steps, and `bind_layer_sandwich` for the bind step. -/
theorem chain_bound_sandwich :
    ∀ {W : Type} (c : PulloutChain W) (bs : List (ℝ≥0 × ℝ≥0)),
      c.HasMassBounds bs → ∀ y : W,
        lbProd bs * dec c.toTmon y ≤ ubProd bs * c.toDmon y ∧
          lbProd bs * c.toDmon y ≤ ubProd bs * dec c.toTmon y := by
  intro W c
  induction c with
  | base a =>
      intro bs hbs y
      have empty_bounds : bs = [] := hbs
      subst empty_bounds
      simp only [lbProd_nil, ubProd_nil, one_mul]
      exact ⟨le_rfl, le_rfl⟩
  | @pureMap B C h rest ih =>
      intro bs hbs y
      classical
      have bounds_of_rest : rest.HasMassBounds bs := hbs
      have tmon_reading : dec (PulloutChain.pureMap h rest).toTmon
          = Finsupp.mapDomain h (dec rest.toTmon) := (pure_maps h rest.toTmon).2
      have dmon_reading : (PulloutChain.pureMap h rest).toDmon
          = Finsupp.mapDomain h rest.toDmon := rfl
      rw [tmon_reading, dmon_reading,
        mapDomain_apply_sum h (dec rest.toTmon)
          (s := (dec rest.toTmon).support ∪ rest.toDmon.support)
          Finset.subset_union_left y,
        mapDomain_apply_sum h rest.toDmon
          (s := (dec rest.toTmon).support ∪ rest.toDmon.support)
          Finset.subset_union_right y]
      have fiber_sum_carries : ∀ (p q : Tens B) (Lb Ub : ℝ≥0),
          (∀ x, Lb * p x ≤ Ub * q x) →
          Lb * ∑ x ∈ (dec rest.toTmon).support ∪ rest.toDmon.support,
              (if h x = y then p x else 0)
            ≤ Ub * ∑ x ∈ (dec rest.toTmon).support ∪ rest.toDmon.support,
              (if h x = y then q x else 0) := by
        intro p q Lb Ub hpq
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hxy : h x = y
        · rw [if_pos hxy, if_pos hxy]
          exact hpq x
        · rw [if_neg hxy, if_neg hxy, mul_zero, mul_zero]
      exact ⟨fiber_sum_carries _ _ _ _ fun x => (ih bs bounds_of_rest x).1,
        fiber_sum_carries _ _ _ _ fun x => (ih bs bounds_of_rest x).2⟩
  | unitIns c' rest ih =>
      intro bs hbs y
      obtain ⟨b₁, c₂⟩ := y
      have bounds_of_rest : rest.HasMassBounds bs := hbs
      have tmon_reading : dec (PulloutChain.unitIns c' rest).toTmon
          = dstL (dec rest.toTmon) (ret c') := by
        have h := dec_dstL rest.toTmon (ret c' : LogTens _)
        rw [dec_ret] at h
        exact h
      have dmon_reading : (PulloutChain.unitIns c' rest).toDmon
          = dstL rest.toDmon (ret c') := rfl
      rw [tmon_reading, dmon_reading, dstL_apply, dstL_apply]
      exact ⟨sandwich_mul_right (ih bs bounds_of_rest b₁).1,
        sandwich_mul_right (ih bs bounds_of_rest b₁).2⟩
  | strengthStep leaf rest ih =>
      intro bs hbs y
      obtain ⟨b₁, x₂⟩ := y
      have bounds_of_rest : rest.HasMassBounds bs := hbs
      have tmon_reading : dec (PulloutChain.strengthStep leaf rest).toTmon
          = dstL (dec rest.toTmon) (dec leaf) := dec_dstL rest.toTmon leaf
      have dmon_reading : (PulloutChain.strengthStep leaf rest).toDmon
          = dstL rest.toDmon (dec leaf) := rfl
      rw [tmon_reading, dmon_reading, dstL_apply, dstL_apply]
      exact ⟨sandwich_mul_right (ih bs bounds_of_rest b₁).1,
        sandwich_mul_right (ih bs bounds_of_rest b₁).2⟩
  | bindStep k rest ih =>
      intro bs hbs y
      cases bs with
      | nil => exact hbs.elim
      | cons b bs' =>
          obtain ⟨hk, bounds_of_rest⟩ := hbs
          rw [lbProd_cons, ubProd_cons]
          exact bind_layer_sandwich rest.toTmon rest.toDmon k hk
            (fun x => (ih bs' bounds_of_rest x).1) (fun x => (ih bs' bounds_of_rest x).2) y

/-! ### The equality converse -/

/-- Upper attainment forces every pair to coincide: if `Π m_i ·
dec(Φ_Tmon)(y) = Π M_i · Φ_Dmon(y)` at an outcome with `Φ_Dmon(y) > 0`,
then every `M_i = m_i` (induction on the chain, handing the attained
equality to a witness index at each bind via `bind_layer_eq_upper`). -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem chain_bound_eq_upper :
    ∀ {W : Type} (c : PulloutChain W) (bs : List (ℝ≥0 × ℝ≥0)),
      c.HasMassBounds bs → (∀ b ∈ bs, 0 < b.1 ∧ b.1 ≤ b.2) → ∀ y : W,
        0 < c.toDmon y →
        lbProd bs * dec c.toTmon y = ubProd bs * c.toDmon y →
        ∀ b ∈ bs, b.2 = b.1 := by
  intro W c
  induction c with
  | base a =>
      intro bs hbs _ y _ _ b hb
      have hnil : bs = [] := hbs
      subst hnil
      exact absurd hb (List.not_mem_nil)
  | pureMap h rest ih =>
      intro bs hbs hpos y hD heq
      classical
      have hbs' : rest.HasMassBounds bs := hbs
      have hTm : dec (PulloutChain.pureMap h rest).toTmon
          = Finsupp.mapDomain h (dec rest.toTmon) := (pure_maps h rest.toTmon).2
      have hDm : (PulloutChain.pureMap h rest).toDmon
          = Finsupp.mapDomain h rest.toDmon := rfl
      set s : Finset _ := (dec rest.toTmon).support ∪ rest.toDmon.support with hs_def
      rw [hDm, mapDomain_apply_sum h rest.toDmon (s := s)
        Finset.subset_union_right y] at hD
      rw [hTm, hDm,
        mapDomain_apply_sum h (dec rest.toTmon) (s := s)
          Finset.subset_union_left y,
        mapDomain_apply_sum h rest.toDmon (s := s)
          Finset.subset_union_right y,
        Finset.mul_sum, Finset.mul_sum] at heq
      have hle : ∀ x ∈ s,
          lbProd bs * (if h x = y then dec rest.toTmon x else 0)
            ≤ ubProd bs * (if h x = y then rest.toDmon x else 0) := by
        intro x _
        by_cases hxy : h x = y
        · rw [if_pos hxy, if_pos hxy]
          exact (chain_bound_sandwich rest bs hbs' x).1
        · rw [if_neg hxy, if_neg hxy, mul_zero, mul_zero]
      have hterm := (Finset.sum_eq_sum_iff_of_le hle).mp heq
      obtain ⟨x₀, hx₀s, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hD.ne'
      have hx₀y : h x₀ = y := by
        by_contra hne
        exact hx₀ (if_neg hne)
      have hq₀ : rest.toDmon x₀ ≠ 0 := by
        intro h0
        exact hx₀ (by rw [if_pos hx₀y, h0])
      have hat := hterm x₀ hx₀s
      rw [if_pos hx₀y, if_pos hx₀y] at hat
      exact ih bs hbs' hpos x₀ (pos_iff_ne_zero.mpr hq₀) hat
  | unitIns c' rest ih =>
      intro bs hbs hpos y hD heq
      obtain ⟨b₁, c₂⟩ := y
      have hbs' : rest.HasMassBounds bs := hbs
      have hTm : dec (PulloutChain.unitIns c' rest).toTmon
          = dstL (dec rest.toTmon) (ret c') := by
        have h := dec_dstL rest.toTmon (ret c' : LogTens _)
        rw [dec_ret] at h
        exact h
      have hDm : (PulloutChain.unitIns c' rest).toDmon
          = dstL rest.toDmon (ret c') := rfl
      rw [hDm, dstL_apply] at hD
      rw [hTm, hDm, dstL_apply, dstL_apply] at heq
      obtain ⟨hq₀, hr₀⟩ := mul_ne_zero_iff.mp hD.ne'
      exact ih bs hbs' hpos b₁ (pos_iff_ne_zero.mpr hq₀)
        (eq_of_mul_mul_right_cancel hr₀ heq)
  | strengthStep leaf rest ih =>
      intro bs hbs hpos y hD heq
      obtain ⟨b₁, x₂⟩ := y
      have hbs' : rest.HasMassBounds bs := hbs
      have hTm : dec (PulloutChain.strengthStep leaf rest).toTmon
          = dstL (dec rest.toTmon) (dec leaf) := dec_dstL rest.toTmon leaf
      have hDm : (PulloutChain.strengthStep leaf rest).toDmon
          = dstL rest.toDmon (dec leaf) := rfl
      rw [hDm, dstL_apply] at hD
      rw [hTm, hDm, dstL_apply, dstL_apply] at heq
      obtain ⟨hq₀, hr₀⟩ := mul_ne_zero_iff.mp hD.ne'
      exact ih bs hbs' hpos b₁ (pos_iff_ne_zero.mpr hq₀)
        (eq_of_mul_mul_right_cancel hr₀ heq)
  | bindStep k rest ih =>
      intro bs hbs hpos y hD heq
      cases bs with
      | nil => exact hbs.elim
      | cons b bs' =>
          obtain ⟨hk, hbs'⟩ := hbs
          have hhead := hpos b (by simp)
          have htail : ∀ b' ∈ bs', 0 < b'.1 ∧ b'.1 ≤ b'.2 :=
            fun b' hb' => hpos b' (List.mem_cons_of_mem _ hb')
          have hL : lbProd bs' ≠ 0 :=
            (lbProd_pos fun b' hb' => (htail b' hb').1).ne'
          have hU : ubProd bs' ≠ 0 :=
            (ubProd_pos fun b' hb' =>
              lt_of_lt_of_le (htail b' hb').1 (htail b' hb').2).ne'
          rw [lbProd_cons, ubProd_cons] at heq
          obtain ⟨hMm, x₀, hq₀, hat⟩ :=
            bind_layer_eq_upper rest.toTmon rest.toDmon k hhead.1.ne' hhead.2
              hL hU hk
              (fun x => (chain_bound_sandwich rest bs' hbs' x).1)
              (fun x => (chain_bound_sandwich rest bs' hbs' x).2)
              y hD heq
          intro b'' hb''
          rcases List.mem_cons.mp hb'' with hb_eq | hb_tail
          · rw [hb_eq]; exact hMm
          · exact ih bs' hbs' htail x₀ (pos_iff_ne_zero.mpr hq₀) hat b'' hb_tail

/-- Lower attainment forces every pair to coincide, the mirror of
`chain_bound_eq_upper` via `bind_layer_eq_lower`. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem chain_bound_eq_lower :
    ∀ {W : Type} (c : PulloutChain W) (bs : List (ℝ≥0 × ℝ≥0)),
      c.HasMassBounds bs → (∀ b ∈ bs, 0 < b.1 ∧ b.1 ≤ b.2) → ∀ y : W,
        0 < c.toDmon y →
        lbProd bs * c.toDmon y = ubProd bs * dec c.toTmon y →
        ∀ b ∈ bs, b.2 = b.1 := by
  intro W c
  induction c with
  | base a =>
      intro bs hbs _ y _ _ b hb
      have hnil : bs = [] := hbs
      subst hnil
      exact absurd hb (List.not_mem_nil)
  | pureMap h rest ih =>
      intro bs hbs hpos y hD heq
      classical
      have hbs' : rest.HasMassBounds bs := hbs
      have hTm : dec (PulloutChain.pureMap h rest).toTmon
          = Finsupp.mapDomain h (dec rest.toTmon) := (pure_maps h rest.toTmon).2
      have hDm : (PulloutChain.pureMap h rest).toDmon
          = Finsupp.mapDomain h rest.toDmon := rfl
      set s : Finset _ := (dec rest.toTmon).support ∪ rest.toDmon.support with hs_def
      rw [hDm, mapDomain_apply_sum h rest.toDmon (s := s)
        Finset.subset_union_right y] at hD
      rw [hTm, hDm,
        mapDomain_apply_sum h (dec rest.toTmon) (s := s)
          Finset.subset_union_left y,
        mapDomain_apply_sum h rest.toDmon (s := s)
          Finset.subset_union_right y,
        Finset.mul_sum, Finset.mul_sum] at heq
      have hle : ∀ x ∈ s,
          lbProd bs * (if h x = y then rest.toDmon x else 0)
            ≤ ubProd bs * (if h x = y then dec rest.toTmon x else 0) := by
        intro x _
        by_cases hxy : h x = y
        · rw [if_pos hxy, if_pos hxy]
          exact (chain_bound_sandwich rest bs hbs' x).2
        · rw [if_neg hxy, if_neg hxy, mul_zero, mul_zero]
      have hterm := (Finset.sum_eq_sum_iff_of_le hle).mp heq
      obtain ⟨x₀, hx₀s, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hD.ne'
      have hx₀y : h x₀ = y := by
        by_contra hne
        exact hx₀ (if_neg hne)
      have hq₀ : rest.toDmon x₀ ≠ 0 := by
        intro h0
        exact hx₀ (by rw [if_pos hx₀y, h0])
      have hat := hterm x₀ hx₀s
      rw [if_pos hx₀y, if_pos hx₀y] at hat
      exact ih bs hbs' hpos x₀ (pos_iff_ne_zero.mpr hq₀) hat
  | unitIns c' rest ih =>
      intro bs hbs hpos y hD heq
      obtain ⟨b₁, c₂⟩ := y
      have hbs' : rest.HasMassBounds bs := hbs
      have hTm : dec (PulloutChain.unitIns c' rest).toTmon
          = dstL (dec rest.toTmon) (ret c') := by
        have h := dec_dstL rest.toTmon (ret c' : LogTens _)
        rw [dec_ret] at h
        exact h
      have hDm : (PulloutChain.unitIns c' rest).toDmon
          = dstL rest.toDmon (ret c') := rfl
      rw [hDm, dstL_apply] at hD
      rw [hTm, hDm, dstL_apply, dstL_apply] at heq
      obtain ⟨hq₀, hr₀⟩ := mul_ne_zero_iff.mp hD.ne'
      exact ih bs hbs' hpos b₁ (pos_iff_ne_zero.mpr hq₀)
        (eq_of_mul_mul_right_cancel hr₀ heq)
  | strengthStep leaf rest ih =>
      intro bs hbs hpos y hD heq
      obtain ⟨b₁, x₂⟩ := y
      have hbs' : rest.HasMassBounds bs := hbs
      have hTm : dec (PulloutChain.strengthStep leaf rest).toTmon
          = dstL (dec rest.toTmon) (dec leaf) := dec_dstL rest.toTmon leaf
      have hDm : (PulloutChain.strengthStep leaf rest).toDmon
          = dstL rest.toDmon (dec leaf) := rfl
      rw [hDm, dstL_apply] at hD
      rw [hTm, hDm, dstL_apply, dstL_apply] at heq
      obtain ⟨hq₀, hr₀⟩ := mul_ne_zero_iff.mp hD.ne'
      exact ih bs hbs' hpos b₁ (pos_iff_ne_zero.mpr hq₀)
        (eq_of_mul_mul_right_cancel hr₀ heq)
  | bindStep k rest ih =>
      intro bs hbs hpos y hD heq
      cases bs with
      | nil => exact hbs.elim
      | cons b bs' =>
          obtain ⟨hk, hbs'⟩ := hbs
          have hhead := hpos b (by simp)
          have htail : ∀ b' ∈ bs', 0 < b'.1 ∧ b'.1 ≤ b'.2 :=
            fun b' hb' => hpos b' (List.mem_cons_of_mem _ hb')
          have hL : lbProd bs' ≠ 0 :=
            (lbProd_pos fun b' hb' => (htail b' hb').1).ne'
          have hU : ubProd bs' ≠ 0 :=
            (ubProd_pos fun b' hb' =>
              lt_of_lt_of_le (htail b' hb').1 (htail b' hb').2).ne'
          rw [lbProd_cons, ubProd_cons] at heq
          obtain ⟨hMm, x₀, hq₀, hat⟩ :=
            bind_layer_eq_lower rest.toTmon rest.toDmon k hhead.1.ne' hhead.2
              hL hU hk
              (fun x => (chain_bound_sandwich rest bs' hbs' x).1)
              (fun x => (chain_bound_sandwich rest bs' hbs' x).2)
              y hD heq
          intro b'' hb''
          rcases List.mem_cons.mp hb'' with hb_eq | hb_tail
          · rw [hb_eq]; exact hMm
          · exact ih bs' hbs' htail x₀ (pos_iff_ne_zero.mpr hq₀) hat b'' hb_tail

/-! ### The log bridge and the principal theorem -/

/-- `Σ_i log(M_i/m_i) = log(Π M_i) − log(Π m_i)` for well-formed bounds
(`0 < m_i ≤ M_i`). -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem log_ratio_sum {bs : List (ℝ≥0 × ℝ≥0)}
    (hb : ∀ b ∈ bs, 0 < b.1 ∧ b.1 ≤ b.2) :
    (bs.map fun b => Real.log ((b.2 : ℝ) / (b.1 : ℝ))).sum
      = Real.log (ubProd bs) - Real.log (lbProd bs) := by
  induction bs with
  | nil => simp [lbProd_nil, ubProd_nil]
  | cons b bs ih =>
      have hhead := hb b (by simp)
      have htail : ∀ b' ∈ bs, 0 < b'.1 ∧ b'.1 ≤ b'.2 :=
        fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')
      have hb1 : (b.1 : ℝ) ≠ 0 := by
        exact_mod_cast hhead.1.ne'
      have hb2 : (b.2 : ℝ) ≠ 0 := by
        exact_mod_cast (lt_of_lt_of_le hhead.1 hhead.2).ne'
      have hlb : (lbProd bs : ℝ) ≠ 0 := by
        exact_mod_cast (lbProd_pos fun b' hb' => (htail b' hb').1).ne'
      have hub : (ubProd bs : ℝ) ≠ 0 := by
        exact_mod_cast (ubProd_pos fun b' hb' =>
          lt_of_lt_of_le (htail b' hb').1 (htail b' hb').2).ne'
      simp only [List.map_cons, List.sum_cons]
      rw [ih htail, lbProd_cons, ubProd_cons]
      push_cast
      rw [Real.log_div hb2 hb1, Real.log_mul hb2 hub, Real.log_mul hb1 hlb]
      ring

/-- Coinciding bounds force mass preservation: if `m_i ≤ Z(k_i(x)) ≤ M_i`
for all `x` with every `M_i = m_i`, every bind of the chain is mass
preserving. -/
-- (A1 bijection-law companion of `chain_bound`, content.tex
-- thm:chain-bound)
@[blueprint_internal]
theorem allMassPreserving_of_bounds_eq :
    ∀ {W : Type} (c : PulloutChain W) (bs : List (ℝ≥0 × ℝ≥0)),
      c.HasMassBounds bs → (∀ b ∈ bs, b.2 = b.1) → c.AllMassPreserving := by
  intro W c
  induction c with
  | base a => intro bs _ _; trivial
  | pureMap h rest ih => intro bs hbs hall; exact ih bs hbs hall
  | unitIns c' rest ih => intro bs hbs hall; exact ih bs hbs hall
  | strengthStep leaf rest ih => intro bs hbs hall; exact ih bs hbs hall
  | bindStep k rest ih =>
      intro bs hbs hall
      cases bs with
      | nil => exact hbs.elim
      | cons b bs' =>
          obtain ⟨hk, hbs'⟩ := hbs
          refine ⟨⟨b.1, fun x => le_antisymm ?_ (hk x).1⟩,
            ih bs' hbs' fun b' hb' => hall b' (List.mem_cons_of_mem _ hb')⟩
          calc Z (k x) ≤ b.2 := (hk x).2
            _ = b.1 := hall b (by simp)

/-- Blueprint `thm:chain-bound` (How wrong can it get): for a pull-out
chain `Φ` (`PulloutChain`, `thm:pullout`) whose binds carry the mass
bounds `m_i ≤ Z(k_i(x)) ≤ M_i` for all `x` (`HasMassBounds`), with the
bounds well formed (`0 < m_i ≤ M_i`) and the `Dmon`-side truth value
positive at the outcome `y`, the two log-truth values `t_Tmon =
dec(Φ_Tmon)(y)` and `t_Dmon = Φ_Dmon(y)` satisfy

  `|log t_Tmon − log t_Dmon| ≤ Σ_i log(M_i/m_i)`,

with equality (the identity, both sides `0`) exactly when every
`M_i = m_i`. Proof: the division-free sandwich `chain_bound_sandwich`
plus the log bridge `log_ratio_sum` give the bound (positivity of
`t_Tmon` is derived from the sandwich, not assumed); if every `M_i = m_i`
the binds are all mass preserving (`allMassPreserving_of_bounds_eq`) and
`thm:pullout` makes both sides `0`; conversely an attained bound forces,
at a witness index per bind, `Z(k_i) = m_i` and `Z(k_i) = M_i`
simultaneously (`chain_bound_eq_upper`/`chain_bound_eq_lower`).

Proof steps are named after the mathematics, and `content.tex`'s
`thm:chain-bound` proof cites those names in its `% lean-step:` tags
(FORMALIZE.md's step-tag convention): `sandwich`, `tmon_pos`,
`log_gap_upper`, `log_gap_lower`, `abs_log_gap_bound` for the bound;
`sandwich_attained` and `bound_vanishes` for the two directions of the
equality case. -/
theorem chain_bound {W : Type} (c : PulloutChain W) (bs : List (ℝ≥0 × ℝ≥0))
    (hbs : c.HasMassBounds bs) (hb : ∀ b ∈ bs, 0 < b.1 ∧ b.1 ≤ b.2)
    (y : W) (hD : 0 < c.toDmon y) :
    |Real.log (dec c.toTmon y) - Real.log (c.toDmon y)|
        ≤ (bs.map fun b => Real.log ((b.2 : ℝ) / (b.1 : ℝ))).sum ∧
      (|Real.log (dec c.toTmon y) - Real.log (c.toDmon y)|
          = (bs.map fun b => Real.log ((b.2 : ℝ) / (b.1 : ℝ))).sum
        ↔ ∀ b ∈ bs, b.2 = b.1) := by
  classical
  have hb1 : ∀ b ∈ bs, 0 < b.1 := fun b h => (hb b h).1
  have hb2 : ∀ b ∈ bs, 0 < b.2 := fun b h => lt_of_lt_of_le (hb b h).1 (hb b h).2
  have hL : 0 < lbProd bs := lbProd_pos hb1
  have hU : 0 < ubProd bs := ubProd_pos hb2
  have sandwich := chain_bound_sandwich c bs hbs y
  have tmon_pos : 0 < dec c.toTmon y := by
    rw [pos_iff_ne_zero]
    intro h0
    have hle := sandwich.2
    rw [h0, mul_zero] at hle
    rcases mul_eq_zero.mp (le_antisymm hle zero_le) with h | h
    · exact hL.ne' h
    · exact hD.ne' h
  have hTr : (0 : ℝ) < dec c.toTmon y := by exact_mod_cast tmon_pos
  have hDr : (0 : ℝ) < c.toDmon y := by exact_mod_cast hD
  have hLr : (0 : ℝ) < lbProd bs := by exact_mod_cast hL
  have hUr : (0 : ℝ) < ubProd bs := by exact_mod_cast hU
  have log_ratio_sum_eq := log_ratio_sum hb
  have log_gap_upper : Real.log (dec c.toTmon y) - Real.log (c.toDmon y)
      ≤ Real.log (ubProd bs) - Real.log (lbProd bs) := by
    have h1 : (lbProd bs : ℝ) * dec c.toTmon y
        ≤ (ubProd bs : ℝ) * c.toDmon y := by exact_mod_cast sandwich.1
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hLr.ne' hTr.ne', Real.log_mul hUr.ne' hDr.ne'] at h2
    linarith
  have log_gap_lower : Real.log (c.toDmon y) - Real.log (dec c.toTmon y)
      ≤ Real.log (ubProd bs) - Real.log (lbProd bs) := by
    have h1 : (lbProd bs : ℝ) * c.toDmon y
        ≤ (ubProd bs : ℝ) * dec c.toTmon y := by exact_mod_cast sandwich.2
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hLr.ne' hDr.ne', Real.log_mul hUr.ne' hTr.ne'] at h2
    linarith
  have abs_log_gap_bound : |Real.log (dec c.toTmon y) - Real.log (c.toDmon y)|
      ≤ (bs.map fun b => Real.log ((b.2 : ℝ) / (b.1 : ℝ))).sum := by
    rw [log_ratio_sum_eq]
    exact abs_le.mpr ⟨by linarith, log_gap_upper⟩
  refine ⟨abs_log_gap_bound, ?_, ?_⟩
  · -- attained bound forces every pair to coincide
    intro heq
    rw [log_ratio_sum_eq] at heq
    have hS0 : 0 ≤ Real.log (ubProd bs) - Real.log (lbProd bs) :=
      heq ▸ abs_nonneg _
    rcases (abs_eq hS0).mp heq with hcase | hcase
    · have log_attained : Real.log ((lbProd bs : ℝ) * dec c.toTmon y)
          = Real.log ((ubProd bs : ℝ) * c.toDmon y) := by
        rw [Real.log_mul hLr.ne' hTr.ne', Real.log_mul hUr.ne' hDr.ne']
        linarith
      have hexp := congrArg Real.exp log_attained
      rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at hexp
      have sandwich_attained : lbProd bs * dec c.toTmon y = ubProd bs * c.toDmon y := by
        exact_mod_cast hexp
      exact chain_bound_eq_upper c bs hbs hb y hD sandwich_attained
    · have log_attained : Real.log ((lbProd bs : ℝ) * c.toDmon y)
          = Real.log ((ubProd bs : ℝ) * dec c.toTmon y) := by
        rw [Real.log_mul hLr.ne' hDr.ne', Real.log_mul hUr.ne' hTr.ne']
        linarith
      have hexp := congrArg Real.exp log_attained
      rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at hexp
      have sandwich_attained : lbProd bs * c.toDmon y = ubProd bs * dec c.toTmon y := by
        exact_mod_cast hexp
      exact chain_bound_eq_lower c bs hbs hb y hD sandwich_attained
  · -- coinciding pairs make both sides zero via `thm:pullout`
    intro hall
    have exact_agreement := pullout c (allMassPreserving_of_bounds_eq c bs hbs hall)
    have bound_vanishes : (bs.map fun b => Real.log ((b.2 : ℝ) / (b.1 : ℝ))).sum = 0 := by
      apply List.sum_eq_zero
      intro v hv
      rcases List.mem_map.mp hv with ⟨b, hbmem, rfl⟩
      have h1 : (b.1 : ℝ) ≠ 0 := by exact_mod_cast (hb1 b hbmem).ne'
      rw [hall b hbmem, div_self h1, Real.log_one]
    rw [bound_vanishes, exact_agreement]
    simp

end NeSyCat
