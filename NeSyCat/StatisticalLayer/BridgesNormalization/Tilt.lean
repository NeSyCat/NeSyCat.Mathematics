/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.StatisticalLayer.BridgesNormalization.DecEncMass

/-!
# Tilt, mass preservation, and the pull-out theorem

Blueprint items `lem:tilt`, `def:mass-preserving`, `lem:mass-preserving-closure`,
and `thm:pullout` (`blueprint/src/content.tex`, §"Bridges and normalization",
`[NeSy26, App. B draft/T3]`). Builds on
`NeSyCat/StatisticalLayer/BridgesNormalization/DecEncMass.lean`'s `dec`/`enc`/`Z`
suite (`def:dec-enc-mass`) and its four companion lemmas
(`pure_maps`/`tensor`/`units`/`strengths`).

`tilt` is introduced inline inside `lem:tilt`'s own displayed equation in
`content.tex` (no separate `definition` env, per the definition-atomicity
law): realized here as `reweight`/`tiltMass`/`tilt`, a companion cluster
tagged `@[blueprint_internal]`, with the lemma's own principal name
(`tilt_bind`) the one cited declaration.

`tilt_bind'` (internal) proves the identity **without** `lem:tilt`'s stated
positivity hypothesis: the ambient `0⁻¹ = 0` convention already shared by
`dec`/`tilt` makes a zero-mass continuation `k(x)` contribute exactly `0` on
both sides, so `tilt_bind'` is a genuinely more general fact; `tilt_bind`
(the cited principal) keeps the blueprint's own displayed hypothesis in its
signature for exact statement fidelity, then discharges it as a free,
unused corollary of `tilt_bind'` (disclosed, not a weakening).

`def:mass-preserving`'s arrow class (`MassPreserving`) reads `∃ c, ∀ x, Z(k
x) = c`, matching "the function `x ↦ Z(k(x))` is constant on `X`" directly.

`thm:pullout`'s point-free chain `Φ = L ⨟ B_1 ⨟ ⋯ ⨟ B_r` is realized as an
inductive family `PulloutChain W`, one constructor per factor kind
`content.tex` lists: a base leaf tensor (`base`, standing for `L`), a
lifted pure map `\Tmon(h)` (`pureMap`, `lem:pure-maps`), a unit insertion
`- \otimes \Ret_\Tmon(c)` (`unitIns`, `lem:tensor` + `lem:units`), a general
leaf/strength insertion `- \otimes a` (`strengthStep`, `lem:tensor`
directly — the two-factor pairing `lem:strengths` (`DecEncMass.lean`) is
itself built from, so `unitIns` is the special case `a = \Ret_\Tmon(c)`),
and a bind `(- \bind k_i)` (`bindStep`). `AllMassPreserving` collects the
mass-preservation hypothesis at every `bindStep` node; `toTmon`/`toDmon`
realize the chain read in `Tmon`/`Dmon` respectively. `pullout` proves
`dec ∘ toTmon = toDmon` by structural induction on the chain, matching the
blueprint's own "induction on `r`".
-/

namespace NeSyCat

open scoped NNReal

variable {X Y Z' : Type*}

/-! ### `lem:tilt` -/

/-- `tilt`'s numerator: reweighting `p` pointwise by `w`, `reweight w p x =
w(x)p(x)` (`reweight_apply` below) — a genuine `Tens X`, since `w(x)p(x) =
0` wherever `p(x) = 0`. -/
-- (A1 bijection-law companion of `tilt_bind`, content.tex lem:tilt: `tilt`
-- is introduced inline inside the lemma's own displayed equation, no
-- separate `definition` env)
@[blueprint_internal]
noncomputable def reweight (w : X → ℝ≥0) (p : Tens X) : Tens X :=
  Finsupp.onFinset p.support (fun x => w x * p x)
    (fun x hx => Finsupp.mem_support_iff.mpr fun hp => hx (by rw [hp, mul_zero]))

-- (A1 bijection-law companion of `tilt_bind`, content.tex lem:tilt)
@[blueprint_internal]
theorem reweight_apply (w : X → ℝ≥0) (p : Tens X) (x : X) :
    reweight w p x = w x * p x :=
  Finsupp.onFinset_apply

/-- `(reweight w p).sum (fun x c => c * g x)` unfolds to a `p.sum`, via the
support inclusion `(reweight w p).support ⊆ p.support` (`reweight_apply`
vanishing off `p`'s support). Reused for both `tilt`'s own denominator and
`tilt_bind'`'s numerator manipulation. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem sum_reweight (w : X → ℝ≥0) (p : Tens X) (g : X → ℝ≥0) :
    (reweight w p).sum (fun x c => c * g x) = p.sum (fun x c => w x * c * g x) := by
  have hsub : (reweight w p).support ⊆ p.support := by
    intro x hx
    by_contra hxp
    apply Finsupp.mem_support_iff.mp hx
    rw [reweight_apply, Finsupp.notMem_support_iff.mp hxp, mul_zero]
  rw [Finsupp.sum_of_support_subset (reweight w p) hsub (fun x c => c * g x)
    (fun x _ => zero_mul _)]
  simp_rw [reweight_apply]
  rfl

/-- `tilt`'s denominator: the reweighted total mass `Σ_x w(x)p(x)`. -/
-- (A1 bijection-law companion of `tilt_bind`, content.tex lem:tilt)
@[blueprint_internal]
noncomputable def tiltMass (w : X → ℝ≥0) (p : Tens X) : ℝ≥0 := p.sum (fun x c => w x * c)

/-- Blueprint `lem:tilt` (tilt reweighting operator): `tilt w p x := w(x)p(x)
/ Σ_x' w(x')p(x')` (`tilt_apply` below unfolds this pointwise). -/
-- (A1 bijection-law companion of `tilt_bind`, content.tex lem:tilt)
@[blueprint_internal]
noncomputable def tilt (w : X → ℝ≥0) (p : Tens X) : Tens X := (tiltMass w p)⁻¹ • reweight w p

-- (A1 bijection-law companion of `tilt_bind`, content.tex lem:tilt)
@[blueprint_internal]
theorem tilt_apply (w : X → ℝ≥0) (p : Tens X) (x : X) :
    tilt w p x = w x * p x / tiltMass w p := by
  unfold tilt
  rw [Finsupp.smul_apply, smul_eq_mul, reweight_apply, div_eq_mul_inv, mul_comm]

/-- `ofLogTens` commutes with `bind`: the mass-carrier reading of a
`LogTens`-bind is the `Tens`-bind of the mass-carrier readings, the
inverse-direction twin of `toLogTens_bind` (`lem:log-iso`), matching how
`ofLogTens_dstL` (`DecEncMass.lean`) is built for `dstL`. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem ofLogTens_bind (a : LogTens X) (k : X → LogTens Y) :
    ofLogTens (bind a k) = bind (ofLogTens a) (fun x => ofLogTens (k x)) := by
  have h : toLogTens (bind (ofLogTens a) (fun x => ofLogTens (k x))) = bind a k := by
    rw [toLogTens_bind, toLogTens_ofLogTens]
    congr 1
    funext x
    rw [toLogTens_ofLogTens]
  rw [← h, ofLogTens_toLogTens]

/-- Total mass of a `LogTens`-bind factors through `k`'s per-index total
mass: `Z(bind a k) = Σ_x ofLogTens(a)(x) * Z(k x)` (`ofLogTens_bind` plus
`bind_sum_eq`, the same Fubini computation `dstL_sum_mul` uses for `⊗`). -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem Z_bind (a : LogTens X) (k : X → LogTens Y) :
    Z (bind a k) = (ofLogTens a).sum (fun x w => w * Z (k x)) := by
  unfold Z
  rw [ofLogTens_bind, bind_sum_eq]

/-- If `k`'s total mass is the same constant `c` at every index, `Z(bind a
k) = Z(a) * c` — the pointwise mass identity behind
`lem:mass-preserving-closure`'s composition clause. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem Z_bind_of_forall_const {k : X → LogTens Y} {c : ℝ≥0} (hc : ∀ x, Z (k x) = c)
    (a : LogTens X) : Z (bind a k) = Z a * c := by
  rw [Z_bind]
  have heq : (ofLogTens a).sum (fun x w => w * Z (k x)) = (ofLogTens a).sum (fun x w => w * c) :=
    Finsupp.sum_congr fun x _ => by rw [hc x]
  rw [heq, ← Finsupp.sum_mul]
  rfl

/-- A zero-mass log-weight vector has every mass-carrier coordinate `0`: the
Fubini sum defining `Z` is a sum of nonnegative terms, so `Z(a) = 0` forces
each term (`ofLogTens(a)(x)`) to vanish. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem ofLogTens_eq_zero_of_Z_eq_zero {a : LogTens X} (hZ : Z a = 0) (x : X) :
    ofLogTens a x = 0 := by
  by_contra hx
  have hxs : x ∈ (ofLogTens a).support := Finsupp.mem_support_iff.mpr hx
  have hZ' : ∑ i ∈ (ofLogTens a).support, (ofLogTens a) i = 0 := hZ
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (ofLogTens a).support) => zero_le (a := (ofLogTens a) i))).mp hZ'
  exact hx (hall x hxs)

/-- `dec(a)(x) * Z(a) = ofLogTens(a)(x)`, unconditionally: the `0⁻¹ = 0`
convention makes both sides `0` together when `Z(a) = 0`
(`ofLogTens_eq_zero_of_Z_eq_zero`), and division cancels the usual way
otherwise. The pointwise identity `tilt_bind'` below is built from. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem dec_mul_Z (a : LogTens X) (x : X) : dec a x * Z a = ofLogTens a x := by
  rw [dec_apply]
  by_cases hZ : Z a = 0
  · rw [hZ, div_zero, zero_mul, ofLogTens_eq_zero_of_Z_eq_zero hZ]
  · rw [div_mul_cancel₀ _ hZ]

/-! ### `def:mass-preserving` -/

/-- Blueprint `def:mass-preserving`: an arrow `k : X → \Tmon Y` is mass
preserving when `x \mapsto Z(k(x))` is constant on `X`. -/
def MassPreserving (k : X → LogTens Y) : Prop := ∃ c : ℝ≥0, ∀ x, Z (k x) = c

/-! ### `lem:tilt`, continued -/

/-- Blueprint `lem:tilt`, proved without the positivity hypothesis: `dec(a
\bind k) = \tilt_{k \seq Z}(\dec(a)) \bind (k \seq \dec)`, for every `a`,
`k` unconditionally. See the module doc comment for why the blueprint's
positivity side condition is not needed by this proof route. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem tilt_bind' (a : LogTens X) (k : X → LogTens Y) :
    dec (bind a k) = bind (tilt (fun x => Z (k x)) (dec a)) (fun x => dec (k x)) := by
  by_cases hZa : Z a = 0
  · have ha0 : ofLogTens a = 0 := by
      apply Finsupp.ext; intro x; exact ofLogTens_eq_zero_of_Z_eq_zero hZa x
    have hda0 : dec a = 0 := by
      unfold dec; rw [ha0, smul_zero]
    have hZbind : Z (bind a k) = 0 := by rw [Z_bind, ha0]; exact Finsupp.sum_zero_index
    have hdecbind : dec (bind a k) = 0 := by unfold dec; rw [hZbind, inv_zero, zero_smul]
    have htilt0 : tilt (fun x => Z (k x)) (dec a) = 0 := by
      rw [hda0]
      have hrw0 : reweight (fun x => Z (k x)) (0 : Tens X) = 0 := by
        apply Finsupp.ext
        intro x
        rw [reweight_apply, Finsupp.zero_apply, mul_zero]
      unfold tilt
      rw [hrw0, smul_zero]
    rw [hdecbind, htilt0]
    unfold bind
    rw [Finsupp.sum_zero_index]
  · apply Finsupp.ext
    intro y
    have hL : dec (bind a k) y
        = (ofLogTens a).sum (fun x c => c * ofLogTens (k x) y) / Z (bind a k) := by
      rw [dec_apply, ofLogTens_bind, bind_apply]
    have hR : bind (tilt (fun x => Z (k x)) (dec a)) (fun x => dec (k x)) y
        = (tilt (fun x => Z (k x)) (dec a)).sum (fun x c => c * dec (k x) y) := bind_apply _ _ y
    rw [hL, hR]
    set Nsum : ℝ≥0 := (ofLogTens a).sum (fun x c => c * ofLogTens (k x) y) with hNsum
    set Dsum : ℝ≥0 := (ofLogTens a).sum (fun x c => c * Z (k x)) with hDsum
    have hZbind : Z (bind a k) = Dsum := by rw [Z_bind]
    have hda : dec a = (Z a)⁻¹ • ofLogTens a := rfl
    have hdecSum : (dec a).sum (fun x c => Z (k x) * c * dec (k x) y) = (Z a)⁻¹ * Nsum := by
      rw [hda, Finsupp.sum_smul_index (fun x => by rw [mul_zero, zero_mul])]
      have hpt : (fun x c => Z (k x) * ((Z a)⁻¹ * c) * dec (k x) y)
          = (fun x c => (Z a)⁻¹ * (c * ofLogTens (k x) y)) := by
        funext x c
        rw [show Z (k x) * ((Z a)⁻¹ * c) * dec (k x) y
            = (Z a)⁻¹ * c * (dec (k x) y * Z (k x)) by ring, dec_mul_Z]
        ring
      rw [hpt, ← Finsupp.mul_sum, hNsum]
    have htiltMass : tiltMass (fun x => Z (k x)) (dec a) = (Z a)⁻¹ * Dsum := by
      unfold tiltMass
      rw [hda, Finsupp.sum_smul_index (fun x => by rw [mul_zero])]
      have hpt : (fun x c => Z (k x) * ((Z a)⁻¹ * c)) = (fun x c => (Z a)⁻¹ * (c * Z (k x))) := by
        funext x c; ring
      rw [hpt, ← Finsupp.mul_sum, hDsum]
    rw [hZbind]
    change Nsum / Dsum = (tilt (fun x => Z (k x)) (dec a)).sum (fun x c => c * dec (k x) y)
    unfold tilt
    rw [Finsupp.sum_smul_index (fun x => by rw [zero_mul])]
    have hstep1 : (reweight (fun x => Z (k x)) (dec a)).sum
        (fun x c => (tiltMass (fun x => Z (k x)) (dec a))⁻¹ * c * dec (k x) y)
        = (tiltMass (fun x => Z (k x)) (dec a))⁻¹ *
            (dec a).sum (fun x c => Z (k x) * c * dec (k x) y) := by
      have hre : (fun x c => (tiltMass (fun x => Z (k x)) (dec a))⁻¹ * c * dec (k x) y)
          = (fun x c => (tiltMass (fun x => Z (k x)) (dec a))⁻¹ * (c * dec (k x) y)) := by
        funext x c; ring
      rw [hre, ← Finsupp.mul_sum, sum_reweight]
    rw [hstep1, hdecSum, htiltMass, mul_inv, inv_inv, div_eq_mul_inv]
    rw [show (Z a) * Dsum⁻¹ * ((Z a)⁻¹ * Nsum) = (Z a * (Z a)⁻¹) * (Nsum * Dsum⁻¹) by ring,
      mul_inv_cancel₀ hZa, one_mul]

/-- `bind` against the everywhere-zero continuation is `0`: every term of
the defining `Finsupp.sum` scales `0` by something. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem bind_zero_cont {X' Y' : Type*} (p : Tens X') :
    bind p (fun _ : X' => (0 : Tens Y')) = 0 := by
  unfold bind
  simp

/-- `(dec a).sum (fun _ w => w) = 1` whenever `Z(a) ≠ 0`: `dec(a)`'s own
total mass is exactly `Z(a)⁻¹ * Z(a) = 1`, the fact making `tilt` at a
positive constant weight act as the identity on `dec(a)`. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem dec_total_mass_eq_one {a : LogTens X} (hZ : Z a ≠ 0) :
    (dec a).sum (fun _ w => w) = 1 := by
  unfold dec
  rw [Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]
  change (Z a)⁻¹ * Z a = 1
  exact inv_mul_cancel₀ hZ

/-- `tilt` at a positive constant weight fixes `dec(a)`: both the `Z(a) = 0`
case (`dec a` is already `0`) and the `Z(a) ≠ 0` case
(`dec_total_mass_eq_one` makes the reweighting's own denominator collapse
to the constant weight itself) leave `dec(a)` unchanged. The genuinely new
content behind `thm:pullout`'s bind-factor case: a mass-preserving
continuation's tilt weight is constant, and this is exactly when `tilt` is
the identity. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem tilt_const_dec {c : ℝ≥0} (hc : c ≠ 0) (a : LogTens X) :
    tilt (Function.const X c) (dec a) = dec a := by
  apply Finsupp.ext
  intro x
  rw [tilt_apply]
  simp only [Function.const_apply]
  by_cases hZ : Z a = 0
  · have hda : dec a = 0 := by unfold dec; rw [hZ, inv_zero, zero_smul]
    rw [hda, Finsupp.zero_apply, mul_zero, zero_div]
  · have hmass : tiltMass (Function.const X c) (dec a) = c := by
      unfold tiltMass
      have heq : (dec a).sum (fun x' c' => Function.const X c x' * c')
          = (dec a).sum (fun _ c' => c * c') := Finsupp.sum_congr fun x' _ => rfl
      rw [heq, ← Finsupp.mul_sum, dec_total_mass_eq_one hZ, mul_one]
    rw [hmass, mul_div_cancel_left₀ _ hc]

/-- The bind-factor case of `thm:pullout`: when `k` is mass preserving
(`def:mass-preserving`), `\dec(a \bind k) = \dec(a) \bind (k \seq \dec)`,
the tilt weight of `tilt_bind'` collapsing to the identity
(`tilt_const_dec`) when `k`'s constant mass is positive, and both sides
collapsing to `0` directly (via `bind_zero_cont`) when it is `0`. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem dec_bind_of_massPreserving {a : LogTens X} {k : X → LogTens Y} (hk : MassPreserving k) :
    dec (bind a k) = bind (dec a) (fun x => dec (k x)) := by
  obtain ⟨c, hc⟩ := hk
  rw [tilt_bind' a k]
  by_cases hc0 : c = 0
  · have hcont : (fun x => dec (k x)) = (fun _ : X => (0 : Tens Y)) := by
      funext x
      have hZk : Z (k x) = 0 := by rw [hc x, hc0]
      unfold dec
      rw [hZk, inv_zero, zero_smul]
    rw [hcont, bind_zero_cont, bind_zero_cont]
  · have hw : (fun x => Z (k x)) = Function.const X c := funext hc
    rw [hw, tilt_const_dec hc0 a]

/-- Blueprint `lem:tilt` (Tilt): under the positivity hypothesis
`content.tex` states — `Z(k(x)) > 0` for every `x \in \supp(\dec(a))` —
`\dec(a \bind k) = \tilt_{k \seq Z}(\dec(a)) \bind (k \seq \dec)`. Proved by
`tilt_bind'`, which needs no such hypothesis (see the module doc comment);
the hypothesis is kept in the signature here purely for exact statement
fidelity to the blueprint's own displayed hypothesis. -/
theorem tilt_bind (a : LogTens X) (k : X → LogTens Y)
    (_hpos : ∀ x ∈ (dec a).support, 0 < Z (k x)) :
    dec (bind a k) = bind (tilt (fun x => Z (k x)) (dec a)) (fun x => dec (k x)) :=
  tilt_bind' a k

/-! ### `lem:mass-preserving-closure` -/

/-- Blueprint `lem:mass-preserving-closure` (Mass-preserving arrows are
closed): the class of mass-preserving arrows (`def:mass-preserving`)
contains `h \seq \Ret_\Tmon` for every pure `h` (mass `1`, `Z_ret`), the
units `\Ret_\Tmon` themselves, and every strength factor with a fixed leaf
(mass `Z(\mathrm{leaf})`, `strengths`); it is closed under Kleisli
composition (`Z_bind_of_forall_const`), under `\otimes` (`Z_dstL`), and
under precomposition with a pure reindexing arrow (structural wiring —
copying, discarding, permuting — touches no weight at all). -/
theorem mass_preserving_closure :
    (∀ {X Y : Type*} (h : X → Y), MassPreserving (fun x : X => (ret (h x) : LogTens Y))) ∧
      (∀ {X : Type*}, MassPreserving (ret : X → LogTens X)) ∧
      (∀ {B A X' : Type*} (leaf : LogTens X'),
        MassPreserving (fun p : B × A => strength p.1 leaf p.2)) ∧
      (∀ {X Y Z'' : Type*} {k1 : X → LogTens Y} {k2 : Y → LogTens Z''},
        MassPreserving k1 → MassPreserving k2 → MassPreserving (fun x => bind (k1 x) k2)) ∧
      (∀ {X1 Y1 X2 Y2 : Type*} {k1 : X1 → LogTens Y1} {k2 : X2 → LogTens Y2},
        MassPreserving k1 → MassPreserving k2 →
          MassPreserving (fun p : X1 × X2 => dstL (k1 p.1) (k2 p.2))) ∧
      (∀ {X' X Y : Type*} {k : X → LogTens Y} (w : X' → X),
        MassPreserving k → MassPreserving (fun x' => k (w x'))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y h
    exact ⟨1, fun x => Z_ret (h x)⟩
  · intro X
    exact ⟨1, Z_ret⟩
  · intro B A X' leaf
    exact ⟨Z leaf, fun p => (strengths p.1 leaf p.2).1⟩
  · intro X Y Z'' k1 k2 hk1 hk2
    obtain ⟨c1, hc1⟩ := hk1
    obtain ⟨c2, hc2⟩ := hk2
    exact ⟨c1 * c2, fun x => by rw [Z_bind_of_forall_const hc2, hc1 x]⟩
  · intro X1 Y1 X2 Y2 k1 k2 hk1 hk2
    obtain ⟨c1, hc1⟩ := hk1
    obtain ⟨c2, hc2⟩ := hk2
    exact ⟨c1 * c2, fun p => by rw [Z_dstL, hc1 p.1, hc2 p.2]⟩
  · intro X' X Y k w hk
    obtain ⟨c, hc⟩ := hk
    exact ⟨c, fun x' => hc (w x')⟩

/-! ### `thm:pullout` -/

/-- Blueprint `thm:pullout` (point-free chain): the four factor kinds
`content.tex`'s `\Phi = L \seq B_1 \seq \cdots \seq B_r` lists — a base
leaf tensor (`base`, standing for `L`), a lifted pure map `\Tmon(h)`
(`pureMap`, `lem:pure-maps`), a unit insertion `- \otimes \Ret_\Tmon(c)`
(`unitIns`, `lem:tensor` + `lem:units`), a general leaf/strength insertion
`- \otimes a` (`strengthStep`, `lem:tensor` directly, the two-factor
pairing `lem:strengths` (`DecEncMass.lean`) is itself built from — so
`unitIns` is exactly the special case `a = \Ret_\Tmon(c)`), and a bind
`(- \bind k_i)` (`bindStep`) — realized as an inductive family indexed by
the chain's final object. -/
-- (A1 bijection-law companion of `pullout`, content.tex thm:pullout)
@[blueprint_internal]
inductive PulloutChain : Type → Type 1
  | base {W : Type} (a : LogTens W) : PulloutChain W
  | pureMap {B C : Type} (h : B → C) (rest : PulloutChain B) : PulloutChain C
  | unitIns {B C : Type} (c : C) (rest : PulloutChain B) : PulloutChain (B × C)
  | strengthStep {B X' : Type} (leaf : LogTens X') (rest : PulloutChain B) :
      PulloutChain (B × X')
  | bindStep {B C : Type} (k : B → LogTens C) (rest : PulloutChain B) : PulloutChain C

-- Compiler-generated recursor byproducts of the `PulloutChain` inductive
-- family (C2-E4a/A2 completeness census: the auto-generated-suffix filter
-- only matches a name's OWN last component, so `.brecOn.go`/`.brecOn.eq`
-- and `ctorElimType` are not caught automatically), post-hoc tagged the
-- same way `NeSyCat/GrammaticalLayer/Grammar.lean` tags `Tm`/`Fm`'s.
attribute [blueprint_internal] PulloutChain.ctorElimType PulloutChain.brecOn.go
  PulloutChain.brecOn.eq

/-- The chain read in `Tmon`: `L`'s own leaf, `\Tmon(h)` applied via
`Finsupp.mapDomain`, a tensor insertion via `dstL` (`unitIns`/
`strengthStep`), or a genuine bind. -/
-- (A1 bijection-law companion of `pullout`, content.tex thm:pullout)
@[blueprint_internal]
noncomputable def PulloutChain.toTmon : {W : Type} → PulloutChain W → LogTens W
  | _, .base a => a
  | _, .pureMap h rest => Finsupp.mapDomain h rest.toTmon
  | _, .unitIns c rest => dstL rest.toTmon (ret c)
  | _, .strengthStep leaf rest => dstL rest.toTmon leaf
  | _, .bindStep k rest => bind rest.toTmon k

/-- The same chain read in `Dmon`: `L`'s leaf decoded, `\Dmon(h)`, a tensor
insertion of the decoded leaf, or a bind against the decoded continuation
`k \seq \dec` — the blueprint's `B_i^{\Dmon}`. -/
-- (A1 bijection-law companion of `pullout`, content.tex thm:pullout)
@[blueprint_internal]
noncomputable def PulloutChain.toDmon : {W : Type} → PulloutChain W → Tens W
  | _, .base a => dec a
  | _, .pureMap h rest => Finsupp.mapDomain h rest.toDmon
  | _, .unitIns c rest => dstL rest.toDmon (ret c)
  | _, .strengthStep leaf rest => dstL rest.toDmon (dec leaf)
  | _, .bindStep k rest => bind rest.toDmon (fun x => dec (k x))

/-- The chain's own mass-preservation hypothesis: every `bindStep`
continuation is mass preserving (`def:mass-preserving`); every other node
contributes no condition. -/
-- (A1 bijection-law companion of `pullout`, content.tex thm:pullout)
@[blueprint_internal]
def PulloutChain.AllMassPreserving : {W : Type} → PulloutChain W → Prop
  | _, .base _ => True
  | _, .pureMap _ rest => rest.AllMassPreserving
  | _, .unitIns _ rest => rest.AllMassPreserving
  | _, .strengthStep _ rest => rest.AllMassPreserving
  | _, .bindStep k rest => MassPreserving k ∧ rest.AllMassPreserving

/-- Blueprint `thm:pullout` (Pull out): if every bind factor of a point-free
chain `\Phi` (`PulloutChain`) is mass preserving
(`AllMassPreserving`), then `\Phi \seq \dec` agrees with the same chain
read in `\Dmon`, `\dec \circ \mathrm{toTmon} = \mathrm{toDmon}` — proved by
structural induction on the chain (the blueprint's own "induction on `r`"):
each non-bind factor commutes with `\dec` by `lem:pure-maps` / `lem:tensor`
/ `lem:units`, and a bind factor commutes with `\dec` exactly when its
continuation is mass preserving (`dec_bind_of_massPreserving`, built from
`lem:tilt`). -/
theorem pullout : ∀ {W : Type} (c : PulloutChain W),
    c.AllMassPreserving → dec c.toTmon = c.toDmon := by
  intro W c
  induction c with
  | base a => intro _; rfl
  | pureMap h rest ih =>
      intro hm
      change dec (Finsupp.mapDomain h rest.toTmon) = Finsupp.mapDomain h rest.toDmon
      rw [(pure_maps h rest.toTmon).2, ih hm]
  | unitIns c' rest ih =>
      intro hm
      change dec (dstL rest.toTmon (ret c')) = dstL rest.toDmon (ret c')
      rw [dec_dstL, dec_ret, ih hm]
  | strengthStep leaf rest ih =>
      intro hm
      change dec (dstL rest.toTmon leaf) = dstL rest.toDmon (dec leaf)
      rw [dec_dstL, ih hm]
  | bindStep k rest ih =>
      intro hm
      obtain ⟨hk, hrest⟩ := hm
      change dec (bind rest.toTmon k) = bind rest.toDmon (fun x => dec (k x))
      rw [dec_bind_of_massPreserving hk, ih hrest]

end NeSyCat
