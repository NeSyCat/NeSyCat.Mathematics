/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.StatisticalLayer.BridgesNormalization.DecEncMass
import NeSyCat.StatisticalLayer.BridgesNormalization.Tilt

/-!
# The normalizer

Blueprint items `def:normalizer`, `lem:normalizer-props`, and
`lem:normalized-heads` (`blueprint/src/content.tex`, §"Bridges and
normalization", `[NeSy26, App. B draft/T3]`). Builds on
`NeSyCat/StatisticalLayer/BridgesNormalization/DecEncMass.lean`'s
`dec`/`enc`/`Z` suite and `Tilt.lean`'s `PulloutChain`/`pullout`.

`nrm := dec ⨟ enc` is realized as `toLogTens ∘ dec` rather than literally
`enc ∘ dec`: `enc`'s domain is `Dist X` (mass-one distributions), and
`dec(a)` is not a proof-carrying mass-one value (it lands in the full mass
carrier `Tens X`, `def:dec-enc-mass`'s own disclosed scope note). `enc`
itself is exactly `toLogTens ∘ Subtype.val`, so applying `toLogTens`
directly to `dec(a)` is the same construction, generalized to inputs that
are not already known to be mass one. At the one genuinely degenerate input
`a = 0` (`Z(a) = 0`, the all-`-∞`/zero-mass vector), `dec(a) = 0` and
`nrm(a) = 0`: `nrm` is total, but `lem:normalizer-props`(ii)'s mass-one
claim, like `dec`'s own mass-one property (`dec_total_mass_eq_one`,
`Tilt.lean`), genuinely needs `Z(a) ≠ 0` — the blueprint's own softmax
formula inherits the same edge case here.

"`a + c\cdot\mathbf 1`" (`lem:normalizer-props`(iii)) is introduced inline
inside the lemma's own displayed clause, no separate `definition` env (the
`lem:tilt`/`tilt` precedent): realized here as `shift`, an
`@[blueprint_internal]` companion, scaling the mass-carrier reading of `a`
by `Real.exp c` (equivalently, adding the real constant `c` to every finite
log-weight coordinate, leaving `-∞` coordinates at `-∞`).

`lem:normalized-heads`'s "every neural symbol interpretation is
post-composed with `nrm`" is realized as `PulloutChain.normalized`, the
node-by-node transform replacing every raw leaf/strength-leaf/bind
continuation of a `PulloutChain` with its `nrm`-composed form; the theorem
`normalized_heads` needs the same `Z ≠ 0` nondegeneracy at every raw bind
continuation (only there, since `AllMassPreserving` itself only constrains
bind nodes) to conclude `dec c.normalized.toTmon = c.toDmon` — mass
preservation after normalizing (`thm:pullout`) composed with "no prediction
changes" (`lem:normalizer-props`(i), unconditional, via
`PulloutChain.normalized_toDmon_eq`).
-/

namespace NeSyCat

open scoped NNReal

variable {X Y : Type*}

/-! ### `def:normalizer` -/

/-- Blueprint `def:normalizer`: `nrm_X := dec_X ⨟ enc_X`, realized as
`toLogTens ∘ dec` (see the module doc comment for why this is the honest
total realization of `enc ∘ dec`). Concretely the log-softmax:
`nrm(a) = a - log Z(a)·1`. -/
noncomputable def nrm (a : LogTens X) : LogTens X := toLogTens (dec a)

/-! ### `lem:normalizer-props` -/

/-- `dec` applied to a value freshly transported via `toLogTens` unwinds to
scaling by the inverse of its own total mass, via the `ofLogTens ∘
toLogTens = id` round trip (`lem:log-iso`): the pointwise companion behind
`dec_nrm` below. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem dec_toLogTens (p : Tens X) : dec (toLogTens p) = (p.sum (fun _ w => w))⁻¹ • p := by
  unfold dec Z
  rw [ofLogTens_toLogTens]

/-- Blueprint `lem:normalizer-props` (i): `dec ∘ nrm = dec`, unconditionally
(true even at the degenerate `Z(a) = 0` input, where both sides are `0`).
Proved via `dec_toLogTens` and `dec_total_mass_eq_one`
(`Tilt.lean`) at `Z(a) ≠ 0`, and directly at `Z(a) = 0`. -/
-- (A1 bijection-law companion of `normalizer_props`, content.tex
-- lem:normalizer-props)
@[blueprint_internal]
theorem dec_nrm (a : LogTens X) : dec (nrm a) = dec a := by
  unfold nrm
  rw [dec_toLogTens]
  by_cases hZ : Z a = 0
  · have hda : dec a = 0 := by unfold dec; rw [hZ, inv_zero, zero_smul]
    rw [hda]
    simp
  · rw [dec_total_mass_eq_one hZ, inv_one, one_smul]

/-- `shift`'s scaling factor, `Real.exp c` read as a nonnegative real: always
positive, hence nonzero, for every real `c`. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
noncomputable def expC (c : ℝ) : ℝ≥0 := ⟨Real.exp c, (Real.exp_pos c).le⟩

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem expC_ne_zero (c : ℝ) : expC c ≠ 0 := by
  simp only [expC, ne_eq, ← NNReal.coe_eq_zero]
  exact (Real.exp_pos c).ne'

/-- `a + c·1` (`lem:normalizer-props`(iii), introduced inline inside the
lemma's own displayed clause, no separate `definition` env, the `lem:tilt`/
`tilt` precedent): scales the mass-carrier reading of `a` by `Real.exp c`,
i.e. adds the real constant `c` to every finite log-weight coordinate while
leaving `-∞` coordinates at `-∞` (`⊗`'s absorption, `lem:log-iso`). -/
-- (A1 bijection-law companion of `normalizer_props`, content.tex
-- lem:normalizer-props)
@[blueprint_internal]
noncomputable def shift (a : LogTens X) (c : ℝ) : LogTens X :=
  toLogTens (expC c • ofLogTens a)

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem ofLogTens_shift (a : LogTens X) (c : ℝ) :
    ofLogTens (shift a c) = expC c • ofLogTens a := by
  unfold shift
  rw [ofLogTens_toLogTens]

/-- `Z` of a shifted vector scales by the same factor `Real.exp c`: the
pointwise companion feeding `lem:normalizer-props`(iii)'s proof, matching
the blueprint's own `Z(a+c\mathbf1) = e^cZ(a)`. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem Z_shift (a : LogTens X) (c : ℝ) : Z (shift a c) = expC c * Z a := by
  unfold Z
  rw [ofLogTens_shift, Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]

/-- `dec` is invariant under `shift`: shifting every finite log-weight
coordinate by a common real constant `c` (equivalently scaling the
mass-carrier reading by the positive factor `Real.exp c`) does not change
the decoded softmax, unconditionally in `a`. -/
-- (A1 bijection-law companion of `normalizer_props`, content.tex
-- lem:normalizer-props)
@[blueprint_internal]
theorem dec_shift (a : LogTens X) (c : ℝ) : dec (shift a c) = dec a := by
  unfold dec
  rw [ofLogTens_shift, Z_shift, smul_smul,
    show (expC c * Z a)⁻¹ * expC c = (Z a)⁻¹ by
      rw [mul_inv, mul_comm (expC c)⁻¹, mul_assoc, inv_mul_cancel₀ (expC_ne_zero c), mul_one]]

/-- Blueprint `lem:normalizer-props` (Normalizer properties): `nrm`
(Definition~`def:normalizer`) satisfies (i) `dec ∘ nrm = dec` (predictions
unchanged, unconditional); (ii) `Z(nrm(a)) = 1` (mass one) whenever
`Z(a) ≠ 0` (the genuine edge case disclosed in the module doc comment);
(iii) `nrm(a + c·1) = nrm(a)` for every constant `c` (kills the shift,
unconditional); (iv) `nrm ∘ nrm = nrm` (idempotent, unconditional). -/
theorem normalizer_props (a : LogTens X) :
    dec (nrm a) = dec a ∧
      (Z a ≠ 0 → Z (nrm a) = 1) ∧
      (∀ c : ℝ, nrm (shift a c) = nrm a) ∧
      nrm (nrm a) = nrm a := by
  refine ⟨dec_nrm a, fun hZ => ?_, fun c => ?_, ?_⟩
  · unfold nrm Z
    rw [ofLogTens_toLogTens]
    exact dec_total_mass_eq_one hZ
  · unfold nrm
    rw [dec_shift]
  · change toLogTens (dec (nrm a)) = nrm a
    rw [dec_nrm]
    rfl

/-! ### `lem:normalized-heads` -/

/-- The chain's own nondegeneracy hypothesis: every raw `bindStep`
continuation (before normalizing) has nowhere-zero mass; every other node
contributes no condition (leaves need no nondegeneracy: `dec_nrm` already
holds unconditionally, so normalizing a leaf never changes the chain's
decoded prediction, and `AllMassPreserving` itself only ever constrains
bind nodes). -/
-- (A1 bijection-law companion of `normalized_heads`, content.tex
-- lem:normalized-heads)
@[blueprint_internal]
def PulloutChain.AllNondegenerate : {W : Type} → PulloutChain W → Prop
  | _, .base _ => True
  | _, .pureMap _ rest => rest.AllNondegenerate
  | _, .unitIns _ rest => rest.AllNondegenerate
  | _, .strengthStep _ rest => rest.AllNondegenerate
  | _, .bindStep k rest => (∀ x, Z (k x) ≠ 0) ∧ rest.AllNondegenerate

/-- "Every neural symbol interpretation is post-composed with `nrm`"
(`lem:normalized-heads`): the node-by-node transform of a `PulloutChain`
replacing every leaf, strength leaf, and bind continuation with its
`nrm`-composed form, leaving `pureMap`/`unitIns` nodes structurally
untouched (they carry no leaf/continuation weight data of their own). -/
-- (A1 bijection-law companion of `normalized_heads`, content.tex
-- lem:normalized-heads)
@[blueprint_internal]
noncomputable def PulloutChain.normalized : {W : Type} → PulloutChain W → PulloutChain W
  | _, .base a => .base (nrm a)
  | _, .pureMap h rest => .pureMap h rest.normalized
  | _, .unitIns c rest => .unitIns c rest.normalized
  | _, .strengthStep leaf rest => .strengthStep (nrm leaf) rest.normalized
  | _, .bindStep k rest => .bindStep (fun x => nrm (k x)) rest.normalized

/-- Every `bindStep` continuation of a normalized chain is mass preserving
(constant mass `1`), given the raw chain is nondegenerate
(`AllNondegenerate`): the mass-one clause of `lem:normalizer-props`(ii)
applied at every raw continuation value. -/
-- (A1 bijection-law companion of `normalized_heads`, content.tex
-- lem:normalized-heads)
@[blueprint_internal]
theorem PulloutChain.normalized_allMassPreserving :
    ∀ {W : Type} (c : PulloutChain W), c.AllNondegenerate → c.normalized.AllMassPreserving := by
  intro W c
  induction c with
  | base a => intro _; trivial
  | pureMap h rest ih =>
      intro hnd
      change rest.normalized.AllMassPreserving
      exact ih hnd
  | unitIns c' rest ih =>
      intro hnd
      change rest.normalized.AllMassPreserving
      exact ih hnd
  | strengthStep leaf rest ih =>
      intro hnd
      change rest.normalized.AllMassPreserving
      exact ih hnd
  | bindStep k rest ih =>
      intro hnd
      obtain ⟨hk, hrest⟩ := hnd
      change MassPreserving (fun x => nrm (k x)) ∧ rest.normalized.AllMassPreserving
      exact ⟨⟨1, fun x => (normalizer_props (k x)).2.1 (hk x)⟩, ih hrest⟩

/-- Normalizing every leaf/strength-leaf/bind continuation of a
`PulloutChain` does not change its `Dmon`-side reading (no prediction
changes, `lem:normalizer-props`(i) threaded through the chain,
unconditional in the raw chain). -/
-- (A1 bijection-law companion of `normalized_heads`, content.tex
-- lem:normalized-heads)
@[blueprint_internal]
theorem PulloutChain.normalized_toDmon_eq :
    ∀ {W : Type} (c : PulloutChain W), c.normalized.toDmon = c.toDmon
  | _, .base a => dec_nrm a
  | _, .pureMap h rest => by
      change Finsupp.mapDomain h rest.normalized.toDmon = Finsupp.mapDomain h rest.toDmon
      rw [rest.normalized_toDmon_eq]
  | _, .unitIns c rest => by
      change dstL rest.normalized.toDmon (ret c) = dstL rest.toDmon (ret c)
      rw [rest.normalized_toDmon_eq]
  | _, .strengthStep leaf rest => by
      change dstL rest.normalized.toDmon (dec (nrm leaf)) = dstL rest.toDmon (dec leaf)
      rw [rest.normalized_toDmon_eq, dec_nrm]
  | _, .bindStep k rest => by
      change bind rest.normalized.toDmon (fun x => dec (nrm (k x)))
          = bind rest.toDmon (fun x => dec (k x))
      rw [rest.normalized_toDmon_eq]
      refine congrArg (bind rest.toDmon) ?_
      funext x
      exact dec_nrm (k x)

/-- Blueprint `lem:normalized-heads` (Normalized heads): if every raw bound
continuation of a point-free chain `Φ` (`PulloutChain.AllNondegenerate`)
has nowhere-zero mass, then post-composing every leaf and every bound
continuation with `nrm` (`PulloutChain.normalized`) makes every bound
continuation mass preserving (`def:mass-preserving`), so
Theorem~`thm:pullout` applies: the normalized chain's `Tmon`-side decoded
prediction agrees with its `Dmon`-side reading, which by
Lemma~`lem:normalizer-props`(i) is exactly the original (unnormalized)
chain's own `Dmon`-side prediction. -/
theorem normalized_heads {W : Type} (c : PulloutChain W) (h : c.AllNondegenerate) :
    dec c.normalized.toTmon = c.toDmon := by
  rw [pullout c.normalized (c.normalized_allMassPreserving h), c.normalized_toDmon_eq]

end NeSyCat
