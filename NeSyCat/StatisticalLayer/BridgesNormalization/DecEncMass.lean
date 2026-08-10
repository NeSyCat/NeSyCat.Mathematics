/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.SemiringMonads.SemiringMonad
import NeSyCat.CategoricalLayer.SemiringMonads.Dist
import NeSyCat.CategoricalLayer.SemiringMonads.LogIso

/-!
# Decode, encode, mass: the bridges of `def:dec-enc-mass`

Blueprint item `def:dec-enc-mass`
(`blueprint/src/content.tex`, §"Bridges and normalization", `[NeSy26, App. B draft/T3]`).

A `Tmon X`-value is read here, via `lem:log-iso`'s isomorphism `Tmon ≅ LTmon`,
directly as a log-weight vector: the type `LogTens X = MS LogS X` of
`NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean` (`⊥`-coordinates reading
as `-∞`, i.e. zero mass, matching `LogS`'s own `0 = ⊥`). `Z` (total mass),
`dec` (softmax), and `enc` (pointwise log) are stated over this
representation, reusing `ofLogTens`/`toLogTens` (`lem:log-iso`) and `Dist`
(`def:dist-monad`) directly rather than re-deriving any exp/log analysis.

`Z X a := Σ_x e^{a_x}` is realized as `(ofLogTens a).sum (fun _ w => w)`,
the same total-mass sum `Dist` itself uses. `dec` scales `ofLogTens a` (the
mass-carrier reading of `a`) by `(Z a)⁻¹`; its codomain is `Tens X` (every
finitely supported nonnegative weight function), not the mass-one subtype
`Dist X`, since `Z a = 0` (the all-`-∞`/zero-mass log-vector) has no
mass-one softmax — a genuine edge case the blueprint's own softmax formula
inherits (division by `Z(a)`), left to the ambient `0⁻¹ = 0` convention.
`enc`'s domain is exactly `Dist X`, so this edge case never arises there:
every `p : Dist X` already carries mass `1`.
-/

namespace NeSyCat

open scoped NNReal

variable {X Y Z' : Type*}

/-! ### `Z`, `dec`, `enc` -/

/-- Blueprint `def:dec-enc-mass` (total mass): `Z(a) := Σ_x e^{a_x}`, realized
as the total mass of `a`'s mass-carrier reading `ofLogTens a` (`lem:log-iso`),
`⊥`/`-∞` coordinates contributing `0` automatically. -/
-- (A1 bijection-law companion of `dec`, content.tex def:dec-enc-mass)
@[blueprint_internal]
noncomputable def Z (a : LogTens X) : ℝ≥0 := (ofLogTens a).sum (fun _ w => w)

/-- Blueprint `def:dec-enc-mass` (decode, softmax): `dec(a)_x := e^{a_x}/Z(a)`,
the mass-carrier reading of `a` (`ofLogTens a`) scaled by `(Z a)⁻¹` (the
`0⁻¹ = 0` convention handling the zero-mass edge case, see the module doc
comment). -/
noncomputable def dec (a : LogTens X) : Tens X := (Z a)⁻¹ • ofLogTens a

/-- Blueprint `def:dec-enc-mass` (encode, pointwise log): `enc(p)_x := log p(x)`,
the log-carrier reading (`toLogTens`, `lem:log-iso`) of `p`'s underlying mass
function. -/
-- (A1 bijection-law companion of `dec`, content.tex def:dec-enc-mass)
@[blueprint_internal]
noncomputable def enc (p : Dist X) : LogTens X := toLogTens p.1

/-- `Z` unfolds to a `Finsupp.sum` over the log-weight vector `a` directly,
via `logEquiv.symm` pointwise (`Finsupp.sum_mapRange_index`, unfolding
`ofLogTens`). -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem Z_eq_sum (a : LogTens X) : Z a = a.sum (fun _ w => (logEquiv.symm w : ℝ≥0)) := by
  change (Finsupp.mapRange logEquiv.symm _ a).sum (fun _ w => w) = _
  exact Finsupp.sum_mapRange_index (fun _ => rfl)

/-- `dec` unfolds pointwise: `dec(a)(x) = (ofLogTens a)(x) / Z(a)`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem dec_apply (a : LogTens X) (x : X) : dec a x = (ofLogTens a) x / Z a := by
  unfold dec
  rw [Finsupp.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-! ### `lem:pure-maps` -/

/-- `logEquiv.symm` sends `0` to `0`, the `h_zero` side condition needed to
push it through `Finsupp.mapDomain`: chases `logEquiv_zero`
(`lem:log-iso`) through `Equiv.symm_apply_apply`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem logEquiv_symm_zero : logEquiv.symm (0 : LogS) = 0 := by
  rw [← logEquiv_zero, Equiv.symm_apply_apply]

/-- `logEquiv.symm` is additive (`LogS`'s own `+`, i.e. `lse`, to `ℝ≥0`'s
`+`): the `h_add` side condition needed to push it through
`Finsupp.mapDomain`, chasing `logEquiv_map_add` (`lem:log-iso`) through the
equivalence's own round-trip identities. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem logEquiv_symm_add (a b : LogS) :
    logEquiv.symm (a + b) = logEquiv.symm a + logEquiv.symm b := by
  have h := logEquiv_map_add (logEquiv.symm a) (logEquiv.symm b)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]

/-- Blueprint `lem:pure-maps` (mass invariance, pointwise companion): `Z`
is invariant under pushing a log-weight vector forward along a pure map `h`
(`\Tmon(h)`, realized as `Finsupp.mapDomain h` — the fibers `h⁻¹(y)`
combine via `LogS`'s own `+ = lse`, so this is exactly "summing `e^{a_x}`
fiber by fiber rearranges the same total sum"). -/
-- (A1 bijection-law companion of `pure_maps`, content.tex lem:pure-maps)
@[blueprint_internal]
theorem Z_mapDomain (h : X → Y) (a : LogTens X) : Z (Finsupp.mapDomain h a) = Z a := by
  rw [Z_eq_sum, Z_eq_sum]
  exact Finsupp.sum_mapDomain_index (fun _ => logEquiv_symm_zero)
    (fun _ m₁ m₂ => logEquiv_symm_add m₁ m₂)

/-- `ofLogTens` (`lem:log-iso`) commutes with `Finsupp.mapDomain`: the
mass-carrier reading of a pushed-forward log-weight vector is the
pushed-forward mass-carrier reading, via `Finsupp.mapDomain_mapRange`
(`logEquiv.symm` being additive). -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem ofLogTens_mapDomain (h : X → Y) (a : LogTens X) :
    ofLogTens (Finsupp.mapDomain h a) = Finsupp.mapDomain h (ofLogTens a) := by
  unfold ofLogTens
  exact (Finsupp.mapDomain_mapRange h a logEquiv.symm logEquiv_symm_zero logEquiv_symm_add).symm

/-- Blueprint `lem:pure-maps` (bundled): for pure `h : X → Y`, `Z(\Tmon(h)(a))
= Z(a)`, and `\Tmon(h) \seq \dec_Y = \dec_X \seq \Dmon(h)`, i.e. decoding
commutes with pushing a log-weight vector forward along `h` (`\Tmon(h)`,
`\Dmon(h)` both realized as `Finsupp.mapDomain h`, at the log and mass
carriers respectively): dividing by the (fiber-invariant, `Z_mapDomain`)
total mass commutes with pushing the mass-carrier reading of `a` forward,
since `Finsupp.mapDomain` and scalar multiplication commute
(`Finsupp.mapDomain_smul`) and `ofLogTens` (`lem:log-iso`) commutes with
`Finsupp.mapDomain` (`Finsupp.mapDomain_mapRange`, `logEquiv.symm` being
additive). -/
theorem pure_maps (h : X → Y) (a : LogTens X) :
    Z (Finsupp.mapDomain h a) = Z a ∧
      dec (Finsupp.mapDomain h a) = Finsupp.mapDomain h (dec a) := by
  refine ⟨Z_mapDomain h a, ?_⟩
  unfold dec
  rw [Z_mapDomain, ofLogTens_mapDomain, Finsupp.mapDomain_smul]

/-! ### `lem:units` -/

/-- `ofLogTens` undoes `ret` at the log carrier: the mass-carrier reading of
`ret_{\Tmon}(x)` is again `ret(x)`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem ofLogTens_ret (x : X) : ofLogTens (ret x : LogTens X) = (ret x : Tens X) := by
  rw [← toLogTens_ret x, ofLogTens_toLogTens]

/-- Blueprint `lem:units` (mass of `Ret`): `Z(\Ret_\Tmon(x)) = 1`. -/
-- (A1 bijection-law companion of `units`, content.tex lem:units)
@[blueprint_internal]
theorem Z_ret (x : X) : Z (ret x : LogTens X) = 1 := by
  unfold Z
  rw [ofLogTens_ret]
  exact ret_mass_one x

/-- Blueprint `lem:units` (`\Ret_\Tmon \seq \dec = \Ret_\Dmon`, pointwise
companion): `\dec(\Ret_\Tmon(x)) = \Ret_\Dmon(x)`, since `\Ret_\Tmon(x)` has
mass `1` (`Z_ret`), so decoding just returns its (already mass-carrier)
reading `ofLogTens_ret` unscaled. -/
-- (A1 bijection-law companion of `units`, content.tex lem:units)
@[blueprint_internal]
theorem dec_ret (x : X) : dec (ret x : LogTens X) = (ret x : Tens X) := by
  unfold dec
  rw [Z_ret, inv_one, one_smul, ofLogTens_ret]

/-- Blueprint `lem:units` (four identities, bundled): `\Ret_\Dmon \seq \enc =
\Ret_\Tmon`; `\enc \seq \dec = \mathrm{id}_\Dmon`; hence `\Ret_\Tmon \seq \dec
= \Ret_\Dmon`; and `Z(\Ret_\Tmon(x)) = 1`. -/
theorem units :
    (∀ x : X, enc (Dist.pure x) = (ret x : LogTens X)) ∧
      (∀ p : Dist X, dec (enc p) = p.1) ∧
      (∀ x : X, dec (ret x : LogTens X) = (ret x : Tens X)) ∧
      (∀ x : X, Z (ret x : LogTens X) = 1) := by
  refine ⟨fun x => ?_, fun p => ?_, dec_ret, Z_ret⟩
  · unfold enc Dist.pure
    exact toLogTens_ret x
  · unfold dec
    have hZ : Z (enc p) = 1 := by
      unfold Z enc
      rw [ofLogTens_toLogTens]
      exact p.2
    rw [hZ, inv_one, one_smul, enc, ofLogTens_toLogTens]

/-! ### `lem:tensor` -/

/-- `ret` has total `S`-mass `1` for every semiring `S`, generalizing
`ret_mass_one` (`NeSyCat/CategoricalLayer/SemiringMonads/Dist.lean`, specific
to `S = ℝ≥0`) to an arbitrary semiring: `ret x = Finsupp.single x 1`, whose
sum collapses to the value `1` at `x`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem ret_sum_one {S : Type*} [Semiring S] {X : Type*} (x : X) :
    (ret x : MS S X).sum (fun _ w => w) = (1 : S) := by
  unfold ret
  exact Finsupp.sum_single_index rfl

/-- `bind`'s total `S`-mass factors through `k`'s per-index total mass:
`(bind f k).sum id = f.sum (fun x w => w * (k x).sum id)`, generalizing the
Fubini computation of `bind_mass_one`
(`NeSyCat/CategoricalLayer/SemiringMonads/Dist.lean`) from the constant
mass-one case to an arbitrary per-index total. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem bind_sum_eq {S : Type*} [CommSemiring S] {X Y : Type*} (f : MS S X) (k : X → MS S Y) :
    (bind f k).sum (fun _ w => w) = f.sum (fun x w => w * (k x).sum (fun _ w => w)) := by
  unfold bind
  rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]

/-- `dstL`'s total `S`-mass is multiplicative: `(dstL f g).sum id = f.sum id
* g.sum id`, by applying `bind_sum_eq` twice (once for each `bind` layer of
`dstL`'s definition) and `ret_sum_one` at the innermost `ret`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem dstL_sum_mul {S : Type*} [CommSemiring S] {X Y : Type*} (f : MS S X) (g : MS S Y) :
    (dstL f g).sum (fun _ w => w) = f.sum (fun _ w => w) * g.sum (fun _ w => w) := by
  unfold dstL
  rw [bind_sum_eq]
  have hinner : ∀ x : X,
      (bind g (fun y => ret (x, y))).sum (fun _ w => w) = g.sum (fun _ w => w) := by
    intro x
    rw [bind_sum_eq]
    simp_rw [ret_sum_one, mul_one]
  simp_rw [hinner]
  rw [← Finsupp.sum_mul]

/-- `toLogTens` (`lem:log-iso`) commutes with `dstL`: applying the log
transport after pairing agrees with pairing after transporting each factor,
by unfolding `dstL` to two nested `bind`s and applying `toLogTens_bind`
(twice) and `toLogTens_ret`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem toLogTens_dstL {X Y : Type*} (f : Tens X) (g : Tens Y) :
    toLogTens (dstL f g) = dstL (toLogTens f) (toLogTens g) := by
  unfold dstL
  rw [toLogTens_bind]
  refine congrArg (bind (toLogTens f)) ?_
  funext x
  rw [toLogTens_bind]
  refine congrArg (bind (toLogTens g)) ?_
  funext y
  exact toLogTens_ret (x, y)

/-- `ofLogTens` (`lem:log-iso`) commutes with `dstL`, the inverse-direction
twin of `toLogTens_dstL`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem ofLogTens_dstL {X Y : Type*} (a : LogTens X) (b : LogTens Y) :
    ofLogTens (dstL a b) = dstL (ofLogTens a) (ofLogTens b) := by
  have h : toLogTens (dstL (ofLogTens a) (ofLogTens b)) = dstL a b := by
    rw [toLogTens_dstL, toLogTens_ofLogTens, toLogTens_ofLogTens]
  rw [← h, ofLogTens_toLogTens]

/-- Mass is multiplicative under `dstL` (`lem:tensor`'s mass clause,
pointwise companion): `Z(dstL a b) = Z(a) Z(b)`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem Z_dstL {X Y : Type*} (a : LogTens X) (b : LogTens Y) : Z (dstL a b) = Z a * Z b := by
  unfold Z
  rw [ofLogTens_dstL, dstL_sum_mul]

/-- Decoding commutes with `dstL` (`lem:tensor`'s decode clause, pointwise
companion): `\dec(dstL\,a\,b) = dstL\,(\dec\,a)\,(\dec\,b)`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem dec_dstL {X Y : Type*} (a : LogTens X) (b : LogTens Y) :
    dec (dstL a b) = dstL (dec a) (dec b) := by
  ext ⟨x, y⟩
  rw [dec_apply, ofLogTens_dstL, dstL_apply, Z_dstL, dstL_apply, dec_apply, dec_apply]
  rw [div_mul_div_comm]

/-- Blueprint `lem:tensor` (Tensor, bundled): writing `a ⊗ b := dstL a b`
for the tensorial-strength pairing `(a⊗b)_{(x,y)} = a_x+b_y` (`dstL_apply`
together with `logS_mul_eq_logMul`/`logMul_coe_coe`), mass is multiplicative,
`Z(a⊗b) = Z(a)Z(b)`, and decoding commutes with tensoring,
`\dec(a\otimes b) = \dec(a)\otimes\dec(b)` (the right-hand `⊗` the analogous
independent-joint pairing `dstL` on `Tens`). -/
theorem tensor {X Y : Type*} (a : LogTens X) (b : LogTens Y) :
    Z (dstL a b) = Z a * Z b ∧ dec (dstL a b) = dstL (dec a) (dec b) :=
  ⟨Z_dstL a b, dec_dstL a b⟩

/-! ### `lem:strengths` -/

/-- Blueprint `lem:strengths` (strength at slot `j`, general form): the
`m`-ary insertion `\sigma^{(j)}_\Tmon(x_1,\ldots,a,\ldots,x_m)` reduces, up
to reassociating the flat product `X_1\times\cdots\times X_m` into
`(\mathrm{Before}\times X_j)\times\mathrm{After}`, to tensoring the
effectful slot `a` with a *single* pure background value on each side:
`bkg : B` standing for the tuple `(x_1,\ldots,x_{j-1})` before slot `j`,
`aft : A` for `(x_{j+1},\ldots,x_m)` after it.
`strength bkg a aft := (\Ret_\Tmon(bkg)\otimes a)\otimes\Ret_\Tmon(aft)`
(`dstL`, `lem:units`, `lem:tensor`), general in `B`/`A` since every concrete
`m`, `j` instantiates `B := X_1\times\cdots\times X_{j-1}`, `A :=
X_{j+1}\times\cdots\times X_m`. -/
-- (A1 bijection-law companion of `strengths`, content.tex lem:strengths)
@[blueprint_internal]
noncomputable def strength {B X A : Type*} (bkg : B) (a : LogTens X) (aft : A) :
    LogTens ((B × X) × A) :=
  dstL (dstL (ret bkg : LogTens B) a) (ret aft : LogTens A)

/-- Blueprint `lem:strengths` (bundled): `Z(\sigma^{(j)}_\Tmon(x_1,\ldots,a,
\ldots,x_m)) = Z(a)$ (the pure coordinates contribute mass `1`,
`lem:units`, so the tensor product's mass, `lem:tensor`, reduces to `a`'s
own), and `\sigma^{(j)}_\Tmon \seq \dec = (\mathrm{id},\ldots,\dec,\ldots,
\mathrm{id}) \seq \sigma^{(j)}_\Dmon \seq (\mathrm{id}\otimes\cdots\otimes
\dec_j\otimes\cdots\otimes\mathrm{id})$: decoding the strength agrees with
decoding only the effectful slot and inserting the plain coordinates as
certain (`\Ret`) values, `\dec(\sigma^{(j)}_\Tmon(bkg,a,aft)) =
\sigma^{(j)}_\Dmon(bkg,\dec(a),aft)`. -/
theorem strengths {B X A : Type*} (bkg : B) (a : LogTens X) (aft : A) :
    Z (strength bkg a aft) = Z a ∧
      dec (strength bkg a aft) =
        dstL (dstL (ret bkg : Tens B) (dec a)) (ret aft : Tens A) := by
  unfold strength
  constructor
  · rw [Z_dstL, Z_dstL, Z_ret, Z_ret, one_mul, mul_one]
  · rw [dec_dstL, dec_dstL, dec_ret, dec_ret]

end NeSyCat
