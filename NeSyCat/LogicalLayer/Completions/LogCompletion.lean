/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.SemiringMonads.LatticeSemiring
import NeSyCat.LogicalLayer.Completions.MassCompletion

/-!
# The log completion `[-∞,∞]`

Blueprint items `inst:log-completion-latcsrng`, `lem:log-completion-bounds`
(`blueprint/src/content.tex`, §"Completions") -- by transport along Mathlib's
own `EReal`/`ℝ≥0∞` exponential-logarithm order isomorphism, mirroring
`NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean`'s finite-carrier
construction one level up. Names below carry an `Inf` suffix throughout
(`logEquivInf`, `lseInf`, `logMulInf`, ...) to avoid colliding with `LogIso.lean`'s
identically-shaped finite-carrier names in the same `NeSyCat` namespace.

## Evaluating `EReal` first

Mathlib's `EReal` (`= ℝ ∪ {-∞,∞}`) is the natural candidate for `[-∞,∞]`,
and it turns out to be EXACTLY the right one: `EReal`'s own native addition is
built with the convention `⊥ + ⊤ = ⊤ + ⊥ = ⊥`
(`Mathlib/Data/EReal/Operations.lean`'s own module doc: chosen "to make sure
that the exponential and logarithm between `EReal` and `ℝ≥0∞` respect the
operations") -- this is precisely the FORCED convention `∞ + (-∞) = -∞` the
log row's `⊗` needs (the log-space image of `0 * ∞ = 0`). Mathlib further
supplies the order isomorphism itself, ready-made: `ENNReal.logOrderIso : ℝ≥0∞
≃o EReal` (`ENNReal.log`/`EReal.exp`, mutually inverse, `Mathlib/Analysis/
SpecialFunctions/Log/ENNRealLogExp.lean`), with `ENNReal.log_mul_add : log (x *
y) = log x + log y` UNCONDITIONALLY (no positivity side condition) -- exactly
the bridge `lem:log-iso` builds by hand for the finite carrier, already proved
for the completion.

## The carrier: a fresh synonym, not `EReal` itself

`EReal` already carries its own `Add`/`Mul`/`Neg` instances (the actual
extended-real arithmetic, not our `lseInf`/`logMulInf`), so registering a fresh
`CommSemiring` on `EReal` directly would compete with them -- the same
instance-competition `LogS := WithBot ℝ` (as opposed to using `WithBot ℝ`
itself) avoids one level down. `LogSInf := EReal` is a fresh type synonym for
exactly that reason; `Lattice`/`BoundedOrder` are inherited by an explicit
`inferInstanceAs` (the same "fresh carrier, inherited order" device `LogS`
and `BoolW` use), and the `CommSemiring` is transported from `ℝ≥0∞` along
`logEquivInf`, mirroring `NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean`'s
`instCommSemiringLogS` exactly.

## `lseInf`/`logMulInf`: the completion's explicit `⊕`/`⊗` formulas

`logMulInf a b := a + b` (the underlying `EReal` addition, cast once through
the identity function `toEReal : LogSInf → EReal`); `lseInf a b := logEquivInf
(exp a + exp b)` (`ℝ≥0∞`'s own addition, pulled back). `logSInf_add_eq_lseInf`/
`logSInf_mul_eq_logMulInf` bridge the transported `+`/`*` to these explicit
formulas, exactly as `logS_add_eq_lse`/`logS_mul_eq_logMul` do for `LogS`.
-/

namespace NeSyCat

open scoped NNReal ENNReal

/-! ### The carrier and its order -/

/-- Blueprint `inst:log-completion-latcsrng` (log completion carrier):
`[-∞,∞]`, realized as a fresh type synonym for Mathlib's `EReal` (see the
module doc comment for why not `EReal` itself). -/
-- (A1 bijection-law companion of `instBLatCSRngLogSInf`,
-- content.tex inst:log-completion-latcsrng)
@[blueprint_internal]
def LogSInf : Type := EReal

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
noncomputable instance instLatticeLogSInf : Lattice LogSInf :=
  inferInstanceAs (Lattice EReal)

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
noncomputable instance instBoundedOrderLogSInf : BoundedOrder LogSInf :=
  inferInstanceAs (BoundedOrder EReal)

/-- The identity function `LogSInf → EReal`, a controlled single cast (the
`LogSInf`-level analogue of `LogS`'s "build at `WithBot ℝ`, cast once"
discipline: every lemma below crosses the `LogSInf`/`EReal` boundary through
this one named function, never an ad hoc inline ascription). -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
def toEReal (a : LogSInf) : EReal := a

/-- Blueprint `inst:log-completion-latcsrng` (the exp/log bridge to `ℝ≥0∞`):
`logEquivInf`, Mathlib's `ENNReal.logOrderIso` retyped to the fresh carrier. -/
-- (A1 bijection-law companion of `instBLatCSRngLogSInf`,
-- content.tex inst:log-completion-latcsrng)
@[blueprint_internal]
noncomputable def logEquivInf : ℝ≥0∞ ≃ LogSInf := ENNReal.logOrderIso.toEquiv

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem logEquivInf_apply (x : ℝ≥0∞) : logEquivInf x = ENNReal.log x := rfl

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem toEReal_logEquivInf (x : ℝ≥0∞) : toEReal (logEquivInf x) = ENNReal.log x := rfl

/-- `logEquivInf` is an order isomorphism: `ENNReal.log_le_log_iff`, Mathlib's
own order-iso fact for the exp/log bridge, retyped. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem logEquivInf_le_iff (x y : ℝ≥0∞) : logEquivInf x ≤ logEquivInf y ↔ x ≤ y :=
  ENNReal.log_le_log_iff

/-! ### The transported `CommSemiring LogSInf` -/

/-- Blueprint `inst:log-completion-latcsrng` (semiring structure): transported
from `CommSemiring ℝ≥0∞` along `logEquivInf`, mirroring
`NeSyCat/CategoricalLayer/SemiringMonads/LogIso.lean`'s `instCommSemiringLogS`. -/
-- (A1 bijection-law companion of `instBLatCSRngLogSInf`,
-- content.tex inst:log-completion-latcsrng)
@[blueprint_internal]
noncomputable instance instCommSemiringLogSInf : CommSemiring LogSInf :=
  Equiv.commSemiring logEquivInf.symm

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem logSInf_add_def (a b : LogSInf) :
    a + b = logEquivInf (logEquivInf.symm a + logEquivInf.symm b) := rfl

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem logSInf_mul_def (a b : LogSInf) :
    a * b = logEquivInf (logEquivInf.symm a * logEquivInf.symm b) := rfl

/-! ### `lseInf`/`logMulInf`: the explicit `⊕`/`⊗` formulas -/

/-- Blueprint `inst:log-completion-latcsrng` (`⊕`, the completed
log-sum-exp): `lseInf a b := logEquivInf (exp a + exp b)`, `ℝ≥0∞`'s own
addition pulled back through the exp/log bridge -- the completion of `LogS`'s
`lse`. -/
-- (A1 bijection-law companion of `instBLatCSRngLogSInf`,
-- content.tex inst:log-completion-latcsrng)
@[blueprint_internal]
noncomputable def lseInf (a b : LogSInf) : LogSInf :=
  logEquivInf (EReal.exp (toEReal a) + EReal.exp (toEReal b))

/-- Blueprint `inst:log-completion-latcsrng` (`⊗`, log-space multiplication):
`logMulInf a b := a + b`, `EReal`'s own native addition -- the FORCED
convention `∞ + (-∞) = -∞` lives here (see the module doc comment). -/
-- (A1 bijection-law companion of `instBLatCSRngLogSInf`,
-- content.tex inst:log-completion-latcsrng)
@[blueprint_internal]
noncomputable def logMulInf (a b : LogSInf) : LogSInf := (toEReal a + toEReal b : EReal)

/-- The forced convention, stated directly: `∞ ⊗ (-∞) = -∞`. -/
-- (A1 bijection-law companion of `instBLatCSRngLogSInf`,
-- content.tex inst:log-completion-latcsrng)
@[blueprint_internal]
theorem logMulInf_top_bot : logMulInf (⊤ : LogSInf) ⊥ = ⊥ := by
  unfold logMulInf toEReal
  change (⊤ : EReal) + ⊥ = ⊥
  simp

/-- The transported `+` equals `lseInf`. -/
-- (A1 bijection-law companion of `instBLatCSRngLogSInf`,
-- content.tex inst:log-completion-latcsrng)
@[blueprint_internal]
theorem logSInf_add_eq_lseInf (a b : LogSInf) : a + b = lseInf a b := by
  rw [logSInf_add_def]; unfold lseInf; congr 1

/-- `logEquivInf.symm`, read through `ENNReal.log`, is the identity on
`LogSInf` (via `toEReal`): the right-inverse half of `logEquivInf`, restated
at the `toEReal` level for the bridging proofs below. -/
-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem toEReal_logEquivInf_symm (a : LogSInf) :
    ENNReal.log (logEquivInf.symm a) = toEReal a := by
  rw [← toEReal_logEquivInf, Equiv.apply_symm_apply]

/-- The transported `*` equals `logMulInf`. -/
-- (A1 bijection-law companion of `instBLatCSRngLogSInf`,
-- content.tex inst:log-completion-latcsrng)
@[blueprint_internal]
theorem logSInf_mul_eq_logMulInf (a b : LogSInf) : a * b = logMulInf a b := by
  rw [logSInf_mul_def]
  unfold logMulInf
  have key : toEReal (logEquivInf (logEquivInf.symm a * logEquivInf.symm b))
      = toEReal a + toEReal b := by
    rw [toEReal_logEquivInf, ENNReal.log_mul_add, toEReal_logEquivInf_symm,
      toEReal_logEquivInf_symm]
  exact key

/-! ### `BLatCSRng LogSInf` -/

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem logSInf_add_le_add_left {a b : LogSInf} (h : a ≤ b) (c : LogSInf) :
    c + a ≤ c + b := by
  rw [logSInf_add_def, logSInf_add_def, logEquivInf_le_iff]
  have h' : logEquivInf.symm a ≤ logEquivInf.symm b := by
    rwa [← logEquivInf_le_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  gcongr

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem logSInf_add_le_add_right {a b : LogSInf} (h : a ≤ b) (c : LogSInf) :
    a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]; exact logSInf_add_le_add_left h c

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem logSInf_mul_le_mul_left {a b : LogSInf} (h : a ≤ b) (c : LogSInf) :
    c * a ≤ c * b := by
  rw [logSInf_mul_def, logSInf_mul_def, logEquivInf_le_iff]
  have h' : logEquivInf.symm a ≤ logEquivInf.symm b := by
    rwa [← logEquivInf_le_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  gcongr

-- (C2-E4a/A2 completeness census: pre-existing internal helper, not itself
-- blueprint-cited)
@[blueprint_internal]
theorem logSInf_mul_le_mul_right {a b : LogSInf} (h : a ≤ b) (c : LogSInf) :
    a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c]; exact logSInf_mul_le_mul_left h c

/-- Blueprint `inst:log-completion-latcsrng` (log completion, semiring row):
`[-∞,∞]` (`⊕ = \mathrm{lse}`, `⊗ = +`), monotone (transported from `ℝ≥0∞`'s
own monotonicity along the order isomorphism `logEquivInf_le_iff`) and
bounded (`⊥ = -∞`, `⊤ = ∞`, inherited from `EReal`). -/
noncomputable instance instBLatCSRngLogSInf : BLatCSRng LogSInf where
  add_le_add_left h c := logSInf_add_le_add_left h c
  add_le_add_right h c := logSInf_add_le_add_right h c
  mul_le_mul_left h c := logSInf_mul_le_mul_left h c
  mul_le_mul_right h c := logSInf_mul_le_mul_right h c
  mul_comm := mul_comm

/-! ### `lem:log-completion-bounds`: discharging `lem:lifted-log`'s bounds
clause -/

/-- Blueprint `lem:log-completion-bounds` (the log row's order-family bounds,
now concrete): on the completed carrier `LogSInf`, `def:order-family`'s
generic bounds instantiate to `⊥ = (∞,-∞)` and `⊤ = (-∞,∞)`, discharging
`lem:lifted-log`'s deferred bounds clause. -/
theorem lifted_log_bounds :
    twoSlot (orderBot : MS LogSInf BoolW) = (⊤, ⊥) ∧
      twoSlot (orderTop : MS LogSInf BoolW) = (⊥, ⊤) :=
  ⟨twoSlot_orderBot, twoSlot_orderTop⟩

end NeSyCat
