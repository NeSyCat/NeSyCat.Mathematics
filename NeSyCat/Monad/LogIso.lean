/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.Monad.LatticeSemiring
import NeSyCat.Monad.SemiringMonad

/-!
# The log semiring and the log isomorphism

Blueprint item `lem:log-iso` (`blueprint/src/content.tex`, §"Semiring weight
monads", `[NeSy26, App. A]`), and the log instance of `def:lattice-semiring`
(`blueprint/src/content.tex`, same section) deferred from
`NeSyCat/Monad/LatticeSemiring.lean`.

## The carrier

`LogS := WithBot ℝ` (a plain type synonym `def`, not `abbrev`, matching
`BoolW := Bool` in `LatticeSemiring.lean` — this file's own `Add`/`Mul`
instances on `LogS` must not compete with, or be shadowed by, any instances
already declared for `WithBot ℝ` itself). Its native lattice order (`⊥`,
`⊓`, `⊔`) is inherited directly (`instLatticeLogS`/`instOrderBotLogS`); its
semiring structure is installed by **transport** along `logEquiv` (Mathlib's
`Equiv.commSemiring`, `Mathlib/Algebra/Ring/TransferInstance.lean`) from the
existing `CommSemiring ℝ≥0`, rather than proved by hand from raw real
analysis. The transported `+`/`*` are then shown, as separate bridging
lemmas, to equal the two explicit formulas `lse`/`logMul` the blueprint
displays — this equality (`logS_add_eq_lse`, `logS_mul_eq_logMul`) is the
mathematical heart of `lem:log-iso`.

Throughout, "WB"-suffixed private helpers (`logToFunWB`, `lseWB`, ...) are
plain functions `ℝ≥0 → WithBot ℝ`/`WithBot ℝ → WithBot ℝ → WithBot ℝ` built
and verified using `WithBot ℝ`'s own ambient instances (no `def`-wrapping
friction); the public `LogS`-typed declarations (`logToFun`, `lse`, ...) are
each obtained from their "WB" twin by a single top-level definitional cast
(`LogS` and `WithBot ℝ` are the same type, just not *reducibly* so — the
cast typechecks by unfolding `LogS` once, exactly as `BoolW`'s `Lattice`
instance is obtained from `Bool`'s). Mixing the two levels *inside* a single
proof (rather than at this one controlled boundary) reliably confuses
`rw`/`simp`'s "instances"-transparency matching against the kernel's full
definitional equality, so every lemma below is stated and used purely at
one level or the other.

## Contents

* `logEquiv : ℝ≥0 ≃ LogS` — `0 ↦ ⊥`, `x > 0 ↦ log x`; inverse `⊥ ↦ 0`,
  `a ↦ exp a`.
* `lse`, `logMul` — the blueprint's explicit `⊕`/`⊗` formulas on `LogS`.
* the transported `CommSemiring LogS` instance, plus `logS_add_eq_lse` /
  `logS_mul_eq_logMul` bridging it to `lse`/`logMul`.
* `logRingEquiv : ℝ≥0 ≃+* LogS` — the semiring isomorphism proper.
* `instLatCSRngLogS : LatCSRng LogS` — completing `def:lattice-semiring`.
* `logTensEquiv X : MS ℝ≥0 X ≃ MS LogS X` and `LogTens` — the monad
  isomorphism `Tmon ≅ LTmon`.
-/

namespace NeSyCat

open scoped NNReal

/-! ### The carrier `LogS` and its native lattice order -/

/-- Blueprint `def:lattice-semiring` (log carrier): `LogS := ℝ ∪ {-∞}`,
realized as Mathlib's `WithBot ℝ`. See the module doc comment for why this
is a plain `def`, not `abbrev`. -/
def LogS : Type := WithBot ℝ

/-- `LogS` inherits `WithBot ℝ`'s lattice order (`⊓ = min`, `⊔ = max`)
directly — the same "fresh carrier, inherited order" device `BoolW` uses in
`LatticeSemiring.lean`. -/
noncomputable instance instLatticeLogS : Lattice LogS :=
  inferInstanceAs (Lattice (WithBot ℝ))

/-- `LogS` has a least element `⊥` (matching the blueprint's `-∞`), inherited
from `WithBot ℝ`; unlike the Boolean instance, there is **no** in-carrier
`⊤` (log is unbounded above), so `LogS` is only ever a `LatCSRng`, never a
`BLatCSRng` — matching the mass instance's own unboundedness. -/
noncomputable instance instOrderBotLogS : OrderBot LogS :=
  inferInstanceAs (OrderBot (WithBot ℝ))

instance instCoeRealLogS : Coe ℝ LogS := ⟨fun a => (a : WithBot ℝ)⟩

/-! ### `logEquiv`, built at the `WithBot ℝ` level and cast once -/

/-- `logEquiv`'s forward direction, at the `WithBot ℝ` level: `0 ↦ ⊥`,
`x > 0 ↦ log x`. -/
noncomputable def logToFunWB (x : ℝ≥0) : WithBot ℝ :=
  if x = 0 then ⊥ else ((Real.log (x : ℝ) : ℝ) : WithBot ℝ)

theorem logToFunWB_zero : logToFunWB 0 = ⊥ := if_pos rfl

theorem logToFunWB_of_ne_zero {x : ℝ≥0} (hx : x ≠ 0) :
    logToFunWB x = ((Real.log (x : ℝ) : ℝ) : WithBot ℝ) := if_neg hx

/-- `logEquiv`'s inverse direction, at the `WithBot ℝ` level: `⊥ ↦ 0`,
`a ↦ exp a` (always positive, hence a genuine element of `ℝ≥0`). -/
noncomputable def logInvFunWB : WithBot ℝ → ℝ≥0 :=
  WithBot.recBotCoe (0 : ℝ≥0) (fun a => ⟨Real.exp a, (Real.exp_pos a).le⟩)

theorem logInvFunWB_bot : logInvFunWB ⊥ = 0 := rfl

theorem logInvFunWB_coe (a : ℝ) :
    logInvFunWB (a : WithBot ℝ) = ⟨Real.exp a, (Real.exp_pos a).le⟩ := rfl

theorem logLeftInvWB : Function.LeftInverse logInvFunWB logToFunWB := by
  intro x
  by_cases hx : x = 0
  · subst hx; simp [logToFunWB_zero, logInvFunWB_bot]
  · rw [logToFunWB_of_ne_zero hx, logInvFunWB_coe]
    have hxpos : (0 : ℝ) < (x : ℝ) := by
      rcases lt_or_eq_of_le x.2 with h | h
      · exact h
      · exact absurd (NNReal.coe_eq_zero.mp h.symm) hx
    exact Subtype.ext (Real.exp_log hxpos)

theorem logRightInvWB : Function.RightInverse logInvFunWB logToFunWB := by
  intro a
  induction a using WithBot.recBotCoe with
  | bot => simp [logInvFunWB_bot, logToFunWB_zero]
  | coe a' =>
    rw [logInvFunWB_coe]
    have hne : (⟨Real.exp a', (Real.exp_pos a').le⟩ : ℝ≥0) ≠ 0 := by
      intro h
      exact absurd (congrArg Subtype.val h) (Real.exp_pos a').ne'
    rw [logToFunWB_of_ne_zero hne]
    congr 1
    exact Real.log_exp a'

noncomputable def logEquivWB : ℝ≥0 ≃ WithBot ℝ :=
  ⟨logToFunWB, logInvFunWB, logLeftInvWB, logRightInvWB⟩

/-- Blueprint `lem:log-iso` (log bijection): `x = 0 ↦ -∞`; `x > 0 ↦ log x`;
inverse `-∞ ↦ 0`, `a ↦ exp a` — a single top-level definitional cast of
`logEquivWB` from `WithBot ℝ` to `LogS` (see the module doc comment). -/
noncomputable def logEquiv : ℝ≥0 ≃ LogS := logEquivWB

noncomputable def logToFun : ℝ≥0 → LogS := logToFunWB
noncomputable def logInvFun : LogS → ℝ≥0 := logInvFunWB

theorem logEquiv_apply (x : ℝ≥0) : logEquiv x = logToFun x := rfl
theorem logEquiv_symm_apply (a : LogS) : logEquiv.symm a = logInvFun a := rfl

@[simp] theorem logToFun_zero : logToFun 0 = (⊥ : LogS) := logToFunWB_zero

theorem logToFun_of_ne_zero {x : ℝ≥0} (hx : x ≠ 0) :
    logToFun x = ((Real.log (x : ℝ) : ℝ) : LogS) := logToFunWB_of_ne_zero hx

/-- `logEquiv` is an order isomorphism: `ℝ≥0`'s order corresponds exactly to
`LogS`'s native `WithBot ℝ` order. Used below both to install the
`LatCSRng LogS` monotonicity fields (transporting `ℝ≥0`'s) and, earlier in
spirit, to justify that the transported algebra and the native lattice order
of `def:lattice-semiring`'s log row genuinely agree. -/
theorem logEquiv_le_iff (x y : ℝ≥0) : logEquiv x ≤ logEquiv y ↔ x ≤ y := by
  by_cases hx : x = 0
  · subst hx
    simp only [logEquiv_apply, logToFun_zero]
    exact ⟨fun _ => by positivity, fun _ => bot_le⟩
  by_cases hy : y = 0
  · subst hy
    simp only [logEquiv_apply, logToFun_zero, logToFun_of_ne_zero hx]
    constructor
    · intro h; exact absurd (le_antisymm h bot_le) WithBot.coe_ne_bot
    · intro h; exact absurd (le_antisymm h (by positivity)) hx
  · simp only [logEquiv_apply, logToFun_of_ne_zero hx, logToFun_of_ne_zero hy]
    change ((Real.log (x : ℝ) : ℝ) : WithBot ℝ) ≤ ((Real.log (y : ℝ) : ℝ) : WithBot ℝ) ↔ x ≤ y
    rw [WithBot.coe_le_coe]
    have hxpos : (0 : ℝ) < (x : ℝ) := by
      rcases lt_or_eq_of_le x.2 with h | h
      · exact h
      · exact absurd (NNReal.coe_eq_zero.mp h.symm) hx
    have hypos : (0 : ℝ) < (y : ℝ) := by
      rcases lt_or_eq_of_le y.2 with h | h
      · exact h
      · exact absurd (NNReal.coe_eq_zero.mp h.symm) hy
    rw [Real.log_le_log_iff hxpos hypos, NNReal.coe_le_coe]

/-! ### `lse`, `logMul`: the blueprint's explicit `⊕`/`⊗` formulas -/

/-- `lse`, at the `WithBot ℝ` level: `⊥` absorbed as the identity
(`lse ⊥ b = b`, `lse a ⊥ = a`), two finite reals combining as
`log(exp a + exp b)`. -/
noncomputable def lseWB (a b : WithBot ℝ) : WithBot ℝ :=
  WithBot.recBotCoe b
    (fun a' => WithBot.recBotCoe (a' : WithBot ℝ)
      (fun b' => ((Real.log (Real.exp a' + Real.exp b') : ℝ) : WithBot ℝ)) b)
    a

/-- `logMul`, at the `WithBot ℝ` level: `⊥` absorbing (`logMul ⊥ b = ⊥`,
`logMul a ⊥ = ⊥`), two finite reals combining as ordinary real addition. -/
def logMulWB (a b : WithBot ℝ) : WithBot ℝ :=
  WithBot.recBotCoe (⊥ : WithBot ℝ)
    (fun a' => WithBot.recBotCoe (⊥ : WithBot ℝ) (fun b' => ((a' + b' : ℝ) : WithBot ℝ)) b)
    a

/-- Blueprint `lem:log-iso` (`⊕`, `lse`, log-sum-exp): `⊥` (`= 0`, the
additive identity of `LogS`) is absorbed as the identity of `lse`
(`lse ⊥ b = b`, `lse a ⊥ = a`, matching `log(0 + e^x) = x`); two finite
reals combine as `lse(a, b) := log(e^a + e^b)`. -/
noncomputable def lse : LogS → LogS → LogS := lseWB

/-- Blueprint `lem:log-iso` (`⊗`, log semiring multiplication): `⊗ := +`,
lifted from `ℝ` to `LogS` with `⊥` absorbing (matching the semiring law
`0 ⊗ x = 0` once `0 := ⊥`). -/
def logMul : LogS → LogS → LogS := logMulWB

@[simp] theorem lse_bot_left (b : LogS) : lse ⊥ b = b := rfl
@[simp] theorem lse_bot_right (a : ℝ) : lse (a : LogS) ⊥ = (a : LogS) := rfl

theorem lse_coe_coe (a b : ℝ) :
    lse (a : LogS) (b : LogS) = ((Real.log (Real.exp a + Real.exp b) : ℝ) : LogS) := rfl

@[simp] theorem logMul_bot_left (b : LogS) : logMul ⊥ b = ⊥ := rfl
@[simp] theorem logMul_bot_right (a : ℝ) : logMul (a : LogS) ⊥ = ⊥ := rfl

theorem logMul_coe_coe (a b : ℝ) : logMul (a : LogS) (b : LogS) = ((a + b : ℝ) : LogS) := rfl

/-! ### The mathematical heart: transported `+`/`*` equal `lse`/`logMul` -/

/-- `logEquiv` carries `ℝ≥0`'s `+` to `lse`: `log(x+y) = lse(log x, log y)`,
i.e. `e^{lse(u,v)} = e^u + e^v` unwound at `u := log x`, `v := log y` (the
blueprint's displayed identity for `lem:log-iso`). Proved by case-splitting
on `x = 0`/`y = 0` (where `lse`'s identity-absorption clauses apply
directly) and, in the remaining case, by `Real.exp_log`. -/
theorem logEquiv_add (x y : ℝ≥0) : logEquiv (x + y) = lse (logEquiv x) (logEquiv y) := by
  by_cases hx : x = 0
  · subst hx; simp [logEquiv_apply]
  by_cases hy : y = 0
  · subst hy; simp [logEquiv_apply, logToFun_of_ne_zero hx]
  have hxy : x + y ≠ 0 := by positivity
  rw [logEquiv_apply, logEquiv_apply, logEquiv_apply,
      logToFun_of_ne_zero hx, logToFun_of_ne_zero hy, logToFun_of_ne_zero hxy, lse_coe_coe]
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    rcases lt_or_eq_of_le x.2 with h | h
    · exact h
    · exact absurd (NNReal.coe_eq_zero.mp h.symm) hx
  have hypos : (0 : ℝ) < (y : ℝ) := by
    rcases lt_or_eq_of_le y.2 with h | h
    · exact h
    · exact absurd (NNReal.coe_eq_zero.mp h.symm) hy
  rw [Real.exp_log hxpos, Real.exp_log hypos, NNReal.coe_add]

/-- `logEquiv` carries `ℝ≥0`'s `*` to `logMul`: `log(xy) = log x + log y`
(`Real.log_mul`), the semiring-isomorphism half of `lem:log-iso` for `⊗`. -/
theorem logEquiv_mul (x y : ℝ≥0) : logEquiv (x * y) = logMul (logEquiv x) (logEquiv y) := by
  by_cases hx : x = 0
  · subst hx; simp [logEquiv_apply]
  by_cases hy : y = 0
  · subst hy; simp [logEquiv_apply, logToFun_of_ne_zero hx]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  rw [logEquiv_apply, logEquiv_apply, logEquiv_apply,
      logToFun_of_ne_zero hx, logToFun_of_ne_zero hy, logToFun_of_ne_zero hxy, logMul_coe_coe]
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    rcases lt_or_eq_of_le x.2 with h | h
    · exact h
    · exact absurd (NNReal.coe_eq_zero.mp h.symm) hx
  have hypos : (0 : ℝ) < (y : ℝ) := by
    rcases lt_or_eq_of_le y.2 with h | h
    · exact h
    · exact absurd (NNReal.coe_eq_zero.mp h.symm) hy
  rw [NNReal.coe_mul, Real.log_mul hxpos.ne' hypos.ne']

/-! ### The transported `CommSemiring LogS` -/

/-- Blueprint `def:lattice-semiring` (log instance, semiring structure):
`CommSemiring LogS` transported from `CommSemiring ℝ≥0` along `logEquiv`,
via Mathlib's transfer machinery (`Equiv.commSemiring`,
`Mathlib/Algebra/Ring/TransferInstance.lean`) rather than proved by hand.
Its `+`/`*`/`0`/`1` fields are, by construction, `logEquiv (logEquiv.symm a
op logEquiv.symm b)` — opaque conjugations, not literally `lse`/`logMul`;
`logS_add_eq_lse`/`logS_mul_eq_logMul`/`logS_zero_eq_bot`/`logS_one_eq_zero`
below bridge them to the blueprint's explicit formulas. -/
noncomputable instance instCommSemiringLogS : CommSemiring LogS :=
  Equiv.commSemiring logEquiv.symm

theorem logS_add_def (a b : LogS) : a + b = logEquiv (logEquiv.symm a + logEquiv.symm b) := rfl
theorem logS_mul_def (a b : LogS) : a * b = logEquiv (logEquiv.symm a * logEquiv.symm b) := rfl
theorem logS_zero_def : (0 : LogS) = logEquiv 0 := rfl
theorem logS_one_def : (1 : LogS) = logEquiv 1 := rfl

/-- The transported `+` equals `lse` — the mathematical heart of
`lem:log-iso`'s `⊕` clause. -/
theorem logS_add_eq_lse (a b : LogS) : a + b = lse a b := by
  rw [logS_add_def, logEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The transported `*` equals `logMul` — the mathematical heart of
`lem:log-iso`'s `⊗` clause. -/
theorem logS_mul_eq_logMul (a b : LogS) : a * b = logMul a b := by
  rw [logS_mul_def, logEquiv_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp] theorem logS_zero_eq_bot : (0 : LogS) = ⊥ := by
  rw [logS_zero_def, logEquiv_apply, logToFun_zero]

@[simp] theorem logS_one_eq_zero : (1 : LogS) = ((0 : ℝ) : LogS) := by
  rw [logS_one_def, logEquiv_apply, logToFun_of_ne_zero one_ne_zero, NNReal.coe_one,
    Real.log_one]

theorem logEquiv_zero : logEquiv 0 = (0 : LogS) := by
  rw [logEquiv_apply, logToFun_zero, ← logS_zero_eq_bot]

theorem logEquiv_one : logEquiv 1 = (1 : LogS) := by
  rw [logEquiv_apply, logToFun_of_ne_zero one_ne_zero, NNReal.coe_one, Real.log_one,
    ← logS_one_eq_zero]

/-- `logEquiv` respects `+` using `LogS`'s own `+` (not `lse` bare) — the
`map_add'` obligation for `logRingEquiv` below. -/
theorem logEquiv_map_add (x y : ℝ≥0) : logEquiv (x + y) = logEquiv x + logEquiv y := by
  rw [logEquiv_add, ← logS_add_eq_lse]

/-- `logEquiv` respects `*` using `LogS`'s own `*` — the `map_mul'`
obligation for `logRingEquiv` below. -/
theorem logEquiv_map_mul (x y : ℝ≥0) : logEquiv (x * y) = logEquiv x * logEquiv y := by
  rw [logEquiv_mul, ← logS_mul_eq_logMul]

/-- Blueprint `lem:log-iso` (Log isomorphism): `log : (ℝ≥0, +, ·) →
(LogS, lse, +)` is a semiring isomorphism, packaged as a bundled
`RingEquiv`. -/
noncomputable def logRingEquiv : ℝ≥0 ≃+* LogS :=
  { logEquiv with
    map_add' := logEquiv_map_add
    map_mul' := logEquiv_map_mul }

theorem logRingEquiv_apply (x : ℝ≥0) : logRingEquiv x = logEquiv x := rfl

/-! ### `LatCSRng LogS`, completing `def:lattice-semiring` -/

theorem logS_add_le_add_left {a b : LogS} (h : a ≤ b) (c : LogS) : c + a ≤ c + b := by
  rw [logS_add_eq_lse, logS_add_eq_lse, ← logEquiv.apply_symm_apply c,
    ← logEquiv.apply_symm_apply a, ← logEquiv.apply_symm_apply b, ← logEquiv_add, ← logEquiv_add,
    logEquiv_le_iff]
  have h' : logEquiv.symm a ≤ logEquiv.symm b := by
    rwa [← logEquiv_le_iff, logEquiv.apply_symm_apply, logEquiv.apply_symm_apply]
  gcongr

theorem logS_add_le_add_right {a b : LogS} (h : a ≤ b) (c : LogS) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]; exact logS_add_le_add_left h c

theorem logS_mul_le_mul_left {a b : LogS} (h : a ≤ b) (c : LogS) : c * a ≤ c * b := by
  rw [logS_mul_eq_logMul, logS_mul_eq_logMul, ← logEquiv.apply_symm_apply c,
    ← logEquiv.apply_symm_apply a, ← logEquiv.apply_symm_apply b, ← logEquiv_mul, ← logEquiv_mul,
    logEquiv_le_iff]
  have h' : logEquiv.symm a ≤ logEquiv.symm b := by
    rwa [← logEquiv_le_iff, logEquiv.apply_symm_apply, logEquiv.apply_symm_apply]
  gcongr

theorem logS_mul_le_mul_right {a b : LogS} (h : a ≤ b) (c : LogS) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c]; exact logS_mul_le_mul_left h c

/-- Blueprint `def:lattice-semiring` (log instance): completes the log row
of the definition — `LogS` is a commutative lattice-semiring, its `+`/`*`
(via `logS_add_eq_lse`/`logS_mul_eq_logMul`, i.e. `lse`/`logMul`) each
monotone with respect to the native `WithBot ℝ` order, transported from
`ℝ≥0`'s own monotonicity along the order isomorphism `logEquiv_le_iff`.
Unbounded (only `LatCSRng`, not `BLatCSRng`), matching the mass instance. -/
noncomputable instance instLatCSRngLogS : LatCSRng LogS where
  add_le_add_left h c := logS_add_le_add_left h c
  add_le_add_right h c := logS_add_le_add_right h c
  mul_le_mul_left h c := logS_mul_le_mul_left h c
  mul_le_mul_right h c := logS_mul_le_mul_right h c
  mul_comm := mul_comm

/-! ### The monad isomorphism `MS ℝ≥0 X ≃ MS LogS X` -/

variable {X Y : Type*}

/-- Blueprint `lem:log-iso` (monad transport, forward direction): apply
`logEquiv` to every weight of an `MS ℝ≥0 X`-value. -/
noncomputable def toLogTens (ρ : MS ℝ≥0 X) : MS LogS X :=
  Finsupp.mapRange logEquiv logEquiv_zero ρ

/-- Blueprint `lem:log-iso` (monad transport, inverse direction): apply
`logEquiv.symm` to every weight of an `MS LogS X`-value. -/
noncomputable def ofLogTens (a : MS LogS X) : MS ℝ≥0 X :=
  Finsupp.mapRange logEquiv.symm (by rw [← logEquiv_zero, Equiv.symm_apply_apply]) a

@[simp] theorem toLogTens_apply (ρ : MS ℝ≥0 X) (x : X) : toLogTens ρ x = logEquiv (ρ x) :=
  Finsupp.mapRange_apply

@[simp] theorem ofLogTens_apply (a : MS LogS X) (x : X) : ofLogTens a x = logEquiv.symm (a x) :=
  Finsupp.mapRange_apply

theorem ofLogTens_toLogTens (ρ : MS ℝ≥0 X) : ofLogTens (toLogTens ρ) = ρ := by
  ext x; simp

theorem toLogTens_ofLogTens (a : MS LogS X) : toLogTens (ofLogTens a) = a := by
  ext x; simp

/-- Blueprint `lem:log-iso` (`ret` commutes with the transport): applying
`logEquiv` to a point mass is again a point mass, since `logEquiv 1 = 1`. -/
theorem toLogTens_ret (x : X) : toLogTens (ret x : MS ℝ≥0 X) = ret x := by
  classical
  ext y
  rw [toLogTens_apply]
  unfold ret
  rw [Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h
  · exact logEquiv_one
  · exact logEquiv_zero

/-- Blueprint `lem:log-iso` (`bind` commutes with the transport): a
`RingEquiv`-respects-sums-and-products computation over `Finsupp.sum` — for
each output value `y`, both sides unfold (`bind_apply`) to a `Finsupp.sum`
over `ℝ≥0`/`LogS` matched up by `logRingEquiv`'s ring-homomorphism
properties (`map_add`, `map_mul`), summed via the generic `map_sum`. -/
theorem toLogTens_bind (ρ : MS ℝ≥0 X) (k : X → MS ℝ≥0 Y) :
    toLogTens (bind ρ k) = bind (toLogTens ρ) (fun x => toLogTens (k x)) := by
  ext y
  rw [toLogTens_apply, bind_apply, bind_apply,
      show toLogTens ρ = Finsupp.mapRange logEquiv logEquiv_zero ρ from rfl,
      Finsupp.sum_mapRange_index (fun x => by rw [zero_mul])]
  simp_rw [toLogTens_apply]
  change logRingEquiv (ρ.sum fun x w => w * k x y)
      = ρ.sum fun x w => logRingEquiv w * logRingEquiv (k x y)
  rw [show (ρ.sum fun x w => w * k x y) = ∑ x ∈ ρ.support, ρ x * k x y from rfl,
      map_sum logRingEquiv (fun x => ρ x * k x y) ρ.support]
  change (∑ x ∈ ρ.support, logRingEquiv (ρ x * k x y))
      = ∑ x ∈ ρ.support, logRingEquiv (ρ x) * logRingEquiv (k x y)
  exact Finset.sum_congr rfl fun x _ => map_mul logRingEquiv (ρ x) (k x y)

/-- Blueprint `lem:log-iso` (monad isomorphism): `logEquiv` transported
pointwise (`toLogTens`/`ofLogTens`) to an isomorphism of monads
`MS ℝ≥0 X ≃ MS LogS X`, natural in the monad operations
(`toLogTens_ret`/`toLogTens_bind` above): `\Tmon \cong \LTmon`. -/
noncomputable def logTensEquiv (X : Type*) : MS ℝ≥0 X ≃ MS LogS X where
  toFun := toLogTens
  invFun := ofLogTens
  left_inv := ofLogTens_toLogTens
  right_inv := toLogTens_ofLogTens

/-- Blueprint `abbr:log-tensor-monad` (Log-tensor monad, `LTmon`): the
log-tensor monad instantiation `MS LogS`, available now that `LogS` carries
a semiring structure (`instCommSemiringLogS`, transported along
`logRingEquiv`). -/
abbrev LogTens (X : Type*) := MS LogS X

end NeSyCat
