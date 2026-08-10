/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.SemiringMonads.LatticeSemiring
import NeSyCat.LogicalLayer.TruthStructures.Chain

/-!
# The t-norm family: `TNorm`, `TRow`, and the Gödel/Viterbi/Łukasiewicz rows

Blueprint items `def:tnorm`, `inst:tnorm-row`, `lem:godel-unique-idempotent`,
`lem:product-not-distrib-psum`, `inst:godel-latcsrng`, `inst:viterbi-latcsrng`,
`inst:luk-latcsrng` (`blueprint/src/content.tex`, §"Semiring weight
monads", the t-norm family placed after the three running rows). Source:
the user's own `new.tex` §"Parameterized Monads" table, generalized
2026-08-09 ("isn't every t-norm algebra an instance of this?"); the
definition of a t-norm itself is standard fuzzy-logic apparatus
(Hájek, *Metamathematics of Fuzzy Logic*, 1998).

## The carrier

`TRow τ` is a fresh type synonym for `unitInterval`, one per t-norm `τ`
(the "OrderDual/Lex pattern" already used for `BoolW`/`LogS`: a plain
`def`, not `abbrev`, so its own `Add`/`Mul` instances never compete with
`unitInterval`'s or with each other's, no diamond between rows). `⊕` is
always `max` (the lattice join, literally the same operation, since `Add`
is *defined* as `⊔`); `⊗` is the t-norm's own operation `τ.op`. The three
named instances (`GodelS`, `ViterbiS`, `LukS`) are `abbrev`s for `TRow`
applied to a fixed t-norm.

## The proof kernel

Every t-norm satisfies `op a b ≤ min a b` (from monotonicity and the unit
law alone) and annihilates `⊥` (same route). Distributivity over `max`
reuses `NeSyCat.chain_binop_sup_right`/`chain_binop_sup_left`
(`thm:chain-lin`(i)'s raw chain lemmas, `Chain.lean`) directly: a t-norm's
own monotonicity in each argument is exactly that lemma's hypothesis, and
`unitInterval` is a chain, so no new distributivity argument is needed
here beyond assembling the pieces.

## `lem:godel-unique-idempotent`

Idempotence (`op a a = a`) pins a t-norm down to `min` in two lines:
`min a b = op (min a b) (min a b) ≤ op a b ≤ min a b`, the middle step by
monotonicity (`min a b ≤ a` and `≤ b` applied to each slot of the
idempotent instance) and the outer step by `op ≤ min` itself.

## `lem:product-not-distrib-psum`

The literature question ("does *every* t-norm distribute over *every*
t-conorm other than `max`?") is false in general: the drastic t-norm
distributes over the probabilistic sum `pSum` everywhere (checked by hand,
not formalized here — out of scope), so no blanket `∀ τ` statement holds
at this generality. What is proved here is the concrete instance the
library needs: the product t-norm does **not** distribute over `pSum`,
stated genuinely in t-norm/t-conorm vocabulary (`viterbiTNorm.op` against
the `unitInterval`-wrapped `pSumU`, not a bare restatement of
`NeSyCat.prob_not_semiring`'s own type), and derived from that lemma's
witness by unwrapping both sides' coordinates. Every t-norm *does*
distribute over `max` (`inst:tnorm-row` below), so `max` is at least a
safe choice where the product t-norm is not.
-/

namespace NeSyCat

/-- Blueprint `def:tnorm` (T-norm): a **t-norm** is a binary operation
`⊗` on `[0,1]` that is commutative, associative, monotone in each
argument, and has two-sided unit `1` (Hájek, *Metamathematics of Fuzzy
Logic*, 1998). -/
structure TNorm where
  /-- The t-norm's operation `⊗`. -/
  op : unitInterval → unitInterval → unitInterval
  /-- `⊗` is commutative. -/
  comm : ∀ a b, op a b = op b a
  /-- `⊗` is associative. -/
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  /-- `⊗` is monotone in its left argument. -/
  mono_left : ∀ a b c, a ≤ b → op a c ≤ op b c
  /-- `1` is a left unit for `⊗`. -/
  one_op : ∀ a, op 1 a = a

namespace TNorm

variable (τ : TNorm)

/-- `⊗` is monotone in its right argument (from `mono_left` and `comm`). -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem mono_right {a b : unitInterval} (h : a ≤ b) (c : unitInterval) :
    τ.op c a ≤ τ.op c b := by
  rw [τ.comm c a, τ.comm c b]
  exact τ.mono_left a b c h

/-- `1` is also a right unit for `⊗` (from `one_op` and `comm`). -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem op_one (a : unitInterval) : τ.op a 1 = a := by
  rw [τ.comm a 1]
  exact τ.one_op a

/-- Every t-norm is bounded above by `min`, on the right: `op a b ≤ b`
(`op a b ≤ op 1 b = b`, monotonicity plus the unit law). -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem le_right (a b : unitInterval) : τ.op a b ≤ b := by
  have h := τ.mono_left a 1 b unitInterval.le_one'
  rwa [τ.one_op] at h

/-- Every t-norm is bounded above by `min`, on the left: `op a b ≤ a`
(dual to `le_right`, via `comm`). -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem le_left (a b : unitInterval) : τ.op a b ≤ a := by
  rw [τ.comm a b]
  exact τ.le_right b a

/-- Every t-norm is bounded above by `min` (combining `le_left`/`le_right`):
`op a b ≤ min a b`. -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem le_min (a b : unitInterval) : τ.op a b ≤ min a b :=
  _root_.le_min (τ.le_left a b) (τ.le_right a b)

/-- A t-norm annihilates `⊥` on the right: `op a ⊥ = ⊥`
(`op a ⊥ ≤ op 1 ⊥ = ⊥` by monotonicity and the unit law, and `⊥` is a
lower bound). -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem op_bot (a : unitInterval) : τ.op a ⊥ = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h := τ.mono_left a 1 ⊥ unitInterval.le_one'
  rwa [τ.one_op] at h

/-- A t-norm annihilates `⊥` on the left (dual to `op_bot`, via `comm`). -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem bot_op (a : unitInterval) : τ.op ⊥ a = ⊥ := by
  rw [τ.comm]
  exact τ.op_bot a

/-- A t-norm distributes over `max`, right argument: `op a (b ⊔ c) =
op a b ⊔ op a c`. Reuses `chain_binop_sup_right` (`thm:chain-lin`(i)) with
`mono_right` as its monotonicity hypothesis: no fresh distributivity
argument is needed, only that `unitInterval` is a chain. -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem op_sup_right (a b c : unitInterval) :
    τ.op a (b ⊔ c) = τ.op a b ⊔ τ.op a c :=
  chain_binop_sup_right τ.op τ.mono_right a b c

/-- A t-norm distributes over `max`, left argument: `op (a ⊔ b) c =
op a c ⊔ op b c`. Reuses `chain_binop_sup_left` with `mono_left`. -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem sup_op_left (a b c : unitInterval) :
    τ.op (a ⊔ b) c = τ.op a c ⊔ τ.op b c :=
  chain_binop_sup_left τ.op (fun h r => τ.mono_left _ _ r h) a b c

end TNorm

-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
set_option linter.unusedVariables false in
/-- Blueprint `inst:tnorm-row` (T-row carrier): a fresh type synonym for
`unitInterval`, one per t-norm `τ`, carrying `⊕ := max` and `⊗ := τ.op`.
The "OrderDual/Lex pattern" already used for `BoolW`/`LogS`: a plain
`def`, not `abbrev`, so instances at different `τ` never compete. -/
@[blueprint_internal]
def TRow (τ : TNorm) : Type := unitInterval

namespace TRow

variable {τ : TNorm}

-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
instance : Lattice (TRow τ) := inferInstanceAs (Lattice unitInterval)

-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
instance : BoundedOrder (TRow τ) := inferInstanceAs (BoundedOrder unitInterval)

-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
instance : Zero (TRow τ) := ⟨(⊥ : unitInterval)⟩

-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
instance : One (TRow τ) := ⟨(1 : unitInterval)⟩

-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
instance : Add (TRow τ) := ⟨(· ⊔ ·)⟩

-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
instance : Mul (TRow τ) := ⟨τ.op⟩

/-- `TRow τ`'s `0` is exactly its `⊥`: the semiring's additive unit is the
lattice bottom, one half of `UnitBounds` holding for every t-norm row. -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem zero_eq_bot : (0 : TRow τ) = ⊥ := rfl

/-- `TRow τ`'s `1` is exactly its `⊤`: the semiring's multiplicative unit
is the lattice top, the other half of `UnitBounds`. -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
theorem one_eq_top : (1 : TRow τ) = ⊤ := rfl

/-- The `CommSemiring` structure on `TRow τ`: `⊕ := max` (associative,
commutative, unit `⊥`, from the ambient lattice) and `⊗ := τ.op`
(associative, commutative, unit `1`, annihilating `⊥`, distributing over
`max`, from the `TNorm` fields and the derived lemmas above). -/
-- (A1 bijection-law companion of `TRow.instBLatCSRng`, content.tex inst:tnorm-row)
@[blueprint_internal]
noncomputable instance instCommSemiring : CommSemiring (TRow τ) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  left_distrib a b c := τ.op_sup_right a b c
  right_distrib a b c := τ.sup_op_left a b c
  zero_mul a := τ.bot_op a
  mul_zero a := τ.op_bot a
  mul_assoc := τ.assoc
  one_mul := τ.one_op
  mul_one := τ.op_one
  mul_comm := τ.comm
  nsmul := nsmulRec

/-- Blueprint `inst:tnorm-row` (T-norm row): every t-norm `τ` gives
`(TRow τ, max, τ.op)` a bounded commutative lattice-semiring, `⊕ := max`
with unit `⊥`, `⊗ := τ.op` with unit `⊤` (`zero_eq_bot`/`one_eq_top`
above): `UnitBounds` holds for every t-norm row. Both monotonicity
directions for `⊕` are the standard lattice facts (`sup_le_sup_left/right`);
for `⊗` they are `TNorm.mono_right`/`TNorm.mono_left`. -/
noncomputable instance instBLatCSRng : BLatCSRng (TRow τ) where
  add_le_add_left h c := sup_le_sup_left h c
  add_le_add_right h c := sup_le_sup_right h c
  mul_le_mul_left h c := τ.mono_right h c
  mul_le_mul_right h c := τ.mono_left _ _ c h
  mul_comm := τ.comm

end TRow

/-- Blueprint `lem:godel-unique-idempotent` (Idempotent t-norms are the
Gödel t-norm): if a t-norm is idempotent (`op a a = a` for every `a`),
then it is `min`. -/
theorem TNorm.eq_min_of_idempotent (τ : TNorm) (h : ∀ a, τ.op a a = a)
    (a b : unitInterval) : τ.op a b = min a b := by
  refine le_antisymm (τ.le_min a b) ?_
  calc min a b = τ.op (min a b) (min a b) := (h _).symm
    _ ≤ τ.op a (min a b) := τ.mono_left _ _ _ (min_le_left a b)
    _ ≤ τ.op a b := τ.mono_right (min_le_right a b) a

/-- Blueprint `inst:godel-latcsrng` (Gödel t-norm): `⊗ := min`. -/
def godelTNorm : TNorm where
  op a b := min a b
  comm := min_comm
  assoc := min_assoc
  mono_left _ _ _ h := by gcongr
  one_op a := min_eq_right unitInterval.le_one'

/-- Blueprint `inst:godel-latcsrng` (Gödel row): `GodelS := TRow godelTNorm`,
`⊕ = max`, `⊗ = min`; `BLatCSRng GodelS` follows from `TRow.instBLatCSRng`
at `τ := godelTNorm`, with no further work. -/
-- (A1 bijection-law companion of `godelTNorm`, content.tex inst:godel-latcsrng)
@[blueprint_internal]
abbrev GodelS := TRow godelTNorm

/-- Blueprint `inst:viterbi-latcsrng` (product/Viterbi t-norm): `⊗ := a·b`,
the MPE (max-times) semiring's multiplication. -/
def viterbiTNorm : TNorm where
  op a b := a * b
  comm := mul_comm
  assoc := mul_assoc
  mono_left _ _ c h := mul_le_mul_of_nonneg_right h c.2.1
  one_op := one_mul

/-- Blueprint `inst:viterbi-latcsrng` (product/Viterbi row): `ViterbiS :=
TRow viterbiTNorm`, `⊕ = max`, `⊗ = ·`; `BLatCSRng ViterbiS` follows from
`TRow.instBLatCSRng` at `τ := viterbiTNorm`. -/
-- (A1 bijection-law companion of `viterbiTNorm`, content.tex inst:viterbi-latcsrng)
@[blueprint_internal]
abbrev ViterbiS := TRow viterbiTNorm

/-! ### The Łukasiewicz t-norm

`op a b := max 0 (a + b - 1)`, the truncated sum. Associativity is the one
genuinely nontrivial law; it is proved once at the real-number level
(`lukOp_assoc_real`, a four-way case split on whether `x+y ≥ 1` and whether
`y+z ≥ 1`) and then lifted to the subtype. -/

/-- `lukOp`'s real-number formula lands back in `[0,1]`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem lukOp_mem (a b : unitInterval) :
    max 0 ((a : ℝ) + b - 1) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (by linarith [a.2.2, b.2.2])⟩

/-- Blueprint `inst:luk-latcsrng` (Łukasiewicz t-norm, underlying
operation): `⊗ := max(0, a+b-1)`, the truncated sum. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
def lukOp (a b : unitInterval) : unitInterval := ⟨max 0 ((a : ℝ) + b - 1), lukOp_mem a b⟩

-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem lukOp_comm (a b : unitInterval) : lukOp a b = lukOp b a := by
  apply Subtype.ext
  change max 0 ((a : ℝ) + b - 1) = max 0 ((b : ℝ) + a - 1)
  rw [add_comm]

/-- The real-number heart of `lukOp`'s associativity: a four-way case
split on whether `x+y ≥ 1` and whether `y+z ≥ 1`. -/
-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem lukOp_assoc_real {x y z : ℝ} (hx1 : x ≤ 1) (hz1 : z ≤ 1) :
    max 0 (max 0 (x + y - 1) + z - 1) = max 0 (x + max 0 (y + z - 1) - 1) := by
  rcases le_total 1 (x + y) with hxy | hxy
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ x + y - 1)]
    rcases le_total 1 (y + z) with hyz | hyz
    · rw [max_eq_right (by linarith : (0 : ℝ) ≤ y + z - 1)]
      congr 1
      ring
    · rw [max_eq_left (by linarith : y + z - 1 ≤ 0)]
      rw [max_eq_left (by linarith : x + y - 1 + z - 1 ≤ 0)]
      rw [max_eq_left (by linarith : x + 0 - 1 ≤ 0)]
  · rw [max_eq_left (by linarith : x + y - 1 ≤ 0)]
    rcases le_total 1 (y + z) with hyz | hyz
    · rw [max_eq_right (by linarith : (0 : ℝ) ≤ y + z - 1)]
      rw [max_eq_left (by linarith : (0 : ℝ) + z - 1 ≤ 0)]
      rw [max_eq_left (by linarith : x + (y + z - 1) - 1 ≤ 0)]
    · rw [max_eq_left (by linarith : y + z - 1 ≤ 0)]
      rw [max_eq_left (by linarith : (0 : ℝ) + z - 1 ≤ 0)]
      rw [max_eq_left (by linarith : x + 0 - 1 ≤ 0)]

-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem lukOp_assoc (a b c : unitInterval) : lukOp (lukOp a b) c = lukOp a (lukOp b c) := by
  apply Subtype.ext
  change max 0 (max 0 ((a : ℝ) + b - 1) + c - 1) = max 0 ((a : ℝ) + max 0 ((b : ℝ) + c - 1) - 1)
  exact lukOp_assoc_real a.2.2 c.2.2

-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem lukOp_mono_left {a b : unitInterval} (h : a ≤ b) (c : unitInterval) :
    lukOp a c ≤ lukOp b c := by
  change max 0 ((a : ℝ) + c - 1) ≤ max 0 ((b : ℝ) + c - 1)
  have : (a : ℝ) ≤ b := h
  gcongr

-- (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
@[blueprint_internal]
theorem lukOp_one (a : unitInterval) : lukOp 1 a = a := by
  apply Subtype.ext
  change max 0 ((1 : ℝ) + a - 1) = a
  rw [show (1 : ℝ) + a - 1 = a by ring]
  exact max_eq_right a.2.1

/-- Blueprint `inst:luk-latcsrng` (Łukasiewicz t-norm): `⊗ := max(0,a+b-1)`,
the truncated sum. -/
def lukTNorm : TNorm where
  op := lukOp
  comm := lukOp_comm
  assoc := lukOp_assoc
  mono_left _ _ c h := lukOp_mono_left h c
  one_op := lukOp_one

/-- Blueprint `inst:luk-latcsrng` (Łukasiewicz row): `LukS := TRow
lukTNorm`, `⊕ = max`, `⊗ = max(0,a+b-1)`; `BLatCSRng LukS` follows from
`TRow.instBLatCSRng` at `τ := lukTNorm`. -/
-- (A1 bijection-law companion of `lukTNorm`, content.tex inst:luk-latcsrng)
@[blueprint_internal]
abbrev LukS := TRow lukTNorm

/-- `viterbiTNorm.op` unfolds to ordinary multiplication (its own
definition), bridging `product_not_distrib_pSum`'s t-norm-vocabulary
statement to `prob_not_semiring`'s real-number witness. -/
-- (A1 bijection-law companion of `product_not_distrib_pSum`,
-- content.tex lem:product-not-distrib-psum)
@[blueprint_internal]
theorem viterbiTNorm_op (p q : unitInterval) : viterbiTNorm.op p q = p * q := rfl

/-- The probabilistic sum `pSum` stays in `[0,1]` given inputs in `[0,1]`:
`pSum p q = 1-(1-p)(1-q)`, a product of two `[0,1]`-valued factors
subtracted from `1`. -/
-- (A1 bijection-law companion of `product_not_distrib_pSum`,
-- content.tex lem:product-not-distrib-psum)
@[blueprint_internal]
theorem pSum_mem (p q : unitInterval) : pSum (p : ℝ) (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  unfold pSum
  constructor
  · nlinarith [p.2.1, p.2.2, q.2.1, q.2.2]
  · nlinarith [p.2.1, p.2.2, q.2.1, q.2.2]

/-- `pSum`, wrapped to `unitInterval → unitInterval → unitInterval`
(`pSum_mem` supplies the membership proof), the `unitInterval`-native
t-conorm `lem:product-not-distrib-psum` states the product t-norm against. -/
-- (A1 bijection-law companion of `product_not_distrib_pSum`,
-- content.tex lem:product-not-distrib-psum)
@[blueprint_internal]
def pSumU (p q : unitInterval) : unitInterval := ⟨pSum p q, pSum_mem p q⟩

/-- Blueprint `lem:product-not-distrib-psum` (the product t-norm does not
distribute over the probabilistic sum): stated genuinely in t-norm/t-conorm
vocabulary, about `viterbiTNorm.op` and the `unitInterval`-wrapped `pSumU`,
not a bare restatement of `prob_not_semiring`'s own type. Derived from
`prob_not_semiring`'s witness by transporting it into `unitInterval` and
unwrapping both sides' coordinates back down. Every t-norm distributes
over `max` (`TRow.instBLatCSRng`); this shows `max` is not replaceable by
just any t-conorm, at least not by `pSum`, for the product t-norm. -/
theorem product_not_distrib_pSum :
    ∃ p q r : unitInterval,
      viterbiTNorm.op p (pSumU q r) ≠ pSumU (viterbiTNorm.op p q) (viterbiTNorm.op p r) := by
  obtain ⟨p, hp, q, hq, r, hr, hne⟩ := prob_not_semiring
  refine ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, fun heq => hne ?_⟩
  have hval := congrArg Subtype.val heq
  simpa [viterbiTNorm_op, pSumU] using hval

end NeSyCat
