/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.GrammaticalLayer.QuantifierNestable
import NeSyCat.CategoricalLayer.SemiringMonads.LogIso

/-!
# Quantifier columns are nestable (C3-B4b, marked at C3-CMP)

Blueprint item `lem:quantifier-columns-nestable`
(`blueprint/src/content.tex`, §"Grammatical layer"): the four running
interpretation families (max, min, the Σ-Π pair, and their log twins)
are symmetric and nestable in the sense of the hypotheses of
`lem:quantifier-nestable`.

**Scope.** The predicates are EXACTLY `QuantifierNestable.lean`'s
`Nestable`/`SymmetricFamily` (the Lean form of
`lem:quantifier-nestable`'s hypotheses), instantiated at the category
of sets — the base category of the running interpretations — where an
`n`-ary reduction family is the fold `foldFam op e` of a binary
operation over the tensor power. `foldFam_nestable` and
`foldFam_symmetric` prove the env's proof sentence generically:
nestability from associativity (with the fold's own seed-unit laws),
symmetry from commutativity (adjacent transpositions).

**C3-ADJ (user ruling): one carrier for all four.** At C3-B4b, `min`
needed a top element the unbounded mass carrier `ℝ≥0` lacks, so it was
instantiated on `unitInterval` while `max`/`Σ`/`Π` stayed on `ℝ≥0` — a
disclosed mixed-carrier proof, kept unmarked. The mass completion
`ℝ≥0∞` (`NeSyCat/LogicalLayer/Completions/MassCompletion.lean`, C3-CMP)
supplies exactly the missing top (`⊤ = ∞`, `min`'s own seed unit), so
all FOUR running families now instantiate on the SAME carrier `ℝ≥0∞`:
`min`'s seed is `⊤` in place of `unitInterval`'s `1`, everything else
unchanged. The log twins `lse`/`+` on `LogS` are untouched (they never
needed a top; their own seeds `0`/`1` were always in-carrier) --
`lem:log-iso`'s transported `CommSemiring` makes `lse`/`logMul`
literally `LogS`'s own `+`/`*`, so the twins inherit both properties
from the transported semiring laws, the env's own "along the log
isomorphism" argument, matching the blueprint's own two-clause shape
(the four running families on one carrier; the log twins by transport).
-/

open CategoryTheory MonoidalCategory

namespace NeSyCat

variable {M : Type} (op : M → M → M) (e : M)

/-- Toward `lem:quantifier-columns-nestable`: the `n`-ary reduction
family of a binary operation with seed `e`, as morphisms on tensor
powers in the category of sets. -/
@[blueprint_internal] -- toward lem:quantifier-columns-nestable: the
-- fold family of a binary reduction
def foldFam : ∀ n, tensorPow (C := Type) M n ⟶ M
  | 0 => TypeCat.ofHom fun _ => e
  | n + 1 => TypeCat.ofHom fun t : tensorPow (C := Type) M n ⊗ M =>
      op (foldFam n t.1) t.2

variable {op e}

/-- Toward `lem:quantifier-columns-nestable`: a fold splits across a
tensor-power split, by associativity and the seed-unit laws. -/
@[blueprint_internal] -- toward lem:quantifier-columns-nestable: fold
-- against the addition split
theorem foldFam_add (hassoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hre : ∀ x, op x e = x) : ∀ (a b : ℕ) (t : tensorPow (C := Type) M (a + b)),
    foldFam op e (a + b) t =
      op (foldFam op e a ((tensorPowAddIso M a b).hom t).1)
        (foldFam op e b ((tensorPowAddIso M a b).hom t).2)
  | a, 0, t => (hre _).symm
  | a, b + 1, t => by
    change op (foldFam op e (a + b) t.1) t.2 =
      op (foldFam op e a ((tensorPowAddIso M a b).hom t.1).1)
        (op (foldFam op e b ((tensorPowAddIso M a b).hom t.1).2) t.2)
    rw [foldFam_add hassoc hre a b t.1, hassoc]

/-- Toward `lem:quantifier-columns-nestable`, the env's NESTABILITY
sentence: a reduction over `mn` inputs decomposes into `m` block
reductions of size `n` followed by a reduction over the `m` block
results — by associativity (and the fold's seed-unit laws). -/
@[blueprint_internal] -- toward lem:quantifier-columns-nestable:
-- nestability of a fold family, by associativity
theorem foldFam_nestable (hassoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hre : ∀ x, op x e = x) :
    Nestable (foldFam op e) := by
  intro m n
  ext t
  induction m with
  | zero => rfl
  | succ m ih =>
    change foldFam op e (n * m + n) t =
      op (foldFam op e m (tensorFinHom m (fun _ => foldFam op e n)
          ((tensorPowMulIso M n m).hom ((tensorPowAddIso M (n * m) n).hom t).1)))
        (foldFam op e n ((tensorPowAddIso M (n * m) n).hom t).2)
    rw [foldFam_add hassoc hre (n * m) n t]
    congr 1
    exact ih ((tensorPowAddIso M (n * m) n).hom t).1

/-- Toward `lem:quantifier-columns-nestable`, the env's SYMMETRY
sentence: the reduction is invariant under any permutation of its
inputs, via the generating adjacent transpositions — by commutativity
and associativity. -/
@[blueprint_internal] -- toward lem:quantifier-columns-nestable:
-- symmetry of a fold family, by commutativity
theorem foldFam_symmetric (hassoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hcomm : ∀ x y, op x y = op y x) :
    SymmetricFamily (foldFam op e) := by
  intro a b
  ext t
  induction b with
  | zero =>
    change op (op (foldFam op e a t.1.1) t.2) t.1.2 =
      op (op (foldFam op e a t.1.1) t.1.2) t.2
    rw [hassoc, hassoc, hcomm t.2 t.1.2]
  | succ b ih =>
    change op (foldFam op e ((a + 2) + b) (swapPow M a b t.1)) t.2 =
      op (foldFam op e ((a + 2) + b) t.1) t.2
    exact congrArg (fun x => op x t.2) (ih t.1)

open scoped NNReal ENNReal in
/-- Blueprint `lem:quantifier-columns-nestable`, the six concrete
columns: max, min, Σ (`+`), Π (`·`) ALL on the mass completion `ℝ≥0∞`
(C3-ADJ: `min`'s seed `⊤` is exactly the top element the completion
supplies, matching `max`/`Σ`/`Π`'s own carrier — one carrier for all
four running families); the log twins on `LogS`, whose transported
semiring operations ARE `lse` and `logMul` (`lem:log-iso`,
`logS_add_eq_lse`/`logS_mul_eq_logMul`), so the twins inherit both
properties along the log isomorphism, the env's own argument. Every
seed is the operation's genuine unit, so each fold family is the
intended `n`-ary reduction. -/
theorem quantifier_columns_nestable :
    (Nestable (foldFam max (0 : ℝ≥0∞)) ∧
        SymmetricFamily (foldFam max (0 : ℝ≥0∞))) ∧
      (Nestable (foldFam min (⊤ : ℝ≥0∞)) ∧
        SymmetricFamily (foldFam min (⊤ : ℝ≥0∞))) ∧
      (Nestable (foldFam (· + ·) (0 : ℝ≥0∞)) ∧
        SymmetricFamily (foldFam (· + ·) (0 : ℝ≥0∞))) ∧
      (Nestable (foldFam (· * ·) (1 : ℝ≥0∞)) ∧
        SymmetricFamily (foldFam (· * ·) (1 : ℝ≥0∞))) ∧
      (Nestable (foldFam (· + ·) (0 : LogS)) ∧
        SymmetricFamily (foldFam (· + ·) (0 : LogS))) ∧
      (Nestable (foldFam (· * ·) (1 : LogS)) ∧
        SymmetricFamily (foldFam (· * ·) (1 : LogS))) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact foldFam_nestable (fun x y z => max_assoc x y z)
      (fun _ => max_eq_left zero_le)
  · exact foldFam_symmetric (fun x y z => max_assoc x y z)
      (fun x y => max_comm x y)
  · exact foldFam_nestable (fun x y z => min_assoc x y z)
      (fun _ => min_eq_left le_top)
  · exact foldFam_symmetric (fun x y z => min_assoc x y z)
      (fun x y => min_comm x y)
  · exact foldFam_nestable (fun x y z => add_assoc x y z)
      (fun x => add_zero x)
  · exact foldFam_symmetric (fun x y z => add_assoc x y z)
      (fun x y => add_comm x y)
  · exact foldFam_nestable (fun x y z => mul_assoc x y z)
      (fun x => mul_one x)
  · exact foldFam_symmetric (fun x y z => mul_assoc x y z)
      (fun x y => mul_comm x y)
  · exact foldFam_nestable (fun x y z => add_assoc x y z)
      (fun x => add_zero x)
  · exact foldFam_symmetric (fun x y z => add_assoc x y z)
      (fun x y => add_comm x y)
  · exact foldFam_nestable (fun x y z => mul_assoc x y z)
      (fun x => mul_one x)
  · exact foldFam_symmetric (fun x y z => mul_assoc x y z)
      (fun x y => mul_comm x y)

end NeSyCat
