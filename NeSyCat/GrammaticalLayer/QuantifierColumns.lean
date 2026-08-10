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
# Quantifier columns are nestable (C3-B4b)

Toward blueprint item `lem:quantifier-columns-nestable`
(`blueprint/src/content.tex`, §"Grammatical layer"): the four running
interpretation families (max, min, the Σ-Π pair, and their log twins)
are symmetric and nestable in the sense of the hypotheses of
`lem:quantifier-nestable`.

**Honest scope (disclosed, C3-B4b).** The predicates are EXACTLY
`QuantifierNestable.lean`'s `Nestable`/`SymmetricFamily` (the Lean
form of `lem:quantifier-nestable`'s hypotheses), instantiated at the
category of sets — the base category of the running interpretations —
where an `n`-ary reduction family is the fold `foldFam op e` of a
binary operation over the tensor power. `foldFam_nestable` and
`foldFam_symmetric` prove the env's proof sentence generically:
nestability from associativity (with the fold's own seed-unit laws),
symmetry from commutativity (adjacent transpositions). The six
concrete columns instantiate them: max, Σ, Π on `ℝ≥0` (the mass
carrier), min on `unitInterval` (min needs the top element the
unbounded mass carrier lacks; the probability carrier supplies it),
and the log twins `lse`/`+` on `LogS` — `lem:log-iso`'s transported
`CommSemiring` makes `lse`/`logMul` literally `LogS`'s own `+`/`*`, so
the twins inherit both properties from the transported semiring laws,
the env's own "along the log isomorphism" argument. The env carries NO
`\lean`/`\leanok` mark: its phrase "the four running interpretation
families" denotes `𝓘(Q)ₙ` data of `def:logical-interpretation`, and no
concrete `LogInterpretation` witnessing the running columns exists in
Lean yet — the families here are their scalar reductions, the level
the env's own proof argues at; the marking decision is deferred to
LEAD (see `.foreman/scratch/C3-B4b-report.md`).
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

open scoped NNReal unitInterval in
/-- Toward `lem:quantifier-columns-nestable` (C3-B4b), the six
concrete columns: max, Σ (`+`), Π (`·`) on `ℝ≥0` (the mass carrier);
min on `unitInterval` (the probability carrier, whose top element is
min's seed unit — the unbounded mass carrier has none); the log twins
on `LogS`, whose transported semiring operations ARE `lse` and
`logMul` (`lem:log-iso`, `logS_add_eq_lse`/`logS_mul_eq_logMul`), so
the twins inherit both properties along the log isomorphism, the
env's own argument. Every seed is the operation's genuine unit, so
each fold family is the intended `n`-ary reduction. -/
@[blueprint_internal] -- toward lem:quantifier-columns-nestable: the
-- six running columns are symmetric and nestable, env unmarked
-- pending LEAD's carrier-level adjudication
theorem quantifier_columns_nestable :
    (Nestable (foldFam max (0 : ℝ≥0)) ∧
        SymmetricFamily (foldFam max (0 : ℝ≥0))) ∧
      (Nestable (foldFam min (1 : unitInterval)) ∧
        SymmetricFamily (foldFam min (1 : unitInterval))) ∧
      (Nestable (foldFam (· + ·) (0 : ℝ≥0)) ∧
        SymmetricFamily (foldFam (· + ·) (0 : ℝ≥0))) ∧
      (Nestable (foldFam (· * ·) (1 : ℝ≥0)) ∧
        SymmetricFamily (foldFam (· * ·) (1 : ℝ≥0))) ∧
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
      (fun x => min_eq_left unitInterval.le_one')
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
