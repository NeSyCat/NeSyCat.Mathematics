/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.GrammaticalLayer.Kleisli

/-!
# Morphisms of Kleisli interpretations

Blueprint items `def:interpretation-morphism` and
`lem:kleisli-term-natural` (`blueprint/src/content.tex`, §"Grammatical
layer"): what it takes to map one Kleisli interpretation
(`def:kleisli-interpretation`) to another, and the term half of the
resulting naturality statement.

**Two readings, two pieces of data.** The batched reading of a formula
and its unbatched reading differ in TWO ways at once, not one. Their
monads differ (`Bmon 𝓜` against `𝓜`), and so do the objects they assign
to a domain symbol (`Bidx → 𝓘(S)` against `𝓘(S)`), because a batch
`s : Bidx → 𝓘(S)` is what the batched reading consumes. A morphism of
interpretations therefore carries an object-level family
`domMor : 𝓘₁(S) ⟶ 𝓘₂(S)` alongside a monad morphism
`monadMor : 𝓜₁ ⟶ 𝓜₂`; in the batch case both are `ev i`, read once as a
projection `(Bidx → X) → X` and once as a monad morphism
(`NeSyCat.evMonadHom`, `NeSyCat/StatisticalLayer/Batching/TypeInstantiation.lean`).
Bundling only the monad half would give a statement the batch case
cannot discharge, since nothing would carry a batch to its `i`-th entry.

**Zero blast radius.** `InterpretationMorphism` is a NEW structure over
the existing records. No field is added to `CatInterpretation`,
`StrongCatInterpretation`, `LogInterpretation`, `DomInterpretation`, or
`KleisliInterpretation`, and no existing declaration is modified: every
law this file needs travels as a hypothesis, the pattern
`batchTransformer` already uses for its own left-unit hypothesis
(`NeSyCat/StatisticalLayer/Batching/BatchTransformer.lean`).

**The shared CD category.** Both readings live over one CD category, one
actor category, and one action; only the monad differs.
`CatInterpretation.withMonad` names that: the target reading is
`I.withMonad M₂`, so `(I.withMonad M₂).cd` is `I.cd` definitionally and
every object of one reading is an object of the other. Two unrelated
`CatInterpretation`s cannot be compared at all, their carriers being
different types; a common CD category is what makes the object-level
family `domMor` expressible, and the batch instantiation has it
definitionally (both readings are `typeCatInterpretation` at `typeCD`).

**Why `strength_natural` is a field.** The induction needs the TARGET
strength to be natural in both slots. `StrongCatInterpretation` bundles
the strength morphism with no naturality law, and this file may not add
one to it, so the law travels here as a hypothesis. It is not a
relation between the two readings, and its doc comment says so.

**Scope.** This file proves the TERM half, `Tm.sem_natural` with its
`TmList.sem_natural` companion. The formula half (`Fm.sem`) and the
instantiation at `ev i` are separate items.
-/

open CategoryTheory MonoidalCategory

universe u u' v v'

namespace NeSyCat

-- A CD category's own category/monoidal/symmetric structures, made local
-- instances for this file. They are exactly the instances every earlier
-- file names by hand through `letI := I.cd.instCat`; registering them
-- locally keeps the terms this file builds syntactically equal to the
-- terms those files' statements already carry.
attribute [local instance] CDCategory.instCat CDCategory.instMonoidal CDCategory.instSymmetric

/-- Companion of `def:interpretation-morphism`: the interpretation `I`
with its monad replaced by `M`, everything else (CD category, actor
category, action) kept. The two readings a morphism of interpretations
compares are `I` and `I.withMonad M₂`; `(I.withMonad M₂).cd` is `I.cd`
definitionally, which is what lets an object-level family
`𝓘₁(S) ⟶ 𝓘₂(S)` be written at all. -/
@[reducible, blueprint_internal] -- companion of def:interpretation-morphism:
-- the target reading's categorical interpretation, `I` with a new monad
-- (reducible so instance search sees through `(I.withMonad M).cd` to
-- `I.cd`, the shared CD category both readings live over)
def CatInterpretation.withMonad {sigA : CatSignature} (I : CatInterpretation sigA)
    (M : CategoryTheory.Monad I.cd.C) : CatInterpretation sigA :=
  { I with monad := M }

variable {sigA : CatSignature} {sigB : LogSignature} {sigG : DomSignature}
  {I : CatInterpretation.{u, v, u', v'} sigA} {M₂ : CategoryTheory.Monad I.cd.C}

/-- Companion of `def:interpretation-morphism`: a morphism `g : X₁ ⟶ X₂`
transported through a monad marker. At `Id` the marker adds nothing and
`g` is used as it stands; at `○` the source's `𝓜₁X₁` reaches the
target's `𝓜₂X₂` by the monad morphism followed by `𝓜₂g`. This is the
single per-slot rule out of which every induced morphism below is
built. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: the
-- per-marker transport rule
def markerMor (θ : I.monad.toFunctor ⟶ M₂.toFunctor) :
    (m : MonSym) → ∀ {X₁ X₂ : I.cd.C}, (X₁ ⟶ X₂) →
      ((I.interpretMon m).obj X₁ ⟶ ((I.withMonad M₂).interpretMon m).obj X₂)
  | .id => fun g => g
  | .mon => fun g => θ.app _ ≫ M₂.map g

/-- Companion of `def:interpretation-morphism`: the morphism
`𝓘₁(M₁S₁,…,MₙSₙ) ⟶ 𝓘₂(M₁S₁,…,MₙSₙ)` induced on a marked-symbol list's
tensor (`interpretMS`), slot by slot via `markerMor`. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: the
-- induced morphism on a marked-symbol list's tensor
def interpretMSMor {J₁ : LogInterpretation I sigB} (D₁ : DomInterpretation I J₁ sigG)
    {J₂ : LogInterpretation (I.withMonad M₂) sigB}
    (D₂ : DomInterpretation (I.withMonad M₂) J₂ sigG)
    (θ : I.monad.toFunctor ⟶ M₂.toFunctor)
    (dm : ∀ S : sigG.Dom, D₁.domObj S ⟶ D₂.domObj S) :
    (l : List (MonSym × sigG.Dom)) →
      (interpretMS I D₁.domObj l ⟶ interpretMS (I.withMonad M₂) D₂.domObj l)
  | [] => 𝟙 (𝟙_ I.cd.C)
  | p :: l => markerMor θ p.1 (dm p.2) ⊗ₘ interpretMSMor D₁ D₂ θ dm l

/-- Companion of `def:interpretation-morphism`: the morphism
`(𝓘₁(M)Ω₁)^{⊠n} ⟶ (𝓘₂(M)Ω₂)^{⊠n}` induced on a tensor power
(`interpretPow`) by a morphism of the two truth objects. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: the
-- induced morphism on a tensor power
def interpretPowMor (θ : I.monad.toFunctor ⟶ M₂.toFunctor) {X₁ X₂ : I.cd.C} (g : X₁ ⟶ X₂)
    (m : MonSym) :
    (n : ℕ) → (interpretPow I X₁ m n ⟶ interpretPow (I.withMonad M₂) X₂ m n)
  | 0 => 𝟙 (𝟙_ I.cd.C)
  | n + 1 => markerMor θ m g ⊗ₘ interpretPowMor θ g m n

/-- Companion of `def:interpretation-morphism`: the morphism
`𝓘₁(l) ⟶ 𝓘₂(l)` induced on a variable context's tensor (`ctxObj`).
Every context slot is `Id`-marked, so this is `interpretMSMor` at the
`Id`-marked list a context interprets to. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: the
-- induced morphism on a variable context's tensor
def ctxObjMor {J₁ : LogInterpretation I sigB} (D₁ : DomInterpretation I J₁ sigG)
    {J₂ : LogInterpretation (I.withMonad M₂) sigB}
    (D₂ : DomInterpretation (I.withMonad M₂) J₂ sigG)
    (θ : I.monad.toFunctor ⟶ M₂.toFunctor)
    (dm : ∀ S : sigG.Dom, D₁.domObj S ⟶ D₂.domObj S) (l : List sigG.Var) :
    ctxObj D₁ l ⟶ ctxObj (I := I.withMonad M₂) (J := J₂) D₂ l :=
  interpretMSMor D₁ D₂ θ dm (l.map fun x => (MonSym.id, sigG.varOver x))

/-- Companion of `def:interpretation-morphism`: a strength natural in
both slots has a left strength natural in both slots, by naturality of
the braiding. `StrongCatInterpretation` bundles the strength morphism
with no naturality law, so the law is a hypothesis here. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: left
-- strength naturality from right strength naturality
theorem StrongCatInterpretation.leftStrength_natural {I : CatInterpretation sigA}
    (SI : StrongCatInterpretation I)
    (hstr : ∀ {X₁ X₂ Y₁ Y₂ : I.cd.C} (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂),
      (a ⊗ₘ I.monad.map b) ≫ SI.strength = SI.strength ≫ I.monad.map (a ⊗ₘ b))
    {X₁ X₂ Y₁ Y₂ : I.cd.C} (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) :
    (I.monad.map a ⊗ₘ b) ≫ SI.leftStrength = SI.leftStrength ≫ I.monad.map (a ⊗ₘ b) := by
  simp only [StrongCatInterpretation.leftStrength, Category.assoc,
    BraidedCategory.braiding_naturality_assoc]
  rw [reassoc_of% hstr b a]
  simp only [← Functor.map_comp, BraidedCategory.braiding_naturality]

/-- Companion of `def:interpretation-morphism`: a strength natural in
both slots has a double strength natural in both slots, by the left
strength above together with naturality of the multiplication. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: double
-- strength naturality from right strength naturality
theorem StrongCatInterpretation.dst_natural {I : CatInterpretation sigA}
    (SI : StrongCatInterpretation I)
    (hstr : ∀ {X₁ X₂ Y₁ Y₂ : I.cd.C} (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂),
      (a ⊗ₘ I.monad.map b) ≫ SI.strength = SI.strength ≫ I.monad.map (a ⊗ₘ b))
    {X₁ X₂ Y₁ Y₂ : I.cd.C} (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) :
    (I.monad.map a ⊗ₘ I.monad.map b) ≫ SI.dst = SI.dst ≫ I.monad.map (a ⊗ₘ b) := by
  simp only [StrongCatInterpretation.dst, Category.assoc]
  rw [reassoc_of% SI.leftStrength_natural hstr a (I.monad.map b), ← Functor.map_comp_assoc,
    hstr a b, Functor.map_comp_assoc, I.monad.mu_naturality]
  rfl

/-- Blueprint `def:interpretation-morphism` (Morphism of interpretations),
the env's one cited principal declaration: what it takes to carry one
Kleisli interpretation (`def:kleisli-interpretation`) to another over the
same CD category. The data are an object-level family `domMor` on domain
symbols, a morphism `omegaMor` of truth objects, and a monad morphism
`monadMor`; the laws are that the two readings' strengths agree along
`monadMor`, and that every symbol of `def:domain-interpretation` and
`def:logical-interpretation` is interpreted compatibly. -/
structure InterpretationMorphism
    {I : CatInterpretation.{u, v, u', v'} sigA} (SI₁ : StrongCatInterpretation I)
    {J₁ : LogInterpretation I sigB} {D₁ : DomInterpretation I J₁ sigG}
    (K₁ : KleisliInterpretation I SI₁ J₁ D₁)
    {M₂ : CategoryTheory.Monad I.cd.C} (SI₂ : StrongCatInterpretation (I.withMonad M₂))
    {J₂ : LogInterpretation (I.withMonad M₂) sigB}
    {D₂ : DomInterpretation (I.withMonad M₂) J₂ sigG}
    (K₂ : KleisliInterpretation (I.withMonad M₂) SI₂ J₂ D₂) where
  /-- The object-level family `𝓘₁(S) ⟶ 𝓘₂(S)`, one morphism per domain
  symbol. In the batch reading this is `ev i` read as a projection
  `(Bidx → X) → X`. -/
  domMor : ∀ S : sigG.Dom, D₁.domObj S ⟶ D₂.domObj S
  /-- The morphism `Ω₁ ⟶ Ω₂` of truth objects. In the batch reading it is
  the identity: a batched formula is read at one shared truth object. -/
  omegaMor : J₁.Ω ⟶ J₂.Ω
  /-- The monad morphism `𝓜₁ ⟶ 𝓜₂`. In the batch reading this is `ev i`
  again, now read as a monad morphism `Bmon 𝓜 ⟶ 𝓜` (`evMonadHom`). -/
  monadMor : CategoryTheory.MonadHom I.monad M₂
  /-- Strength compatibility: pushing a pure factor into a computation and
  then changing reading is the same as changing reading first. -/
  strength_compat : ∀ {X Y : I.cd.C},
    SI₁.strength ≫ monadMor.app (X ⊗ Y) = (𝟙 X ⊗ₘ monadMor.app Y) ≫ SI₂.strength
  /-- Naturality of the TARGET strength. This is a law of `SI₂` alone, not
  a relation between the two readings: `StrongCatInterpretation` bundles
  the strength morphism without it, and the induction below needs it, so
  it travels here as a hypothesis. -/
  strength_natural : ∀ {X₁ X₂ Y₁ Y₂ : I.cd.C} (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂),
    (a ⊗ₘ M₂.map b) ≫ SI₂.strength = SI₂.strength ≫ M₂.map (a ⊗ₘ b)
  /-- Every function symbol is interpreted compatibly: `𝓘₁(f)` followed by
  the induced morphism on its codomain equals the induced morphism on its
  domain followed by `𝓘₂(f)`. -/
  funMorK_compat : ∀ f : sigG.Fun,
    K₁.funMorK f ≫ interpretMSMor D₁ D₂ monadMor.toNatTrans domMor (sigG.fcod f)
      = interpretMSMor D₁ D₂ monadMor.toNatTrans domMor (sigG.fdom f) ≫ K₂.funMorK f
  /-- Every relation symbol is interpreted compatibly. -/
  relMorK_compat : ∀ R : sigG.Rel,
    K₁.relMorK R ≫ omegaMor
      = interpretMSMor D₁ D₂ monadMor.toNatTrans domMor (sigG.rari R) ≫ K₂.relMorK R
  /-- Every connective symbol is interpreted compatibly. -/
  connMor_compat : ∀ c : sigB.Conn,
    J₁.connMor c ≫ markerMor monadMor.toNatTrans (sigB.connMonad c) omegaMor
      = interpretPowMor monadMor.toNatTrans omegaMor (sigB.connMonad c) (sigB.connArity c) ≫
          J₂.connMor c
  /-- Every quantifier symbol is interpreted compatibly, at every arity. -/
  quanMor_compat : ∀ (Q : sigB.Quan) (n : ℕ),
    J₁.quanMor Q n ≫ markerMor monadMor.toNatTrans (sigB.quanMonad Q) omegaMor
      = interpretPowMor monadMor.toNatTrans omegaMor (sigB.quanMonad Q) n ≫ J₂.quanMor Q n

namespace InterpretationMorphism

variable {SI₁ : StrongCatInterpretation I} {J₁ : LogInterpretation I sigB}
  {D₁ : DomInterpretation I J₁ sigG} {K₁ : KleisliInterpretation I SI₁ J₁ D₁}
  {SI₂ : StrongCatInterpretation (I.withMonad M₂)}
  {J₂ : LogInterpretation (I.withMonad M₂) sigB}
  {D₂ : DomInterpretation (I.withMonad M₂) J₂ sigG}
  {K₂ : KleisliInterpretation (I.withMonad M₂) SI₂ J₂ D₂}
  (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂)

/-- Companion of `def:interpretation-morphism`: the induced morphism on a
marked-symbol list's tensor, read off the morphism's own data. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: named
-- accessor for interpretMSMor at this morphism's data
def msMor (l : List (MonSym × sigG.Dom)) :
    interpretMS I D₁.domObj l ⟶ interpretMS (I.withMonad M₂) D₂.domObj l :=
  interpretMSMor D₁ D₂ Φ.monadMor.toNatTrans Φ.domMor l

/-- Companion of `def:interpretation-morphism`: the induced morphism on a
variable context's tensor, read off the morphism's own data. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: named
-- accessor for ctxObjMor at this morphism's data
def ctxMor (l : List sigG.Var) :
    ctxObj D₁ l ⟶ ctxObj (I := I.withMonad M₂) (J := J₂) D₂ l :=
  ctxObjMor D₁ D₂ Φ.monadMor.toNatTrans Φ.domMor l

/-- Companion of `def:interpretation-morphism`: the two readings' left
strengths agree along the monad morphism, by naturality of the braiding
and of the monad morphism. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: left
-- strength compatibility, derived from strength_compat
theorem leftStrength_compat {X Y : I.cd.C} :
    SI₁.leftStrength ≫ Φ.monadMor.app (X ⊗ Y)
      = (Φ.monadMor.app X ⊗ₘ 𝟙 Y) ≫ SI₂.leftStrength := by
  simp only [StrongCatInterpretation.leftStrength, Category.assoc,
    BraidedCategory.braiding_naturality_assoc]
  rw [Φ.monadMor.toNatTrans.naturality, ← Category.assoc SI₁.strength, Φ.strength_compat]
  simp only [Category.assoc]

/-- Companion of `def:interpretation-morphism`: the two readings' double
strengths agree along the monad morphism. Derived from `strength_compat`,
the monad morphism's own multiplication law, and naturality. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: double
-- strength compatibility, derived from strength_compat
theorem dst_compat {X Y : I.cd.C} :
    SI₁.dst ≫ Φ.monadMor.app (X ⊗ Y)
      = (Φ.monadMor.app X ⊗ₘ Φ.monadMor.app Y) ≫ SI₂.dst := by
  simp only [StrongCatInterpretation.dst, Category.assoc]
  erw [Φ.monadMor.app_μ]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Φ.strength_compat, Functor.map_comp_assoc,
    Φ.monadMor.toNatTrans.naturality_assoc, Φ.monadMor.toNatTrans.naturality_assoc,
    reassoc_of% Φ.leftStrength_compat,
    ← reassoc_of% SI₂.leftStrength_natural Φ.strength_natural (𝟙 X) (Φ.monadMor.app Y)]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp

end InterpretationMorphism

end NeSyCat
