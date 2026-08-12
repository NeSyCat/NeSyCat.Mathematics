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
  /-- The object-level family copies: `domMor S` carries the CD category's
  chosen comultiplication on `𝓘₁(S)` to the one on `𝓘₂(S)`. The formula
  half's atomic, compound and quantified clauses all route their context
  through `copy`, so the family has to respect it. In the batch reading
  this is the diagonal on a function type read at one index. -/
  domMor_comul : ∀ S : sigG.Dom,
    domMor S ≫ (I.cd.comon (D₂.domObj S)).comul
      = (I.cd.comon (D₁.domObj S)).comul ≫ (domMor S ⊗ₘ domMor S)
  /-- The object-level family discards: `domMor S` carries the CD
  category's chosen counit on `𝓘₁(S)` to the one on `𝓘₂(S)`. Together with
  `domMor_comul` this says every component is a comonoid morphism. -/
  domMor_counit : ∀ S : sigG.Dom,
    domMor S ≫ (I.cd.comon (D₂.domObj S)).counit = (I.cd.comon (D₁.domObj S)).counit
  /-- The chosen comultiplication is compatible with the tensor: on
  `X ⊠ Y` it is the two factors' comultiplications followed by the shuffle
  that puts the four factors back in order. This is a law of the CD
  category alone, like `strength_natural` below, and it travels here for
  the same reason: this file may not change `CDCategory`. `CDCategory`
  does declare a field of this name, but as elaborated that field is
  reflexivity, because the structure's own `comon` field is itself a local
  instance and so `ComonObj.comul (X := X ⊗ Y)` there resolves to the
  chosen comonoid rather than to the induced one. -/
  comul_tensor : ∀ X Y : I.cd.C,
    (I.cd.comon (X ⊗ Y)).comul
      = ((I.cd.comon X).comul ⊗ₘ (I.cd.comon Y).comul) ≫ tensorμ X X Y Y
  /-- The chosen counit is compatible with the tensor: on `X ⊠ Y` it is the
  two factors' counits into the unit. The discard twin of `comul_tensor`,
  carried here for the same reason. -/
  counit_tensor : ∀ X Y : I.cd.C,
    (I.cd.comon (X ⊗ Y)).counit
      = ((I.cd.comon X).counit ⊗ₘ (I.cd.comon Y).counit) ≫ (λ_ (𝟙_ I.cd.C)).hom
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

/-!
## The term half of the naturality induction

`Tm.sem_natural` below, with its list companion `TmList.sem_natural`, is
the term half: a morphism of interpretations carries `Tm.sem`'s reading of
a term to the other reading's, one grammar rule at a time. Two clauses do
the work. A variable term reads as the monad's unit, so its clause is the
monad morphism's own unit law together with naturality of the target
unit. A functional term reads as its argument list's semantics followed
by `𝓘(f)`, so its clause is `funMorK_compat` together with the induction
hypothesis on the list; the list's cons clause is where the two strengths
meet, through `dst_compat` and the target strength's naturality.

**Transports.** `Tm.sem` computes its clauses through `Tm.inn` and
`Tm.KTyped`, and both of those are compiled by recursion over a nested
inductive, so their clauses hold propositionally and not definitionally.
`Tm.sem`'s own equations therefore carry casts. The lemmas below turn each
cast into an `eqToHom` composite once and for all: `eqRec_cod` for the
codomain transport of the functional-term clause, `Tm.sem_var_eq` and
`Tm.sem_app_eq` for the two clauses themselves, `msMor_eqToHom` and
`ctxMor_eqToHom` for moving an `eqToHom` past an induced morphism.
-/

section TermNaturality

variable {J : LogInterpretation I sigB} {D : DomInterpretation I J sigG}
  {SI : StrongCatInterpretation I}

/-- Companion of `lem:kleisli-term-natural`: a transport in a morphism's
codomain is a composite with `eqToHom`. Stated for an arbitrary family
`F : α → C` of objects, which is all the proof uses; the induction below
meets it at `F := fun l => 𝓜𝓘(l)`, where `Tm.sem`'s functional-term clause
transports along the value-match witness of `Tm.KTyped`. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: the
-- codomain-transport lemma the functional-term clause needs
theorem eqRec_cod {C : Type*} [Category C] {α : Sort*} (F : α → C) {X : C} {a b : α}
    (g : X ⟶ F a) (h : a = b) :
    @Eq.rec α a (fun y _ => X ⟶ F y) g b h = g ≫ eqToHom (congrArg F h) := by
  cases h; simp

/-- Companion of `lem:kleisli-term-natural`: `inn(x) = [x]`, the variable
clause of `Tm.inn` (`def:grammatical-signature`) as a rewrite. `Tm.inn`
recurses over a nested inductive, so its clauses are propositional. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: Tm.inn's
-- variable clause as a rewrite
theorem Tm.inn_var (x : sigG.Var) : (Tm.var x : Tm sigG sigB).inn = [x] := by
  simp [Tm.inn]

/-- Companion of `lem:kleisli-term-natural`: `inn(f(ξ⃗))` is the
concatenation of the arguments' own contexts, the functional clause of
`Tm.inn` as a rewrite. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: Tm.inn's
-- functional clause as a rewrite
theorem Tm.inn_app (f : sigG.Fun) (args : List (Tm sigG sigB)) :
    (Tm.app f args : Tm sigG sigB).inn = (args.map Tm.inn).flatten := by
  simp [Tm.inn]

/-- Companion of `lem:kleisli-term-natural`: the two conjuncts of
`Tm.KTyped` at a functional term, the value-match witness and the
arguments' own typing. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural:
-- Tm.KTyped's functional clause, read off
theorem Tm.ktyped_app {f : sigG.Fun} {args : List (Tm sigG sigB)}
    (ht : (Tm.app f args : Tm sigG sigB).KTyped) :
    (args.map Tm.kcod).flatten = sigG.fdom f ∧ ∀ a ∈ args, a.KTyped := by
  simpa [Tm.KTyped] using ht

/-- Companion of `lem:kleisli-term-natural`: `⟦x⟧` is the monad's unit at
`𝓘([x])`, up to the transport along `inn(x) = [x]`. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: Tm.sem's
-- variable clause, cast-free
theorem Tm.sem_var_eq (K : KleisliInterpretation I SI J D) (x : sigG.Var)
    (h : (Tm.var x : Tm sigG sigB).KTyped) :
    Tm.sem K (.var x) h
      = eqToHom (congrArg (ctxObj D) (Tm.inn_var x)) ≫ I.monad.η.app (ctxObj D [x]) := by
  have hh : Tm.sem K (Tm.var x) h ≍ I.monad.η.app (ctxObj D [x]) := by
    rw [Tm.sem.eq_1]
    simp only [eq_mpr_eq_cast]
    exact cast_heq _ _
  exact eq_of_heq (hh.trans (eqToHom_comp_heq _ _).symm)

/-- Companion of `lem:kleisli-term-natural`: `⟦f(ξ⃗)⟧` is the argument
list's semantics followed by `𝓘(f)`, up to the transport along
`inn(f(ξ⃗)) = inn(ξ⃗)` and the value-match witness `he`. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: Tm.sem's
-- functional clause, cast-free
theorem Tm.sem_app_eq (K : KleisliInterpretation I SI J D) (f : sigG.Fun)
    (args : List (Tm sigG sigB)) (ht : (Tm.app f args : Tm sigG sigB).KTyped)
    (he : (args.map Tm.kcod).flatten = sigG.fdom f) (hargs : ∀ a ∈ args, a.KTyped) :
    Tm.sem K (.app f args) ht
      = eqToHom (congrArg (ctxObj D) (Tm.inn_app f args)) ≫ TmList.sem K args hargs ≫
          I.monad.map (eqToHom (congrArg (interpretMS I D.domObj) he) ≫ K.funMorK f) := by
  have hh : Tm.sem K (Tm.app f args) ht
      ≍ TmList.sem K args hargs ≫
          I.monad.map (eqToHom (congrArg (interpretMS I D.domObj) he) ≫ K.funMorK f) := by
    rw [Tm.sem.eq_2]
    simp only [eq_mpr_eq_cast]
    refine (cast_heq _ _).trans ?_
    rw [eqRec_cod (fun l => I.monad.obj (interpretMS I D.domObj l))]
    simp [eqToHom_map]
  exact eq_of_heq (hh.trans (eqToHom_comp_heq _ _).symm)

end TermNaturality

section TermNaturalityMor

variable {SI₁ : StrongCatInterpretation I} {J₁ : LogInterpretation I sigB}
  {D₁ : DomInterpretation I J₁ sigG} {K₁ : KleisliInterpretation I SI₁ J₁ D₁}
  {SI₂ : StrongCatInterpretation (I.withMonad M₂)}
  {J₂ : LogInterpretation (I.withMonad M₂) sigB}
  {D₂ : DomInterpretation (I.withMonad M₂) J₂ sigG}
  {K₂ : KleisliInterpretation (I.withMonad M₂) SI₂ J₂ D₂}

/-- Companion of `lem:kleisli-term-natural`: the induced morphism on a
marked-symbol list's tensor commutes with a transport of the list. -/
@[blueprint_internal, reassoc (attr := blueprint_internal)]
-- companion of lem:kleisli-term-natural: msMor against a list transport
theorem msMor_eqToHom (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂)
    {l l' : List (MonSym × sigG.Dom)} (h : l = l') :
    eqToHom (congrArg (interpretMS I D₁.domObj) h) ≫ Φ.msMor l'
      = Φ.msMor l ≫ eqToHom (congrArg (interpretMS (I.withMonad M₂) D₂.domObj) h) := by
  cases h; simp

/-- Companion of `lem:kleisli-term-natural`: the induced morphism on a
context's tensor commutes with a transport of the context. -/
@[blueprint_internal, reassoc (attr := blueprint_internal)]
-- companion of lem:kleisli-term-natural: ctxMor against a context transport
theorem ctxMor_eqToHom (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂)
    {l l' : List sigG.Var} (h : l = l') :
    eqToHom (congrArg (ctxObj D₁) h) ≫ Φ.ctxMor l'
      = Φ.ctxMor l ≫ eqToHom (congrArg (ctxObj (I := I.withMonad M₂) (J := J₂) D₂) h) := by
  cases h; simp

/-- Companion of `lem:kleisli-term-natural`: `funMorK_compat` written
through the named accessor `msMor`. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural:
-- funMorK_compat at msMor
theorem funMorK_comp_msMor (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) (f : sigG.Fun) :
    K₁.funMorK f ≫ Φ.msMor (sigG.fcod f) = Φ.msMor (sigG.fdom f) ≫ K₂.funMorK f :=
  Φ.funMorK_compat f

/-- Companion of `lem:kleisli-term-natural`: the induced morphism on a
concatenated marked-symbol list splits along `kcodAppendIso`, by induction
on the first list. The unit case is naturality of the left unitor; the
step case is naturality of the associator. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: msMor
-- against the concatenation associator
theorem msMor_kcodAppendIso (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) :
    ∀ l1 l2 : List (MonSym × sigG.Dom),
      Φ.msMor (l1 ++ l2) ≫ (kcodAppendIso D₂ l1 l2).hom
        = (kcodAppendIso D₁ l1 l2).hom ≫ (Φ.msMor l1 ⊗ₘ Φ.msMor l2)
  | [], l2 => by
      change Φ.msMor l2 ≫ (λ_ (interpretMS (I.withMonad M₂) D₂.domObj l2)).inv
          = (λ_ (interpretMS I D₁.domObj l2)).inv ≫ (𝟙 (𝟙_ I.cd.C) ⊗ₘ Φ.msMor l2)
      rw [id_tensorHom]
      exact MonoidalCategory.leftUnitor_inv_naturality _
  | p :: l1', l2 => by
      have ih := msMor_kcodAppendIso Φ l1' l2
      change (markerMor Φ.monadMor.toNatTrans p.1 (Φ.domMor p.2) ⊗ₘ Φ.msMor (l1' ++ l2)) ≫
          (((I.withMonad M₂).interpretMon p.1).obj (D₂.domObj p.2) ◁
              (kcodAppendIso D₂ l1' l2).hom ≫ (α_ _ _ _).inv)
        = (((I.interpretMon p.1).obj (D₁.domObj p.2) ◁ (kcodAppendIso D₁ l1' l2).hom ≫
            (α_ _ _ _).inv)) ≫
          ((markerMor Φ.monadMor.toNatTrans p.1 (Φ.domMor p.2) ⊗ₘ Φ.msMor l1') ⊗ₘ Φ.msMor l2)
      rw (config := { transparency := .default })
        [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, ih,
          Category.assoc, ← associator_inv_naturality, ← id_tensorHom, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp]

/-- Companion of `lem:kleisli-term-natural`: `msMor_kcodAppendIso` read in
the other direction, the form `TmList.sem`'s cons clause needs. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: the
-- inverse half of msMor against the concatenation associator
theorem msMor_kcodAppendIso_inv (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂)
    (l1 l2 : List (MonSym × sigG.Dom)) :
    (kcodAppendIso D₁ l1 l2).inv ≫ Φ.msMor (l1 ++ l2)
      = (Φ.msMor l1 ⊗ₘ Φ.msMor l2) ≫ (kcodAppendIso D₂ l1 l2).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← msMor_kcodAppendIso Φ l1 l2, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Companion of `lem:kleisli-term-natural`: the induced morphism on a
concatenated context splits along `ctxAppendIso`, the context twin of
`msMor_kcodAppendIso` and proved the same way. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: ctxMor
-- against the concatenation associator
theorem ctxMor_ctxAppendIso (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) :
    ∀ l1 l2 : List sigG.Var,
      Φ.ctxMor (l1 ++ l2) ≫ (ctxAppendIso D₂ l1 l2).hom
        = (ctxAppendIso D₁ l1 l2).hom ≫ (Φ.ctxMor l1 ⊗ₘ Φ.ctxMor l2)
  | [], l2 => by
      change Φ.ctxMor l2 ≫ (λ_ (ctxObj (I := I.withMonad M₂) (J := J₂) D₂ l2)).inv
          = (λ_ (ctxObj D₁ l2)).inv ≫ (𝟙 (𝟙_ I.cd.C) ⊗ₘ Φ.ctxMor l2)
      rw [id_tensorHom]
      exact MonoidalCategory.leftUnitor_inv_naturality _
  | x :: l1', l2 => by
      have ih := ctxMor_ctxAppendIso Φ l1' l2
      change (Φ.domMor (sigG.varOver x) ⊗ₘ Φ.ctxMor (l1' ++ l2)) ≫
          (D₂.domObj (sigG.varOver x) ◁ (ctxAppendIso D₂ l1' l2).hom ≫ (α_ _ _ _).inv)
        = (D₁.domObj (sigG.varOver x) ◁ (ctxAppendIso D₁ l1' l2).hom ≫ (α_ _ _ _).inv) ≫
          ((Φ.domMor (sigG.varOver x) ⊗ₘ Φ.ctxMor l1') ⊗ₘ Φ.ctxMor l2)
      rw (config := { transparency := .default })
        [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, ih,
          Category.assoc, ← associator_inv_naturality, ← id_tensorHom, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp]

mutual

/-- Companion of `lem:kleisli-term-natural`, the list half: a morphism of
interpretations carries the tensored semantics `⟦ξ⃗⟧` of a term list to the
other reading's. The empty list is the monad morphism's unit law; the cons
step is `dst_compat` and the target strength's naturality, against the two
induction hypotheses. -/
@[blueprint_internal] -- companion of lem:kleisli-term-natural: the
-- term-list half of the mutual induction
theorem TmList.sem_natural (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) :
    ∀ (ts : List (Tm sigG sigB)) (hts : ∀ a ∈ ts, a.KTyped),
      TmList.sem K₁ ts hts ≫ Φ.monadMor.app (interpretMS I D₁.domObj (ts.map Tm.kcod).flatten) ≫
          M₂.map (Φ.msMor (ts.map Tm.kcod).flatten)
        = Φ.ctxMor (ts.map Tm.inn).flatten ≫ TmList.sem K₂ ts hts
  | [], _ => by
      change I.monad.η.app (𝟙_ I.cd.C) ≫ Φ.monadMor.app (𝟙_ I.cd.C) ≫ M₂.map (𝟙 (𝟙_ I.cd.C))
          = 𝟙 (𝟙_ I.cd.C) ≫ M₂.η.app (𝟙_ I.cd.C)
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      exact Φ.monadMor.app_η _
  | t :: ts, hts => by
      have head_natural := Tm.sem_natural Φ t (hts t List.mem_cons_self)
      have tail_natural :=
        TmList.sem_natural Φ ts (fun a ha => hts a (List.mem_cons_of_mem t ha))
      simp only [TmList.sem, Category.assoc]
      rw (config := { transparency := .default })
        [Φ.monadMor.toNatTrans.naturality_assoc, reassoc_of% Φ.dst_compat,
          ← CategoryTheory.Functor.map_comp, msMor_kcodAppendIso_inv,
          CategoryTheory.Functor.map_comp,
          ← reassoc_of% (StrongCatInterpretation.dst_natural SI₂ Φ.strength_natural
            (Φ.msMor t.kcod) (Φ.msMor (ts.map Tm.kcod).flatten)),
          ← Category.assoc (Tm.sem K₁ t _ ⊗ₘ TmList.sem K₁ ts _), tensorHom_comp_tensorHom]
      simp only [← Category.assoc, tensorHom_comp_tensorHom]
      simp only [Category.assoc]
      rw (config := { transparency := .default })
        [head_natural, tail_natural, ← tensorHom_comp_tensorHom]
      simp only [← Category.assoc]
      rw (config := { transparency := .default })
        [← ctxMor_ctxAppendIso Φ t.inn (ts.map Tm.inn).flatten]
      rfl

/-- Blueprint `lem:kleisli-term-natural` (Term semantics is natural), the
env's one cited principal declaration: a morphism of interpretations
(`def:interpretation-morphism`) carries the term semantics of
`def:kleisli-interpretation` to the target reading's, for every term of
`def:grammatical-signature`'s grammar. By structural induction over terms,
mutually with `TmList.sem_natural` over argument lists: a variable term is
the monad morphism's unit law with naturality of the target unit, and a
functional term is `funMorK_compat` with the list's induction hypothesis. -/
theorem Tm.sem_natural (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) :
    ∀ (ξ : Tm sigG sigB) (h : ξ.KTyped),
      Tm.sem K₁ ξ h ≫ Φ.monadMor.app (interpretMS I D₁.domObj ξ.kcod) ≫
          M₂.map (Φ.msMor ξ.kcod)
        = Φ.ctxMor ξ.inn ≫ Tm.sem K₂ ξ h
  | .var x, h => by
      rw (config := { transparency := .default })
        [Tm.sem_var_eq K₁ x h, Tm.sem_var_eq K₂ x h, Category.assoc,
          ← Category.assoc (I.monad.η.app _), Φ.monadMor.app_η, ← M₂.η.naturality,
          ← Category.assoc, ctxMor_eqToHom Φ (Tm.inn_var x), Category.assoc]
      rfl
  | .app f args, ht => by
      obtain ⟨he, hargs⟩ := Tm.ktyped_app ht
      have list_natural := TmList.sem_natural Φ args hargs
      rw (config := { transparency := .default })
        [Tm.sem_app_eq K₁ f args ht he hargs, Tm.sem_app_eq K₂ f args ht he hargs,
          Category.assoc, Category.assoc,
          Φ.monadMor.toNatTrans.naturality_assoc, ← CategoryTheory.Functor.map_comp,
          Category.assoc, funMorK_comp_msMor Φ f, msMor_eqToHom_assoc Φ he,
          CategoryTheory.Functor.map_comp, reassoc_of% list_natural,
          ctxMor_eqToHom_assoc Φ (Tm.inn_app f args)]
      rfl

end

end TermNaturalityMor

/-!
## The formula clauses, read off cast-free

`Fm.sem` computes its four clauses through `Fm.on` and `Fm.KTyped`, both
compiled by recursion over a nested inductive, so those clauses hold
propositionally and not definitionally and `Fm.sem`'s own equations carry
casts. The lemmas below turn each cast into an `eqToHom` composite once and
for all, the formula-side twins of `Tm.sem_var_eq` and `Tm.sem_app_eq`:
`Fm.on_rel`/`Fm.on_conn`/`Fm.on_quant`/`Fm.on_subst` for the context,
`Fm.ktyped_rel`/`Fm.ktyped_conn`/`Fm.ktyped_quant`/`Fm.ktyped_subst` for the
typing side condition, and `Fm.sem_rel_eq`/`Fm.sem_conn_eq`/
`Fm.sem_quant_eq`/`Fm.sem_subst_eq` for the clauses themselves.

Two further casts appear here that the term half never met. A `Prop`
structure has no definitional eta, so the `obtain` a clause performs on its
typing witness stays a blocked `And.rec` in the equation: `and_rec_proj`
turns it into the witness's own projections, which proof irrelevance then
identifies with any other witness. And a clause that rewrites a hypothesis
rather than the goal leaves a `cast` in a morphism's codomain rather than an
`Eq.rec`: `cast_hom_cod` is `eqRec_cod`'s twin for that shape.

The connective and quantifier clauses dispatch on the marker their symbol
carries, so their morphisms are named here as `connMorAt` and `quanMorAt`,
built by the same marker match `Fm.sem` performs.
-/

section FmClauses

variable {J : LogInterpretation I sigB} {D : DomInterpretation I J sigG}
  {SI : StrongCatInterpretation I} [DecidableEq sigG.Var]

/-- Companion of `def:kleisli-interpretation`: a non-dependent case
analysis on a conjunction is that conjunction's own two projections. Lean
has no definitional eta for a `Prop` structure, so a clause's `obtain` on
its typing witness survives into `Fm.sem`'s equations as a blocked
`And.rec`; this releases it, and proof irrelevance then identifies the
projections with any other witness of the same conjunction. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: releases
-- the blocked And.rec a clause's `obtain` leaves in Fm.sem's equations
theorem and_rec_proj {a b : Prop} {M : Sort*} (f : ∀ (_ : a) (_ : b), M) (h : a ∧ b) :
    @And.rec a b (fun _ => M) f h = f h.1 h.2 := by
  cases h; rfl

/-- Companion of `def:kleisli-interpretation`: a cast in a morphism's
codomain is a composite with `eqToHom`. The twin of `eqRec_cod` for the
shape a clause leaves when it rewrites a hypothesis rather than the goal. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- codomain-cast lemma the relation-symbol and substitution clauses need
theorem cast_hom_cod {C : Type*} [Category C] {X Y Y' : C} (f : X ⟶ Y) (e : Y = Y')
    (h : (X ⟶ Y) = (X ⟶ Y')) : cast h f = f ≫ eqToHom e := by
  subst e; simp

/-- Companion of `def:kleisli-interpretation`: `[R(ξ⃗)]` is the dedup'd
concatenation of the arguments' own contexts, the atomic clause of `Fm.on`
as a rewrite. `Fm.on` recurses over a nested inductive, so its clauses are
propositional. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: Fm.on's
-- atomic clause as a rewrite
theorem Fm.on_rel (R : sigG.Rel) (args : List (Tm sigG sigB)) :
    (Fm.rel R args : Fm sigG sigB).on = firstDedup (args.map Tm.inn).flatten := by
  simp [Fm.on]

/-- Companion of `def:kleisli-interpretation`: `[*(φ⃗)]` is the dedup'd
concatenation of the arguments' own contexts, the compound clause of
`Fm.on` as a rewrite. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: Fm.on's
-- compound clause as a rewrite
theorem Fm.on_conn (c : sigB.Conn) (args : List (Fm sigG sigB)) :
    (Fm.conn c args : Fm sigG sigB).on = firstDedup (args.map Fm.on).flatten := by
  simp [Fm.on]

/-- Companion of `def:kleisli-interpretation`: `[Qx⃗(φ)]` is `[φ]` with the
bound variables removed, the quantified clause of `Fm.on` as a rewrite. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: Fm.on's
-- quantified clause as a rewrite
theorem Fm.on_quant (Q : sigB.Quan) (xs : List sigG.Var) (body : Fm sigG sigB) :
    (Fm.quant Q xs body : Fm sigG sigB).on = body.on.filter (fun v => !decide (v ∈ xs)) := by
  simp [Fm.on]

/-- Companion of `def:kleisli-interpretation`: `[φ[x := ξ]]` is `[φ]` with
`x` replaced positionally by `inn(ξ)`, the substituted clause of `Fm.on` as
a rewrite. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: Fm.on's
-- substituted clause as a rewrite
theorem Fm.on_subst (body : Fm sigG sigB) (x : sigG.Var) (t : Tm sigG sigB) :
    (Fm.subst body x t : Fm sigG sigB).on
      = body.on.takeWhile (fun v => decide (v ≠ x)) ++
          (t.inn ++ (body.on.dropWhile (fun v => decide (v ≠ x))).tail) := by
  simp [Fm.on]

/-- Companion of `def:kleisli-interpretation`: the two conjuncts of
`Fm.KTyped` at an atomic formula, the value-match witness and the
arguments' own typing. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- Fm.KTyped's atomic clause, read off
theorem Fm.ktyped_rel {R : sigG.Rel} {args : List (Tm sigG sigB)}
    (ht : (Fm.rel R args : Fm sigG sigB).KTyped) :
    (args.map Tm.kcod).flatten = sigG.rari R ∧ ∀ a ∈ args, a.KTyped := by
  simpa [Fm.KTyped] using ht

/-- Companion of `def:kleisli-interpretation`: the two conjuncts of
`Fm.KTyped` at a compound formula, the arity match and the arguments' own
typing. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- Fm.KTyped's compound clause, read off
theorem Fm.ktyped_conn {c : sigB.Conn} {args : List (Fm sigG sigB)}
    (ht : (Fm.conn c args : Fm sigG sigB).KTyped) :
    sigB.connArity c = args.length ∧ ∀ a ∈ args, a.KTyped := by
  simpa [Fm.KTyped] using ht

/-- Companion of `def:kleisli-interpretation`: a quantified formula's
typing is its body's. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- Fm.KTyped's quantified clause, read off
theorem Fm.ktyped_quant {Q : sigB.Quan} {xs : List sigG.Var} {body : Fm sigG sigB}
    (ht : (Fm.quant Q xs body : Fm sigG sigB).KTyped) : body.KTyped := by
  simpa [Fm.KTyped] using ht

/-- Companion of `def:kleisli-interpretation`: the four conjuncts of
`Fm.KTyped` at a substituted formula: the term's value match, the
substituted variable's occurrence, and the two subterms' own typing. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- Fm.KTyped's substituted clause, read off
theorem Fm.ktyped_subst {body : Fm sigG sigB} {x : sigG.Var} {t : Tm sigG sigB}
    (ht : (Fm.subst body x t : Fm sigG sigB).KTyped) :
    Tm.kcod t = [(MonSym.id, sigG.varOver x)] ∧ x ∈ body.on ∧ body.KTyped ∧ t.KTyped := by
  simpa [Fm.KTyped] using ht

/-- Companion of `def:kleisli-interpretation`: `⟦R(ξ⃗)⟧` is the dedup'd
context routed to the argument list's semantics and then through `𝓘(R)`, up
to the transport along `[R(ξ⃗)] = firstDedup(inn(ξ⃗))` and the value-match
witness `he`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: Fm.sem's
-- atomic clause, cast-free
theorem Fm.sem_rel_eq (K : KleisliInterpretation I SI J D) (R : sigG.Rel)
    (args : List (Tm sigG sigB)) (ht : (Fm.rel R args : Fm sigG sigB).KTyped)
    (he : (args.map Tm.kcod).flatten = sigG.rari R) (hargs : ∀ a ∈ args, a.KTyped) :
    Fm.sem K (.rel R args) ht
      = eqToHom (congrArg (ctxObj D) (Fm.on_rel R args)) ≫
        ctxCopy D (firstDedup (args.map Tm.inn).flatten) (firstDedup_nodup _)
            (args.map Tm.inn).flatten (fun _ hy => mem_firstDedup hy) ≫
        TmList.sem K args hargs ≫
        I.monad.map (eqToHom (congrArg (interpretMS I D.domObj) he) ≫ K.relMorK R) := by
  have hh : Fm.sem K (Fm.rel R args) ht
      ≍ ctxCopy D (firstDedup (args.map Tm.inn).flatten) (firstDedup_nodup _)
            (args.map Tm.inn).flatten (fun _ hy => mem_firstDedup hy) ≫
          TmList.sem K args hargs ≫
          I.monad.map (eqToHom (congrArg (interpretMS I D.domObj) he) ≫ K.relMorK R) := by
    rw [Fm.sem.eq_1]
    simp only [eq_mpr_eq_cast]
    refine (cast_heq _ _).trans ?_
    rw [eqRec_cod (fun l => I.monad.obj (interpretMS I D.domObj l))]
    simp [eqToHom_map]
  exact eq_of_heq (hh.trans (eqToHom_comp_heq _ _).symm)

/-- Companion of `def:kleisli-interpretation`: `𝓘(*)` at whichever marker
the connective carries, read at an arity the typing witness matches — the
`○`-marked instance as it stands, the `Id`-marked one after `dstFoldN`
collapses the `n` separately-monadic factors. The same marker match
`Fm.sem`'s compound clause performs, named so that clause can be stated
without repeating it. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- compound clause's marker-dispatched connective morphism
def connMorAt (SI : StrongCatInterpretation I) (J : LogInterpretation I sigB)
    (c : sigB.Conn) (n : ℕ) (harity : sigB.connArity c = n) :
    tensorList (List.replicate n (I.monad.obj J.Ω)) ⟶ I.monad.obj J.Ω := by
  match hCM : sigB.connMonad c with
  | .mon =>
    have hcm := J.connMor c
    rw [hCM, harity] at hcm
    exact hcm
  | .id =>
    have hcm := J.connMor c
    rw [hCM, harity] at hcm
    exact dstFoldN SI J.Ω n ≫ I.monad.map hcm

/-- Companion of `def:kleisli-interpretation`: `⟦*(φ⃗)⟧` is the dedup'd
context routed to the formula list's semantics and then through `𝓘(*)`, up
to the transport along `[*(φ⃗)] = firstDedup([φ⃗])` and the constant-map
identity `map (fun _ => 𝓜Ω) φ⃗ = replicate |φ⃗| 𝓜Ω`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: Fm.sem's
-- compound clause, cast-free
theorem Fm.sem_conn_eq (K : KleisliInterpretation I SI J D) (c : sigB.Conn)
    (args : List (Fm sigG sigB)) (ht : (Fm.conn c args : Fm sigG sigB).KTyped)
    (harity : sigB.connArity c = args.length) (hargs : ∀ a ∈ args, a.KTyped) :
    Fm.sem K (.conn c args) ht
      = eqToHom (congrArg (ctxObj D) (Fm.on_conn c args)) ≫
        ctxCopy D (firstDedup (args.map Fm.on).flatten) (firstDedup_nodup _)
            (args.map Fm.on).flatten (fun _ hy => mem_firstDedup hy) ≫
        FmList.sem K args hargs ≫
        eqToHom (congrArg tensorList (List.map_const' (l := args) (b := I.monad.obj J.Ω))) ≫
        connMorAt SI J c args.length harity := by
  have hh : Fm.sem K (Fm.conn c args) ht
      ≍ ctxCopy D (firstDedup (args.map Fm.on).flatten) (firstDedup_nodup _)
            (args.map Fm.on).flatten (fun _ hy => mem_firstDedup hy) ≫
          FmList.sem K args hargs ≫
          eqToHom (congrArg tensorList (List.map_const' (l := args) (b := I.monad.obj J.Ω))) ≫
          connMorAt SI J c args.length harity := by
    rw [Fm.sem.eq_2]
    simp only [eq_mpr_eq_cast]
    refine (cast_heq _ _).trans ?_
    refine heq_of_eq ?_
    simp only [eq_mp_eq_cast]
    simp only [and_rec_proj]
    rw [cast_hom_cod _
        (congrArg tensorList (List.map_const' (l := args) (b := I.monad.obj J.Ω))),
      Category.assoc]
    rfl
  exact eq_of_heq (hh.trans (eqToHom_comp_heq _ _).symm)

/-- Companion of `def:kleisli-interpretation`: `𝓘(Q)_n` at whichever
marker the quantifier carries, the quantifier twin of `connMorAt`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- quantified clause's marker-dispatched quantifier morphism
def quanMorAt (SI : StrongCatInterpretation I) (J : LogInterpretation I sigB)
    (Q : sigB.Quan) (n : ℕ) :
    tensorList (List.replicate n (I.monad.obj J.Ω)) ⟶ I.monad.obj J.Ω := by
  match hQM : sigB.quanMonad Q with
  | .mon =>
    have hqm := J.quanMor Q n
    rw [hQM] at hqm
    exact hqm
  | .id =>
    have hqm := J.quanMor Q n
    rw [hQM] at hqm
    exact dstFoldN SI J.Ω n ≫ I.monad.map hqm

/-- Companion of `def:kleisli-interpretation`: `⟦Qx⃗(φ)⟧` is the remaining
context copied once per product state, each copy taking its own state
through `⟦φ⟧`, the results tensored and fed to `𝓘(Q)_N`, up to the transport
along `[Qx⃗(φ)] = [φ] ∖ x⃗`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: Fm.sem's
-- quantified clause, cast-free
theorem Fm.sem_quant_eq (K : KleisliInterpretation I SI J D) (Q : sigB.Quan)
    (xs : List sigG.Var) (body : Fm sigG sigB)
    (ht : (Fm.quant Q xs body : Fm sigG sigB).KTyped) (hbody : body.KTyped) :
    Fm.sem K (.quant Q xs body) ht
      = eqToHom (congrArg (ctxObj D) (Fm.on_quant Q xs body)) ≫
        comulN (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs))))
            (listCard K (body.on.filter (fun v => decide (v ∈ xs)))) ≫
        tensorFin (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs)))) (I.monad.obj J.Ω)
          (listCard K (body.on.filter (fun v => decide (v ∈ xs))))
          (fun i =>
            ((ρ_ (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs))))).inv ≫
                (𝟙 (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs)))) ⊗ₘ
                  listPt K (body.on.filter (fun v => decide (v ∈ xs))) i) ≫
                ctxMerge D (fun v => decide (v ∈ xs)) body.on) ≫
              Fm.sem K body hbody) ≫
        quanMorAt SI J Q (listCard K (body.on.filter (fun v => decide (v ∈ xs)))) := by
  have hh : Fm.sem K (Fm.quant Q xs body) ht
      ≍ comulN (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs))))
            (listCard K (body.on.filter (fun v => decide (v ∈ xs)))) ≫
          tensorFin (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs)))) (I.monad.obj J.Ω)
            (listCard K (body.on.filter (fun v => decide (v ∈ xs))))
            (fun i =>
              ((ρ_ (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs))))).inv ≫
                  (𝟙 (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs)))) ⊗ₘ
                    listPt K (body.on.filter (fun v => decide (v ∈ xs))) i) ≫
                  ctxMerge D (fun v => decide (v ∈ xs)) body.on) ≫
                Fm.sem K body hbody) ≫
          quanMorAt SI J Q (listCard K (body.on.filter (fun v => decide (v ∈ xs)))) := by
    rw [Fm.sem.eq_3]
    simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
    exact cast_heq _ _
  exact eq_of_heq (hh.trans (eqToHom_comp_heq _ _).symm)

/-- Companion of `def:kleisli-interpretation`: `⟦φ[x := ξ]⟧` is the term's
semantics tensored in at `x`'s own position and bound into the body's
semantics, up to the transport along `[φ[x := ξ]]`'s positional split. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: Fm.sem's
-- substituted clause, cast-free
theorem Fm.sem_subst_eq (K : KleisliInterpretation I SI J D) (body : Fm sigG sigB)
    (x : sigG.Var) (t : Tm sigG sigB) (ht : (Fm.subst body x t : Fm sigG sigB).KTyped)
    (hkcod : Tm.kcod t = [(MonSym.id, sigG.varOver x)]) (hocc : x ∈ body.on)
    (hbody : body.KTyped) (htt : t.KTyped) :
    Fm.sem K (.subst body x t) ht
      = eqToHom (congrArg (ctxObj D) (Fm.on_subst body x t)) ≫
        (ctxAppendIso D (body.on.takeWhile (fun v => decide (v ≠ x)))
            (t.inn ++ (body.on.dropWhile (fun v => decide (v ≠ x))).tail)).hom ≫
        (𝟙 (ctxObj D (body.on.takeWhile (fun v => decide (v ≠ x)))) ⊗ₘ
          (ctxAppendIso D t.inn (body.on.dropWhile (fun v => decide (v ≠ x))).tail).hom) ≫
        (𝟙 (ctxObj D (body.on.takeWhile (fun v => decide (v ≠ x)))) ⊗ₘ
          ((Tm.sem K t htt ≫
            I.monad.map (eqToHom (congrArg (interpretMS I D.domObj) hkcod) ≫
              (ρ_ (D.domObj (sigG.varOver x))).hom)) ⊗ₘ
            𝟙 (ctxObj D (body.on.dropWhile (fun v => decide (v ≠ x))).tail))) ≫
        (𝟙 (ctxObj D (body.on.takeWhile (fun v => decide (v ≠ x)))) ⊗ₘ SI.leftStrength) ≫
        SI.strength ≫
        I.monad.map
          ((ctxAppendIso D (body.on.takeWhile (fun v => decide (v ≠ x)))
                (x :: (body.on.dropWhile (fun v => decide (v ≠ x))).tail)).inv ≫
            eqToHom (congrArg (ctxObj D) (list_split_pre_post hocc))) ≫
        SI.bind (Fm.sem K body hbody) := by
  have hh : Fm.sem K (Fm.subst body x t) ht
      ≍ (ctxAppendIso D (body.on.takeWhile (fun v => decide (v ≠ x)))
            (t.inn ++ (body.on.dropWhile (fun v => decide (v ≠ x))).tail)).hom ≫
        (𝟙 (ctxObj D (body.on.takeWhile (fun v => decide (v ≠ x)))) ⊗ₘ
          (ctxAppendIso D t.inn (body.on.dropWhile (fun v => decide (v ≠ x))).tail).hom) ≫
        (𝟙 (ctxObj D (body.on.takeWhile (fun v => decide (v ≠ x)))) ⊗ₘ
          ((Tm.sem K t htt ≫
            I.monad.map (eqToHom (congrArg (interpretMS I D.domObj) hkcod) ≫
              (ρ_ (D.domObj (sigG.varOver x))).hom)) ⊗ₘ
            𝟙 (ctxObj D (body.on.dropWhile (fun v => decide (v ≠ x))).tail))) ≫
        (𝟙 (ctxObj D (body.on.takeWhile (fun v => decide (v ≠ x)))) ⊗ₘ SI.leftStrength) ≫
        SI.strength ≫
        I.monad.map
          ((ctxAppendIso D (body.on.takeWhile (fun v => decide (v ≠ x)))
                (x :: (body.on.dropWhile (fun v => decide (v ≠ x))).tail)).inv ≫
            eqToHom (congrArg (ctxObj D) (list_split_pre_post hocc))) ≫
        SI.bind (Fm.sem K body hbody) := by
    rw [Fm.sem.eq_4]
    simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
    refine (cast_heq _ _).trans ?_
    simp only [and_rec_proj]
    rw [cast_hom_cod _ (congrArg (fun l => I.monad.obj (interpretMS I D.domObj l)) hkcod)]
    refine heq_of_eq ?_
    simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  exact eq_of_heq (hh.trans (eqToHom_comp_heq _ _).symm)

end FmClauses

/-!
## The context machinery is compatible with a morphism of interpretations

The atomic, compound and quantified clauses of `Fm.sem` all route their
context through `copy` before consuming it, so the formula half needs the
whole of `def:kleisli-interpretation`'s insertion machinery to commute with
a morphism of interpretations. `ctxMor_comul` and `ctxMor_counit` are the
root of that: the induced morphism on a context's tensor is a comonoid
morphism, because each component is one (`domMor_comul`, `domMor_counit`)
and the chosen comonoid is compatible with the tensor (`comul_tensor`,
`counit_tensor`). `ctxProjFilter_compat`, `projTo_compat` and
`ctxCopy_compat` then carry that up through the three layers of the
machinery, in the order it is built.
-/

section ContextCompat

variable {SI₁ : StrongCatInterpretation I} {J₁ : LogInterpretation I sigB}
  {D₁ : DomInterpretation I J₁ sigG} {K₁ : KleisliInterpretation I SI₁ J₁ D₁}
  {SI₂ : StrongCatInterpretation (I.withMonad M₂)}
  {J₂ : LogInterpretation (I.withMonad M₂) sigB}
  {D₂ : DomInterpretation (I.withMonad M₂) J₂ sigG}
  {K₂ : KleisliInterpretation (I.withMonad M₂) SI₂ J₂ D₂}

/-- Companion of `def:interpretation-morphism`: the induced morphism on the
empty context is the identity of the tensor unit. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: ctxMor's
-- empty clause
theorem ctxMor_nil (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) :
    Φ.ctxMor [] = 𝟙 (𝟙_ I.cd.C) := rfl

/-- Companion of `def:interpretation-morphism`: the induced morphism on a
context splits off its head slot's own component. -/
@[blueprint_internal] -- companion of def:interpretation-morphism: ctxMor's
-- cons clause
theorem ctxMor_cons (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) (x : sigG.Var)
    (l : List sigG.Var) :
    Φ.ctxMor (x :: l) = Φ.domMor (sigG.varOver x) ⊗ₘ Φ.ctxMor l := rfl

/-- Companion of `def:kleisli-interpretation`: the induced morphism on a
context's tensor discards as the chosen counits do, by induction on the
context out of `domMor_counit` and `counit_tensor`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: ctxMor
-- respects the chosen counit
theorem ctxMor_counit (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) : ∀ l : List sigG.Var,
    Φ.ctxMor l ≫ (I.cd.comon (ctxObj (I := I.withMonad M₂) (J := J₂) D₂ l)).counit
      = (I.cd.comon (ctxObj D₁ l)).counit
  | [] => by
      change 𝟙 (𝟙_ I.cd.C) ≫ _ = _
      rw [Category.id_comp]
      rfl
  | x :: l' => by
      have tail_counit := ctxMor_counit Φ l'
      change (Φ.domMor (sigG.varOver x) ⊗ₘ Φ.ctxMor l') ≫
          (I.cd.comon (D₂.domObj (sigG.varOver x) ⊗
            ctxObj (I := I.withMonad M₂) (J := J₂) D₂ l')).counit
        = (I.cd.comon (D₁.domObj (sigG.varOver x) ⊗ ctxObj D₁ l')).counit
      rw (config := { transparency := .default })
        [Φ.counit_tensor, Φ.counit_tensor, ← Category.assoc,
          tensorHom_comp_tensorHom, Φ.domMor_counit, tail_counit]

/-- Companion of `def:kleisli-interpretation`: the induced morphism on a
context's tensor copies as the chosen comultiplications do, by induction on
the context out of `domMor_comul`, `comul_tensor` and naturality of the
shuffle. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: ctxMor
-- respects the chosen comultiplication
theorem ctxMor_comul (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) : ∀ l : List sigG.Var,
    Φ.ctxMor l ≫ (I.cd.comon (ctxObj (I := I.withMonad M₂) (J := J₂) D₂ l)).comul
      = (I.cd.comon (ctxObj D₁ l)).comul ≫ (Φ.ctxMor l ⊗ₘ Φ.ctxMor l)
  | [] => by
      change 𝟙 (𝟙_ I.cd.C) ≫ _ = _ ≫ (𝟙 (𝟙_ I.cd.C) ⊗ₘ 𝟙 (𝟙_ I.cd.C))
      rw [Category.id_comp, tensorHom_id, id_whiskerRight, Category.comp_id]
      rfl
  | x :: l' => by
      have tail_comul := ctxMor_comul Φ l'
      change (Φ.domMor (sigG.varOver x) ⊗ₘ Φ.ctxMor l') ≫
          (I.cd.comon (D₂.domObj (sigG.varOver x) ⊗
            ctxObj (I := I.withMonad M₂) (J := J₂) D₂ l')).comul
        = (I.cd.comon (D₁.domObj (sigG.varOver x) ⊗ ctxObj D₁ l')).comul ≫
          ((Φ.domMor (sigG.varOver x) ⊗ₘ Φ.ctxMor l') ⊗ₘ
            (Φ.domMor (sigG.varOver x) ⊗ₘ Φ.ctxMor l'))
      rw (config := { transparency := .default })
        [Φ.comul_tensor, Φ.comul_tensor, ← Category.assoc,
          tensorHom_comp_tensorHom, Φ.domMor_comul, tail_comul, ← tensorHom_comp_tensorHom,
          Category.assoc, tensorμ_natural, ← Category.assoc]

/-- Companion of `def:kleisli-interpretation`: the surviving-head clause of
`ctxProjFilter`, as a rewrite with its list transport made explicit. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- ctxProjFilter's surviving-head clause, cast-free
theorem ctxProjFilter_cons_pos {J : LogInterpretation I sigB} (D : DomInterpretation I J sigG)
    (p : sigG.Var → Bool) (y : sigG.Var) (l' : List sigG.Var) (hpy : p y = true) :
    ctxProjFilter D p (y :: l')
      = (𝟙 (D.domObj (sigG.varOver y)) ⊗ₘ ctxProjFilter D p l') ≫
        eqToHom (congrArg (ctxObj D) (List.filter_cons_of_pos hpy).symm) := by
  have hh : ctxProjFilter D p (y :: l')
      ≍ (𝟙 (D.domObj (sigG.varOver y)) ⊗ₘ ctxProjFilter D p l') := by
    rw [ctxProjFilter]
    split
    · dsimp only
      rw (config := { transparency := .default }) [eqRec_cod (ctxObj D)]
      exact comp_eqToHom_heq _ _
    · simp_all
  exact eq_of_heq (hh.trans (comp_eqToHom_heq _ _).symm)

/-- Companion of `def:kleisli-interpretation`: the discarded-head clause of
`ctxProjFilter`, as a rewrite with its list transport made explicit. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- ctxProjFilter's discarded-head clause, cast-free
theorem ctxProjFilter_cons_neg {J : LogInterpretation I sigB} (D : DomInterpretation I J sigG)
    (p : sigG.Var → Bool) (y : sigG.Var) (l' : List sigG.Var) (hpy : p y = false) :
    ctxProjFilter D p (y :: l')
      = ((I.cd.comon (D.domObj (sigG.varOver y))).counit ⊗ₘ ctxProjFilter D p l') ≫
        (λ_ (ctxObj D (l'.filter p))).hom ≫
        eqToHom (congrArg (ctxObj D)
          (List.filter_cons_of_neg (by simp [hpy]) : (y :: l').filter p = l'.filter p).symm) := by
  have hh : ctxProjFilter D p (y :: l')
      ≍ ((I.cd.comon (D.domObj (sigG.varOver y))).counit ⊗ₘ ctxProjFilter D p l') ≫
        (λ_ (ctxObj D (l'.filter p))).hom := by
    rw [ctxProjFilter]
    split
    · simp_all
    · dsimp only
      rw (config := { transparency := .default }) [eqRec_cod (ctxObj D)]
      exact comp_eqToHom_heq _ _
  exact eq_of_heq ((hh.trans (comp_eqToHom_heq _ _).symm).trans
    (heq_of_eq (Category.assoc _ _ _)))

/-- Companion of `def:kleisli-interpretation`: discarding the variables a
predicate rejects commutes with a morphism of interpretations, by induction
on the context. A surviving head is carried by its own component; a
discarded head is carried by `domMor_counit`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- ctxProjFilter against a morphism of interpretations
theorem ctxProjFilter_compat (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂)
    (p : sigG.Var → Bool) : ∀ l : List sigG.Var,
    Φ.ctxMor l ≫ ctxProjFilter (I := I.withMonad M₂) (J := J₂) D₂ p l
      = ctxProjFilter D₁ p l ≫ Φ.ctxMor (l.filter p)
  | [] => by
      change 𝟙 (𝟙_ I.cd.C) ≫ 𝟙 (𝟙_ I.cd.C) = 𝟙 (𝟙_ I.cd.C) ≫ 𝟙 (𝟙_ I.cd.C)
      rfl
  | y :: l' => by
      have tail_proj := ctxProjFilter_compat Φ p l'
      cases hpy : p y
      · rw [ctxProjFilter_cons_neg D₂ p y l' hpy, ctxProjFilter_cons_neg D₁ p y l' hpy,
          ctxMor_cons]
        rw (config := { transparency := .default })
          [Category.assoc, Category.assoc, ctxMor_eqToHom Φ
            (List.filter_cons_of_neg (by simp [hpy]) : (y :: l').filter p = l'.filter p).symm]
        conv_rhs => rw [← MonoidalCategory.leftUnitor_naturality_assoc, ← id_tensorHom]
        rw (config := { transparency := .default })
          [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, Φ.domMor_counit,
            tail_proj, Category.comp_id]
      · rw [ctxProjFilter_cons_pos D₂ p y l' hpy, ctxProjFilter_cons_pos D₁ p y l' hpy,
          ctxMor_cons]
        rw (config := { transparency := .default })
          [Category.assoc, ctxMor_eqToHom Φ (List.filter_cons_of_pos hpy).symm, ctxMor_cons]
        rw (config := { transparency := .default })
          [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, tail_proj,
            Category.comp_id, Category.id_comp]
        rfl

/-- Companion of `def:kleisli-interpretation`: projecting a context down to
one of its variables commutes with a morphism of interpretations, by
`ctxProjFilter_compat` and naturality of the right unitor. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: projTo
-- against a morphism of interpretations
theorem projTo_compat [DecidableEq sigG.Var] (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂)
    (l : List sigG.Var) (hnd : l.Nodup) (x : sigG.Var) (hx : x ∈ l) :
    Φ.ctxMor l ≫ projTo (I := I.withMonad M₂) (J := J₂) D₂ l hnd x hx
      = projTo D₁ l hnd x hx ≫ Φ.domMor (sigG.varOver x) := by
  rw [projTo, projTo]
  rw (config := { transparency := .default })
    [← Category.assoc, ctxProjFilter_compat Φ (fun v => decide (v = x)) l, Category.assoc,
      ← ctxMor_eqToHom_assoc Φ (filter_eq_singleton_of_nodup_mem hnd hx), ctxMor_cons, ctxMor_nil,
      tensorHom_id, MonoidalCategory.rightUnitor_naturality]
  simp only [Category.assoc]
  rfl

/-- Companion of `def:kleisli-interpretation`: routing a deduplicated
context to every position of a target list commutes with a morphism of
interpretations, by induction on the target list out of `ctxMor_comul` and
`projTo_compat`. This is what the atomic and compound clauses of `Fm.sem`
need, since both prepend `copy` to their argument list's semantics. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: ctxCopy
-- against a morphism of interpretations
theorem ctxCopy_compat [DecidableEq sigG.Var] (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂)
    (Dl : List sigG.Var) (hnd : Dl.Nodup) :
    ∀ (L : List sigG.Var) (hL : ∀ x ∈ L, x ∈ Dl),
      ctxCopy D₁ Dl hnd L hL ≫ Φ.ctxMor L
        = Φ.ctxMor Dl ≫ ctxCopy (I := I.withMonad M₂) (J := J₂) D₂ Dl hnd L hL
  | [], hL => by
      rw [ctxCopy, ctxCopy, ctxMor_nil, Category.assoc]
      rw (config := { transparency := .default })
        [Category.comp_id, ← Category.assoc, ctxProjFilter_compat Φ (fun _ => false) Dl,
          Category.assoc, ← ctxMor_eqToHom Φ (by simp : Dl.filter (fun _ => false) = []),
          ctxMor_nil, Category.comp_id]
  | x :: L', hL => by
      have tail_copy := ctxCopy_compat Φ Dl hnd L' (fun y hy => hL y (List.mem_cons_of_mem x hy))
      rw [ctxCopy, ctxCopy, ctxMor_cons]
      rw (config := { transparency := .default })
        [Category.assoc, tensorHom_comp_tensorHom, reassoc_of% (ctxMor_comul Φ Dl),
          tensorHom_comp_tensorHom, projTo_compat Φ Dl hnd x, ← tail_copy]
      rfl

end ContextCompat

/-!
## The marker dispatch is compatible with a morphism of interpretations

`Fm.sem`'s compound and quantified clauses read their symbol's monad
marker and dispatch on it. At `○` the symbol's morphism is applied as it
stands; at `Id` the `n` separately-monadic factors are first collapsed by
`dstFoldN` and the plain morphism is then applied inside the monad. The
`Id` branch was long reported unprovable, since `StrongCatInterpretation`
carries the strength as bare data. It goes through here because a morphism
of interpretations carries the two laws that branch needs:
`strength_compat` (through `dst_compat`) and `strength_natural` (through
`dst_natural`). `dstFoldN_compat` is where they are spent.

`markerAdapt` names the dispatch with the marker as an ordinary argument
rather than as the scrutinee of a dependent match, so that a case analysis
on it produces no transports at all. `connMorAt_eq` and `quanMorAt_eq`
identify `Fm.sem`'s own dispatch with it, and `markerAdapt_compat` then
proves the compatibility once for both.
-/

section MarkerCompat

variable {SI₁ : StrongCatInterpretation I} {J₁ : LogInterpretation I sigB}
  {D₁ : DomInterpretation I J₁ sigG} {K₁ : KleisliInterpretation I SI₁ J₁ D₁}
  {SI₂ : StrongCatInterpretation (I.withMonad M₂)}
  {J₂ : LogInterpretation (I.withMonad M₂) sigB}
  {D₂ : DomInterpretation (I.withMonad M₂) J₂ sigG}
  {K₂ : KleisliInterpretation (I.withMonad M₂) SI₂ J₂ D₂}

/-- Companion of `def:interpretation-morphism`: at `Id` the per-slot
transport is the morphism itself. -/
@[blueprint_internal] -- companion of def:interpretation-morphism:
-- markerMor's Id clause
theorem markerMor_id (θ : I.monad.toFunctor ⟶ M₂.toFunctor) {X₁ X₂ : I.cd.C} (g : X₁ ⟶ X₂) :
    markerMor θ MonSym.id g = g := rfl

/-- Companion of `def:interpretation-morphism`: at `○` the per-slot
transport is the monad morphism followed by `𝓜₂` of the morphism. -/
@[blueprint_internal] -- companion of def:interpretation-morphism:
-- markerMor's ○ clause
theorem markerMor_mon (θ : I.monad.toFunctor ⟶ M₂.toFunctor) {X₁ X₂ : I.cd.C} (g : X₁ ⟶ X₂) :
    markerMor θ MonSym.mon g = θ.app X₁ ≫ M₂.map g := rfl

/-- Companion of `def:kleisli-interpretation`: the `n`-ary strength
collapse commutes with a morphism of interpretations, by induction on the
arity. The unit case is the monad morphism's unit law. The step case
spends `dst_compat` and then naturality of the target double strength,
which is where `strength_natural` earns its place in the bundle. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: dstFoldN
-- against a morphism of interpretations
theorem dstFoldN_compat (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) {X₁ X₂ : I.cd.C}
    (g : X₁ ⟶ X₂) : ∀ n : ℕ,
    dstFoldN SI₁ X₁ n ≫ Φ.monadMor.app (tensorList (List.replicate n X₁)) ≫
        M₂.map (interpretPowMor Φ.monadMor.toNatTrans g MonSym.id n)
      = interpretPowMor Φ.monadMor.toNatTrans g MonSym.mon n ≫ dstFoldN SI₂ X₂ n
  | 0 => by
      change I.monad.η.app (𝟙_ I.cd.C) ≫ Φ.monadMor.app (𝟙_ I.cd.C) ≫ M₂.map (𝟙 (𝟙_ I.cd.C))
          = 𝟙 (𝟙_ I.cd.C) ≫ M₂.η.app (𝟙_ I.cd.C)
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      exact Φ.monadMor.app_η _
  | n + 1 => by
      have tail_collapse := dstFoldN_compat Φ g n
      change ((𝟙 (I.monad.obj X₁) ⊗ₘ dstFoldN SI₁ X₁ n) ≫ SI₁.dst) ≫ _ ≫
          M₂.map (markerMor Φ.monadMor.toNatTrans MonSym.id g ⊗ₘ
            interpretPowMor Φ.monadMor.toNatTrans g MonSym.id n)
        = (markerMor Φ.monadMor.toNatTrans MonSym.mon g ⊗ₘ
            interpretPowMor Φ.monadMor.toNatTrans g MonSym.mon n) ≫
          ((𝟙 (M₂.obj X₂) ⊗ₘ dstFoldN SI₂ X₂ n) ≫ SI₂.dst)
      rw (config := { transparency := .default })
        [markerMor_id, markerMor_mon, Category.assoc, reassoc_of% Φ.dst_compat,
          ← StrongCatInterpretation.dst_natural SI₂ Φ.strength_natural g
            (interpretPowMor Φ.monadMor.toNatTrans g MonSym.id n),
          ← Category.assoc (𝟙 (I.monad.obj X₁) ⊗ₘ dstFoldN SI₁ X₁ n), tensorHom_comp_tensorHom]
      rw (config := { transparency := .default })
        [tensorHom_comp_tensorHom_assoc, Category.assoc, Category.assoc, tail_collapse,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      rfl

/-- Companion of `def:kleisli-interpretation`: the marker dispatch of
`Fm.sem`'s compound and quantified clauses, written with the marker as an
ordinary argument. A case analysis on that argument produces no
transports, which is what makes the compatibility below provable at all. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- marker dispatch, with the marker as an argument rather than a scrutinee
def markerAdapt (SI : StrongCatInterpretation I) (X : I.cd.C) :
    (m : MonSym) → (n : ℕ) → (interpretPow I X m n ⟶ (I.interpretMon m).obj X) →
      (tensorList (List.replicate n (I.monad.obj X)) ⟶ I.monad.obj X)
  | .mon, _, g => g
  | .id, n, g => dstFoldN SI X n ≫ I.monad.map g

/-- Companion of `def:kleisli-interpretation`: at `○` the dispatch applies
the morphism as it stands. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- markerAdapt's ○ clause
theorem markerAdapt_mon (SI : StrongCatInterpretation I) (X : I.cd.C) (n : ℕ)
    (g : interpretPow I X MonSym.mon n ⟶ (I.interpretMon MonSym.mon).obj X) :
    markerAdapt SI X MonSym.mon n g = g := rfl

/-- Companion of `def:kleisli-interpretation`: at `Id` the dispatch first
collapses the `n` separately-monadic factors, then applies the morphism
inside the monad. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- markerAdapt's Id clause
theorem markerAdapt_id (SI : StrongCatInterpretation I) (X : I.cd.C) (n : ℕ)
    (g : interpretPow I X MonSym.id n ⟶ (I.interpretMon MonSym.id).obj X) :
    markerAdapt SI X MonSym.id n g = dstFoldN SI X n ≫ I.monad.map g := rfl

/-- Companion of `def:kleisli-interpretation`: transporting the morphism
along a marker equation and dispatching at the transported marker is
dispatching at the original one. This is what identifies `Fm.sem`'s own
dependent marker match with `markerAdapt`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- markerAdapt against a marker transport
theorem markerAdapt_cast (SI : StrongCatInterpretation I) (X : I.cd.C) (n : ℕ)
    {m m' : MonSym} (h : m = m')
    (g : interpretPow I X m n ⟶ (I.interpretMon m).obj X) :
    markerAdapt SI X m' n
        (cast (congrArg (fun mm => interpretPow I X mm n ⟶ (I.interpretMon mm).obj X) h) g)
      = markerAdapt SI X m n g := by
  cases h; rfl

/-- Companion of `def:kleisli-interpretation`: the quantified clause's
marker dispatch is `markerAdapt` at the quantifier's own marker. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- quanMorAt through markerAdapt
theorem quanMorAt_eq (SI : StrongCatInterpretation I) (J : LogInterpretation I sigB)
    (Q : sigB.Quan) (n : ℕ) :
    quanMorAt SI J Q n = markerAdapt SI J.Ω (sigB.quanMonad Q) n (J.quanMor Q n) := by
  rw [quanMorAt]
  split
  · rename_i hQM
    rw [← markerAdapt_cast SI J.Ω n hQM (J.quanMor Q n), markerAdapt_mon]
    rfl
  · rename_i hQM
    rw [← markerAdapt_cast SI J.Ω n hQM (J.quanMor Q n), markerAdapt_id]
    rfl

/-- Companion of `def:kleisli-interpretation`: the marker dispatch commutes
with a morphism of interpretations, given that the dispatched morphisms do.
At `○` this is the given compatibility itself. At `Id` it is naturality of
the monad morphism, the given compatibility, and `dstFoldN_compat`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- markerAdapt against a morphism of interpretations
theorem markerAdapt_compat (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) (m : MonSym) (n : ℕ)
    (g₁ : interpretPow I J₁.Ω m n ⟶ (I.interpretMon m).obj J₁.Ω)
    (g₂ : interpretPow (I.withMonad M₂) J₂.Ω m n ⟶
      ((I.withMonad M₂).interpretMon m).obj J₂.Ω)
    (hg : g₁ ≫ markerMor Φ.monadMor.toNatTrans m Φ.omegaMor
      = interpretPowMor Φ.monadMor.toNatTrans Φ.omegaMor m n ≫ g₂) :
    markerAdapt SI₁ J₁.Ω m n g₁ ≫ Φ.monadMor.app J₁.Ω ≫ M₂.map Φ.omegaMor
      = interpretPowMor Φ.monadMor.toNatTrans Φ.omegaMor MonSym.mon n ≫
        markerAdapt SI₂ J₂.Ω m n g₂ := by
  cases m with
  | mon => exact hg
  | id =>
      rw [markerAdapt_id, markerAdapt_id, markerMor_id] at *
      rw (config := { transparency := .default })
        [Category.assoc, Φ.monadMor.toNatTrans.naturality_assoc, ← CategoryTheory.Functor.map_comp,
          hg, CategoryTheory.Functor.map_comp, reassoc_of% (dstFoldN_compat Φ Φ.omegaMor n),
          Category.assoc]
      rfl

/-- Companion of `def:kleisli-interpretation`: the compound clause's marker
dispatch is `markerAdapt` at the connective's own marker, once its arity is
transported to the argument list's length. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation:
-- connMorAt through markerAdapt
theorem connMorAt_eq (SI : StrongCatInterpretation I) (J : LogInterpretation I sigB)
    (c : sigB.Conn) (n : ℕ) (harity : sigB.connArity c = n) :
    connMorAt SI J c n harity
      = markerAdapt SI J.Ω (sigB.connMonad c) n
          (eqToHom (congrArg (fun k => interpretPow I J.Ω (sigB.connMonad c) k) harity.symm) ≫
            J.connMor c) := by
  subst harity
  simp only [eqToHom_refl, Category.id_comp]
  rw [connMorAt]
  split
  · rename_i hCM
    rw [← markerAdapt_cast SI J.Ω _ hCM (J.connMor c), markerAdapt_mon]
    rfl
  · rename_i hCM
    rw [← markerAdapt_cast SI J.Ω _ hCM (J.connMor c), markerAdapt_id]
    rfl

/-- Companion of `def:kleisli-interpretation`: the compound clause's
connective morphism commutes with a morphism of interpretations, by
`markerAdapt_compat` at `connMor_compat`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- compound clause's connective morphism against a morphism of
-- interpretations
theorem connMorAt_compat (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) (c : sigB.Conn) (n : ℕ)
    (harity : sigB.connArity c = n) :
    connMorAt SI₁ J₁ c n harity ≫ Φ.monadMor.app J₁.Ω ≫ M₂.map Φ.omegaMor
      = interpretPowMor Φ.monadMor.toNatTrans Φ.omegaMor MonSym.mon n ≫
        connMorAt SI₂ J₂ c n harity := by
  subst harity
  rw [connMorAt_eq, connMorAt_eq]
  simp only [eqToHom_refl, Category.id_comp]
  exact markerAdapt_compat Φ (sigB.connMonad c) (sigB.connArity c) (J₁.connMor c) (J₂.connMor c)
    (Φ.connMor_compat c)

/-- Companion of `def:kleisli-interpretation`: the quantified clause's
quantifier morphism commutes with a morphism of interpretations, by
`markerAdapt_compat` at `quanMor_compat`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- quantified clause's quantifier morphism against a morphism of
-- interpretations
theorem quanMorAt_compat (Φ : InterpretationMorphism SI₁ K₁ SI₂ K₂) (Q : sigB.Quan) (n : ℕ) :
    quanMorAt SI₁ J₁ Q n ≫ Φ.monadMor.app J₁.Ω ≫ M₂.map Φ.omegaMor
      = interpretPowMor Φ.monadMor.toNatTrans Φ.omegaMor MonSym.mon n ≫
        quanMorAt SI₂ J₂ Q n := by
  rw [quanMorAt_eq, quanMorAt_eq]
  exact markerAdapt_compat Φ (sigB.quanMonad Q) n (J₁.quanMor Q n) (J₂.quanMor Q n)
    (Φ.quanMor_compat Q n)

end MarkerCompat

-- (completeness census, same pattern as `Tm.KTyped.eq_def` in
-- `NeSyCat/GrammaticalLayer/Kleisli.lean`: equation-lemma and congruence
-- byproducts of `Tm.sem`/`TmList.sem`, generated in this module by the
-- clause lemmas above and by the cons step's `simp only [TmList.sem]`,
-- with no attribute site of their own, tagged post-hoc -- not
-- blueprint-cited, plumbing of the two semantics functions)
attribute [blueprint_internal] Tm.sem.eq_def TmList.sem.eq_def Tm.sem.congr_simp
  TmList.sem.congr_simp Fm.sem.eq_def Fm.sem.congr_simp FmList.sem.congr_simp
  ctxCopy.congr_simp connMorAt.congr_simp projTo.congr_simp ctxProjFilter.eq_def
  ctxCopy.eq_def

-- (step correspondence, C3-ISAR: a mutual block compiles each of its two
-- theorems to a proof term that mentions only the compiler's own bundle
-- `<name>._f`, so `scripts/blueprint.sh`'s step scan, which closes over
-- used constants through `@[blueprint_internal]` companions, sees no
-- lemma of the actual proof until the bundles carry the tag themselves.
-- They are blueprint-internal in the plain sense of the word: generated
-- plumbing of these two proofs, cited by nothing.)
attribute [blueprint_internal] Tm.sem_natural._f TmList.sem_natural._f

end NeSyCat
