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

-- (completeness census, same pattern as `Tm.KTyped.eq_def` in
-- `NeSyCat/GrammaticalLayer/Kleisli.lean`: equation-lemma and congruence
-- byproducts of `Tm.sem`/`TmList.sem`, generated in this module by the
-- clause lemmas above and by the cons step's `simp only [TmList.sem]`,
-- with no attribute site of their own, tagged post-hoc -- not
-- blueprint-cited, plumbing of the two semantics functions)
attribute [blueprint_internal] Tm.sem.eq_def TmList.sem.eq_def Tm.sem.congr_simp
  TmList.sem.congr_simp

-- (step correspondence, C3-ISAR: a mutual block compiles each of its two
-- theorems to a proof term that mentions only the compiler's own bundle
-- `<name>._f`, so `scripts/blueprint.sh`'s step scan, which closes over
-- used constants through `@[blueprint_internal]` companions, sees no
-- lemma of the actual proof until the bundles carry the tag themselves.
-- They are blueprint-internal in the plain sense of the word: generated
-- plumbing of these two proofs, cited by nothing.)
attribute [blueprint_internal] Tm.sem_natural._f TmList.sem_natural._f

end NeSyCat
