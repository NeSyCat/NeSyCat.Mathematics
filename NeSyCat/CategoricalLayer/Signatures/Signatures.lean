/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr

/-!
# Categorical signatures and CD semantics

Blueprint items `def:categorical-signature`, `def:cd-category`,
`def:categorical-interpretation` (`blueprint/src/content.tex`, §"Categorical
signatures and CD semantics", `NeSyCat Theory v2`, `new.tex` 1--396) — the
theory's outermost signature/interpretation layer: a categorical signature
names a category symbol, an actor symbol, and a monad symbol; a CD
(copy-discard) category is a symmetric monoidal category with a chosen
commutative comonoid on every object, compatible with the tensor; a
categorical interpretation assigns a CD category, a monoidal actor category
acting on it, and a monad to a categorical signature's three symbols.

Mathlib has no bundled copy-discard/Markov category class, but it does carry
the ingredients: `CategoryTheory.SymmetricCategory` and per-object comonoids
`CategoryTheory.ComonObj X` (`Mathlib.CategoryTheory.Monoidal.Comon_`) with
`CategoryTheory.IsCommComonObj X` (`Mathlib.CategoryTheory.Monoidal.CommComon_`).
`CDCategory` below reuses these (encoding route (a) of the C3-B1/B2 LEAD
pin): a `CDCategory` bundles `[Category C] [MonoidalCategory C]
[SymmetricCategory C]`, a chosen `ComonObj X` and `IsCommComonObj X` for
every object `X`, and the tensor-compatibility the environment states —
`comon (X ⊗ Y)` agrees with the comonoid Mathlib's own
`instance : ComonObj A → ComonObj B → ComonObj (A ⊗ B)` induces from
`comon X`/`comon Y` — as the two Prop fields `copy_tensor`/`del_tensor`.

The actegory action `⋉ : 𝒜 × 𝒞 → 𝒞` of `def:categorical-interpretation` is
stated in the blueprint as a bare function on objects, with no coherence
square written down anywhere in that environment (confirmed against
`def:domain-interpretation`, the one place it is later used: there it
appears only as an object map `I(Θ) ⋉ I(MS)`, never applied to a
morphism). `CatInterpretation.act` below is accordingly a plain function
`A → cd.C → cd.C`, with no functoriality/coherence fields — adding any
would be a law the document does not state, which the C3-B1/B2 encoding
pins rule out.
-/

open CategoryTheory MonoidalCategory

universe u u' v v'

namespace NeSyCat

/-- Companion of `def:categorical-signature` (the `Mon := {Id, ○}` notation)
and of `def:categorical-interpretation` (`CatInterpretation.interpretMon`
below quantifies over it): a code for the two-element set of monad
symbols, the implicit identity symbol `Id` and the signature's own named
monad symbol `○`. -/
@[blueprint_internal] -- companion code (codes doctrine) for `Mon := {Id, ○}`
inductive MonSym where
  | id
  | mon
  deriving DecidableEq, Repr

-- (completeness census, same pattern as `BoolW` in
-- `NeSyCat/CategoricalLayer/SemiringMonads/LatticeSemiring.lean`:
-- `deriving`-synthesized declarations carry no attribute site of their own,
-- so they are tagged post-hoc -- not blueprint-cited, plumbing of `MonSym`)
attribute [blueprint_internal] MonSym.toCtorIdx MonSym.ofNat MonSym.ofNat_ctorIdx
  MonSym.ctorElimType instDecidableEqMonSym instReprMonSym instReprMonSym.repr

/-- Blueprint `def:categorical-signature` (Categorical signature): a
categorical signature `Σ_α` consists of a category symbol `C`, an actor
symbol `A`, and a monad symbol `○`. Each symbol is a bare name (pure data,
no internal structure): a categorical signature fixes only how many
symbols of each kind there are and how they will later be looked up by an
interpretation, never their meaning. -/
structure CatSignature where
  /-- The category symbol `C`. -/
  catSymbol : String
  /-- The actor symbol `A`. -/
  actorSymbol : String
  /-- The monad symbol `○`. -/
  monadSymbol : String
  deriving DecidableEq, Repr

-- (completeness census, same pattern as above) `deriving`-synthesized
-- declarations for `CatSignature`, not blueprint-cited.
attribute [blueprint_internal] instDecidableEqCatSignature instDecidableEqCatSignature.decEq
  instReprCatSignature instReprCatSignature.repr

/-- Blueprint `def:cd-category` (CD category): a CD (copy-discard) category
`(𝒞, ⊠_𝒞, I_𝒞, copy, del)` is a symmetric monoidal category equipped with a
commutative comonoid `copy_X : X → X ⊠_𝒞 X`, `del_X : X → I_𝒞` on every
object `X`, compatible with `⊠_𝒞`. `comon`/`comm` supply the commutative
comonoid on every object (`copy := ComonObj.comul`, `del := ComonObj.counit`
under `comon`); `copy_tensor`/`del_tensor` state the tensor-compatibility:
the chosen comonoid on `X ⊠_𝒞 Y` agrees with the one Mathlib's own
`ComonObj (A ⊗ B)` instance induces from the chosen comonoids on `X` and
`Y`. -/
structure CDCategory where
  /-- The category symbol's interpretation, the CD category's carrier. -/
  C : Type u
  [instCat : Category.{v} C]
  [instMonoidal : MonoidalCategory C]
  [instSymmetric : SymmetricCategory C]
  /-- The chosen commutative comonoid `(copy_X, del_X)` on every object. -/
  comon : ∀ X : C, ComonObj X
  /-- Commutativity of the chosen comonoid on every object. -/
  comm : ∀ X : C, letI := comon X; IsCommComonObj X
  /-- `copy` is compatible with `⊠_𝒞`: the chosen comultiplication on
  `X ⊠_𝒞 Y` agrees with the one induced from `X`'s and `Y`'s. -/
  copy_tensor : ∀ X Y : C, letI := comon X; letI := comon Y;
    (comon (X ⊗ Y)).comul = ComonObj.comul (X := X ⊗ Y)
  /-- `del` is compatible with `⊠_𝒞`: the chosen counit on `X ⊠_𝒞 Y` agrees
  with the one induced from `X`'s and `Y`'s. -/
  del_tensor : ∀ X Y : C, letI := comon X; letI := comon Y;
    (comon (X ⊗ Y)).counit = ComonObj.counit (X := X ⊗ Y)

/-- Blueprint `def:categorical-interpretation` (Categorical interpretation):
a categorical interpretation `𝓘_α` of a categorical signature `Σ_α` is
given by a CD category
`𝓘(C)` for the category symbol, a monoidal category `𝓘(A)` for the actor
symbol acting on `𝓘(C)` as an actegory with action `⋉ : A × C → C`, and a
monad `ℳ := 𝓘(○)` on `𝓘(C)` for the monad symbol. -/
structure CatInterpretation (sigA : CatSignature) where
  /-- The interpretation `𝓘(C)` of the category symbol, a CD category. -/
  cd : CDCategory.{u, v}
  /-- The interpretation `𝓘(A)` of the actor symbol, a monoidal category. -/
  A : Type u'
  [instCatA : Category.{v'} A]
  [instMonoidalA : MonoidalCategory A]
  /-- The actegory action `⋉ : A × C → C` of `𝓘(A)` on `𝓘(C)`. -/
  act : A → cd.C → cd.C
  /-- The monad `ℳ := 𝓘(○)` on `𝓘(C)`, the interpretation of the monad
  symbol `○`. -/
  monad : letI := cd.instCat; CategoryTheory.Monad cd.C

/-- Companion of `def:categorical-interpretation`'s closing sentence: "The
identity monad symbol `Id` is always interpreted by the identity functor on
`C`." Interprets a monad symbol as an endofunctor of `cd.C`, sending
`MonSym.id` to the identity functor and `MonSym.mon` to the underlying
functor of `ℳ := 𝓘(○)` — a definitional clause (true by construction, `Id`
needs no separate law), not new data. -/
@[blueprint_internal] -- definitional companion of def:categorical-interpretation
def CatInterpretation.interpretMon {sigA : CatSignature} (I : CatInterpretation sigA) :
    letI := I.cd.instCat; MonSym → (I.cd.C ⥤ I.cd.C) :=
  letI := I.cd.instCat
  fun
  | .id => 𝟭 I.cd.C
  | .mon => I.monad.toFunctor

end NeSyCat
