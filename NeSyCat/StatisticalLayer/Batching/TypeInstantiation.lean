/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.Signatures.Signatures
import NeSyCat.StatisticalLayer.Batching.BatchTransformer

/-!
# The concrete instantiation substrate at `Type` (C4-T1)

Scaffolding toward `thm:pointwise-eval-kleisli`
(`blueprint/src/content.tex`, §"Batching"): the abstract apparatus of
`def:cd-category`/`def:categorical-interpretation` instantiated
concretely at `Set`, plus the canonical strength on a lawful `Type`-monad
and the categorical-monad-morphism reading of `ev_i`. NOT the theorem
itself: `thm:pointwise-eval-kleisli` needs a further mutual-induction
argument over `Fm.sem`/`Tm.sem`'s six clauses (see
`PointwiseKleisli.lean`'s module doc) that this file does not attempt.

**Universe restriction (disclosed).** `CategoryTheory.ofTypeMonad`
(`Mathlib.CategoryTheory.Monad.Types`) converts a lawful Lean `Monad m`
into a `CategoryTheory.Monad` only for `m : Type u → Type u` (a
`Type`-endofunctor, not `Type u → Type v`). `BatchTransformer.lean`'s own
`BmonT B M := ReaderT (Fin B) M` is declared for `M : Type → Type*`
generally, but `Fin B : Type 0` pins the reader index to the bottom
universe, so `BmonT B M : Type 0 → Type u` needs `M`'s own codomain at
`u = 0` for `BmonT B M` itself to land back in `Type 0 → Type 0` and so
qualify for `ofTypeMonad`. This file therefore works throughout at
`M : Type → Type` (the codomain `Type 0`), not the library's general
`M : Type → Type*`. `MS S` (`NeSyCat/CategoricalLayer/SemiringMonads/SemiringMonad.lean`)
is defined for `X : Type*` and specializes to `Type → Type` at
`X : Type`, and since C4-MONAD it also carries the Lean
`Monad`/`LawfulMonad` instances `instMonadMS`/`instLawfulMonadMS`
(registered over the library's own `ret`/`bind`, with the three
obligations discharged from `semiring_monad_laws`), so
`ofTypeMonad (MS S)` typechecks and this file's substrate reaches the
library's own monad. `Idmon`, the identity-monad clause the
blueprint prose names alongside `MS S`, has no separate Lean object in
this library (`TruthSpace.lean`'s module doc: "no Lean object" needed,
the identity case is definitionally trivial); read as Lean core's own
`Id : Type u → Type u` (`Id α := α`, with a registered
`Monad`/`LawfulMonad Id` instance), it DOES satisfy this file's
`M : Type → Type` restriction outright, at every universe including
`u = 0`.
-/

open CategoryTheory MonoidalCategory

namespace NeSyCat

universe u

/-! ### The Type category as a CD category -/

/-- Blueprint `def:type-cd-category` (Set as a CD category): `Type u`,
cartesian monoidal and symmetric via Mathlib's own
`typesCartesianMonoidalCategory`/
`CartesianMonoidalCategory.toSymmetricCategory`, is a `CDCategory`
(`def:cd-category`) with the diagonal comonoid on every object
(`CartesianCopyDiscard.instComonObjOfCartesian`/`instIsCommComonObjOfCartesian`)
and tensor-compatibility discharged by the generic cartesian-to-copy-discard
bridge `CartesianCopyDiscard.ofCartesianMonoidalCategory` together with
`CopyDiscardCategory.copy_tensor`/`discard_tensor`. Toward
`thm:pointwise-eval-kleisli`: the first piece of the concrete instantiation
substrate at `Type`. -/
noncomputable def typeCD : NeSyCat.CDCategory.{u+1,u} where
  C := Type u
  comon := fun X => CartesianCopyDiscard.instComonObjOfCartesian X
  comm := fun X => CartesianCopyDiscard.instIsCommComonObjOfCartesian X
  copy_tensor := fun X Y => by
    letI := CartesianCopyDiscard.instComonObjOfCartesian X
    letI := CartesianCopyDiscard.instComonObjOfCartesian Y
    letI : CopyDiscardCategory (Type u) := CartesianCopyDiscard.ofCartesianMonoidalCategory
    rw [CopyDiscardCategory.copy_tensor (C := Type u) X Y]
  del_tensor := fun X Y => by
    letI := CartesianCopyDiscard.instComonObjOfCartesian X
    letI := CartesianCopyDiscard.instComonObjOfCartesian Y
    letI : CopyDiscardCategory (Type u) := CartesianCopyDiscard.ofCartesianMonoidalCategory
    rw [CopyDiscardCategory.discard_tensor (C := Type u) X Y]

/-! ### The canonical strength on a lawful `Type`-monad -/

variable {M : Type u → Type u} [Monad M]

/-- Blueprint `def:type-strength` (Canonical strength): the canonical
(tensorial) left strength of a `Type`-valued monad `M` with respect to the
cartesian product, inserting one pure value `p.1` alongside an
`M`-effectful one `p.2`. Toward `thm:pointwise-eval-kleisli`. -/
def typeStrength {X Y : Type u} (p : X × M Y) : M (X × Y) :=
  p.2 >>= fun y => pure (p.1, y)

variable [LawfulMonad M]

/-- Blueprint `lem:type-strength-laws` (naturality in the pure slot):
`typeStrength` commutes with remapping the pure coordinate along `f`
first or last. -/
theorem typeStrength_naturality_left {X X' Y : Type u} (f : X → X') (x : X) (my : M Y) :
    typeStrength (f x, my) = Prod.map f id <$> typeStrength (x, my) := by
  simp [typeStrength]

-- (A1 bijection-law companion of `typeStrength_naturality_left`,
-- content.tex lem:type-strength-laws)
@[blueprint_internal]
theorem typeStrength_naturality_right {X Y Y' : Type u} (g : Y → Y') (x : X) (my : M Y) :
    typeStrength (x, g <$> my) = Prod.map id g <$> typeStrength (x, my) := by
  simp [typeStrength]

-- (A1 bijection-law companion of `typeStrength_naturality_left`,
-- content.tex lem:type-strength-laws)
@[blueprint_internal]
theorem typeStrength_unit {X Y : Type u} (x : X) (y : Y) :
    typeStrength (x, (pure y : M Y)) = pure (x, y) := by
  simp [typeStrength]

-- (A1 bijection-law companion of `typeStrength_naturality_left`,
-- content.tex lem:type-strength-laws)
@[blueprint_internal]
theorem typeStrength_assoc {X Y : Type u} (x : X) (mmy : M (M Y)) :
    typeStrength (x, mmy >>= id) =
      typeStrength (x, mmy) >>= fun p => typeStrength (p.1, p.2) := by
  simp [typeStrength]

-- (A1 bijection-law companion of `typeStrength_naturality_left`,
-- content.tex lem:type-strength-laws)
@[blueprint_internal]
theorem typeStrength_left_unitor {Y : Type u} (my : M Y) :
    (fun p : PUnit.{u+1} × Y => p.2) <$> typeStrength ((PUnit.unit : PUnit.{u+1}), my) = my := by
  simp [typeStrength]

-- (A1 bijection-law companion of `typeStrength_naturality_left`,
-- content.tex lem:type-strength-laws)
@[blueprint_internal]
theorem typeStrength_assoc_coherence {X X' Y : Type u} (x : X) (x' : X') (my : M Y) :
    (fun p : (X × X') × Y => (p.1.1, (p.1.2, p.2))) <$> typeStrength ((x, x'), my) =
      typeStrength (x, typeStrength (x', my)) := by
  simp [typeStrength]

/-! ### A `CatInterpretation` at `Type` -/

/-- Blueprint `def:type-cat-interpretation` (A categorical interpretation at
Set): a `def:categorical-interpretation` witness at `typeCD` (specialized
to `Type 0`), for a lawful `M : Type → Type` — `𝓘(C) := typeCD`, the actor
category `𝓘(A)` taken as `Type` itself acting on `typeCD.C` by its own
cartesian product, and the monad `ℳ := 𝓘(○)` realized as
`CategoryTheory.ofTypeMonad M` (`Mathlib.CategoryTheory.Monad.Types`,
background machinery converting a lawful Lean `Monad` into a categorical
`Monad`). Toward `thm:pointwise-eval-kleisli`. -/
noncomputable def typeCatInterpretation (sigA : CatSignature)
    (M : Type → Type) [Monad M] [LawfulMonad M] : NeSyCat.CatInterpretation sigA where
  cd := typeCD.{0}
  A := Type
  act := fun a x => a × x
  monad := CategoryTheory.ofTypeMonad M

/-! ### `ev i` as a categorical monad morphism -/

variable {B : ℕ} {M' : Type → Type} [Monad M'] [LawfulMonad M']

/-- Blueprint `def:ev-monad-hom` (`ev i` as a monad morphism): `ev i`
(`thm:pointwise-eval`), read categorically at `typeCatInterpretation`'s
realization, is a `CategoryTheory.MonadHom` from `ofTypeMonad
(BmonT B M')` to `ofTypeMonad M'` — the two law fields `app_η`/`app_μ`
of `MonadHom` correspond exactly to the two clauses of
`ev_isMonadMorphism`: `app_η` is the unit clause (`rfl`, `ofTypeMonad`'s
unit is `pure`), `app_μ` is the bind clause read at `join`, closing by
`bind_assoc`/`pure_bind` once `ev_isMonadMorphism`'s own clauses are
applied. Naturality of the underlying transformation is `ReaderT`'s own
`run_map`. Toward `thm:pointwise-eval-kleisli`. -/
noncomputable def evMonadHom (i : Fin B) :
    CategoryTheory.MonadHom (CategoryTheory.ofTypeMonad (BmonT B M'))
      (CategoryTheory.ofTypeMonad M') where
  app X := TypeCat.ofHom (fun m => ev i m)
  naturality X Y f := by
    refine ConcreteCategory.hom_ext _ _ fun m => ?_
    simp only [CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom]
    change ev i (f <$> m) = f <$> ev i m
    exact ReaderT.run_map _ m i
  app_η X := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    simp only [CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom, ofTypeMonad_η_app]
    rfl
  app_μ X := by
    refine ConcreteCategory.hom_ext _ _ fun mm => ?_
    simp only [CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom, ofTypeMonad_μ_app]
    change ev i (joinM mm) = joinM (ev i ((fun m => ev i m) <$> mm))
    simp only [joinM, map_eq_pure_bind]
    set mm2 : BmonT B M' (BmonT B M' X) := mm with hmm2
    have hbind1 : ev i (mm2 >>= id) = ev i mm2 >>= fun x => ev i (id x) :=
      (ev_isMonadMorphism (B := B) (M := M') (X := BmonT B M' X) (Y := X) i).2 mm2
        (id : BmonT B M' X → BmonT B M' X)
    have hbind2 : ev i (mm2 >>= fun a => pure (ev i a)) =
        ev i mm2 >>= fun a => ev i (pure (ev i a) : BmonT B M' (M' X)) :=
      (ev_isMonadMorphism (B := B) (M := M') (X := BmonT B M' X) (Y := M' X) i).2 mm2
        (fun a => pure (ev i a))
    have hpure : ∀ v : M' X, ev i (pure v : BmonT B M' (M' X)) = pure v :=
      fun v => (ev_isMonadMorphism (B := B) (M := M') (X := M' X) (Y := X) i).1 v
    rw [hbind1, hbind2]
    simp only [id_eq, hpure, bind_assoc, pure_bind]

/-! ### `ev` commutes with the canonical strength -/

omit [LawfulMonad M'] in
/-- Blueprint `lem:ev-strength-natural` (`ev i` commutes with strength):
`ev i` commutes with the canonical strength (`typeStrength`) across `M'`
and its batch transform `BmonT B M'` — the pure coordinate rides along
untouched, whether it is inserted before or after evaluating at index `i`.
Needs no lawfulness of `M'` at all: `typeStrength` unfolds to `ReaderT`'s
own bind, and `ev i` is literally indexing at `i`, so both sides reduce
definitionally through `ReaderT.run_bind`. Toward
`thm:pointwise-eval-kleisli`. -/
theorem ev_strength_natural (i : Fin B) {X' Y' : Type} (x : X') (bm : BmonT B M' Y') :
    ev i (typeStrength (x, bm)) = typeStrength (x, ev i bm) := by
  change (bm >>= fun y => pure (x, y)) i = ev i bm >>= fun y => pure (x, y)
  change (bm >>= fun y => pure (x, y)).run i = _
  rw [ReaderT.run_bind]
  rfl

end NeSyCat
