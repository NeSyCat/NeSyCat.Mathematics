import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# §1.1 Categories (Leinster, *Basic Category Theory*, pp. 10-16)

This file formalizes items from §1.1 of the pilot target, using Mathlib's
`CategoryTheory.Category` class (`Mathlib.CategoryTheory.Category.Basic`) as
the ambient background notion of category (Leinster's Definition 1.1.1).

Covered:
* Definition 1.1.4 (isomorphism; isomorphic objects).
* Example 1.1.5 (isomorphisms in `Set` are exactly the bijections).
* Exercise 1.1.13 (a map has at most one inverse).
-/

namespace NeSyCat.Pilot

open CategoryTheory

variable {C : Type*} [Category C]

/-- Leinster 1.1.4 (Isomorphism): a map `f : A ⟶ B` in a category is an
**isomorphism** if there exists `g : B ⟶ A` with `g ∘ f = 1_A` and
`f ∘ g = 1_B` (written here in categorical order: `f ≫ g = 𝟙 A` and
`g ≫ f = 𝟙 B`); such `g` is unique (see `inverse_unique` below) and is
called `f⁻¹`. -/
def IsIsomorphism {A B : C} (f : A ⟶ B) : Prop :=
  ∃ g : B ⟶ A, f ≫ g = 𝟙 A ∧ g ≫ f = 𝟙 B

/-- Leinster 1.1.4 (Isomorphic objects): objects `A` and `B` of a category
are **isomorphic** if there exists an isomorphism `f : A ⟶ B`. Leinster
writes this `A ≅ B`. -/
def IsIsomorphic (A B : C) : Prop :=
  ∃ f : A ⟶ B, IsIsomorphism f

/-- Leinster 1.1.13 (Exercise): a map in a category can have at most one
inverse — given `f : A ⟶ B`, there is at most one `g : B ⟶ A` with
`g ∘ f = 1_A` and `f ∘ g = 1_B`. -/
theorem inverse_unique {A B : C} (f : A ⟶ B) {g g' : B ⟶ A}
    (hg : f ≫ g = 𝟙 A ∧ g ≫ f = 𝟙 B) (hg' : f ≫ g' = 𝟙 A ∧ g' ≫ f = 𝟙 B) :
    g = g' := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hg1', -⟩ := hg'
  calc g = g ≫ 𝟙 A := (Category.comp_id g).symm
    _ = g ≫ (f ≫ g') := by rw [hg1']
    _ = (g ≫ f) ≫ g' := (Category.assoc g f g').symm
    _ = 𝟙 B ≫ g' := by rw [hg2]
    _ = g' := Category.id_comp g'

/-- Leinster 1.1.5 (Example): the isomorphisms in **Set** are exactly the
bijections. Here **Set** is represented, as usual in Mathlib, by the
category `Type u` of types and functions (`Mathlib.CategoryTheory.Types`),
so this specializes `IsIsomorphism` to that category. -/
theorem isIsomorphism_iff_bijective {A B : Type u} (f : A ⟶ B) :
    IsIsomorphism f ↔ Function.Bijective f := by
  sorry -- TODO: prove both directions: forward direction extracts injectivity
        -- and surjectivity from the two categorical inverse equations
        -- (via `ConcreteCategory.congr_hom`); backward direction builds the
        -- inverse morphism from `Equiv.ofBijective` (via `TypeCat.ofHom`) and
        -- checks the two triangle identities (via `ConcreteCategory.hom_ext`).

end NeSyCat.Pilot
