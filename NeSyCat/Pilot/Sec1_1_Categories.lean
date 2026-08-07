import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Order

/-!
# §1.1 Categories (Leinster, *Basic Category Theory*, pp. 10-16)

This file formalizes items from §1.1 of the pilot target, using Mathlib's
`CategoryTheory.Category` class (`Mathlib.CategoryTheory.Category.Basic`) as
the ambient background notion of category (Leinster's Definition 1.1.1).

Covered:
* Example 1.1.3 (categories of mathematical structures: **Set**, **Grp**,
  **Ring**, **Vect_k**, **Top**, each with "the evident" composition and
  identities). Formalized element-level, against Mathlib's bundled
  categories `Type u` (for **Set**), `GrpCat` (for **Grp** — Leinster's
  **Grp**; this vendored Mathlib names the bundled category `GrpCat`),
  `RingCat` (for **Ring**), `ModuleCat k` (for **Vect_k**, `k` a field),
  and `TopCat` (for **Top**).
* Definition 1.1.4 (isomorphism; isomorphic objects).
* Example 1.1.5 (isomorphisms in `Set` are exactly the bijections).
* Exercise 1.1.13 (a map has at most one inverse).
-/

namespace NeSyCat.Pilot

open CategoryTheory

variable {C : Type*} [Category C]

/-!
### Leinster 1.1.3 (Example — Categories of mathematical structures)

"There are categories **Set** (sets and functions), **Grp** (groups and
group homomorphisms), **Ring** (rings and ring homomorphisms), **Vect_k**
(vector spaces over a field `k` and `k`-linear maps), and **Top**
(topological spaces and continuous maps), in each case with the evident
composition and identities."

We do not rebuild these five categories from scratch (Mathlib already
bundles them as categories); instead, for each one, we record
element-level that the ambient categorical identity `𝟙 X` really is the
identity function, and categorical composition `f ≫ g` really is ordinary
function composition applied in the expected order — i.e. that the
composition and identities really are "the evident" ones.
-/

/-- Leinster 1.1.3 (Categories of mathematical structures — **Set**): the
identity morphism of the category of sets and functions (Mathlib's
`Type u`, standing in for **Set**) acts, on elements, as the identity
function. -/
theorem set_id_apply {X : Type u} (x : X) : (𝟙 X : X ⟶ X) x = x :=
  types_id_apply X x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Set**):
composition of morphisms in the category of sets and functions acts, on
elements, as ordinary function composition (applied in the expected
order: `(f ≫ g) x = g (f x)`). -/
theorem set_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) :=
  types_comp_apply f g x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Grp**): the
identity morphism of the category of groups and group homomorphisms
(Mathlib's `GrpCat`) acts, on elements, as the identity function. -/
theorem grpCat_id_apply {G : GrpCat} (x : G) : (𝟙 G : G ⟶ G) x = x :=
  GrpCat.id_apply G x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Grp**):
composition of morphisms in the category of groups and group
homomorphisms acts, on elements, as ordinary function composition
(applied in the expected order: `(f ≫ g) x = g (f x)`). -/
theorem grpCat_comp_apply {G H K : GrpCat} (f : G ⟶ H) (g : H ⟶ K) (x : G) :
    (f ≫ g) x = g (f x) :=
  GrpCat.comp_apply f g x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Ring**): the
identity morphism of the category of rings and ring homomorphisms
(Mathlib's `RingCat`) acts, on elements, as the identity function. -/
theorem ringCat_id_apply {R : RingCat} (x : R) : (𝟙 R : R ⟶ R) x = x :=
  RingCat.id_apply R x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Ring**):
composition of morphisms in the category of rings and ring homomorphisms
acts, on elements, as ordinary function composition (applied in the
expected order: `(f ≫ g) x = g (f x)`). -/
theorem ringCat_comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) (x : R) :
    (f ≫ g) x = g (f x) :=
  RingCat.comp_apply f g x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Vect_k**): the
identity morphism of the category of `k`-vector spaces and `k`-linear maps
(Mathlib's `ModuleCat k` for a field `k`) acts, on elements, as the
identity function. -/
theorem moduleCat_id_apply {k : Type*} [Field k] {M : ModuleCat k} (x : M) :
    (𝟙 M : M ⟶ M) x = x :=
  ModuleCat.id_apply M x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Vect_k**):
composition of morphisms in the category of `k`-vector spaces and
`k`-linear maps acts, on elements, as ordinary function composition
(applied in the expected order: `(f ≫ g) x = g (f x)`). -/
theorem moduleCat_comp_apply {k : Type*} [Field k] {M N P : ModuleCat k}
    (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g) x = g (f x) :=
  ModuleCat.comp_apply f g x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Top**): the
identity morphism of the category of topological spaces and continuous
maps (Mathlib's `TopCat`) acts, on elements, as the identity function. -/
theorem topCat_id_apply {X : TopCat} (x : X) : (𝟙 X : X ⟶ X) x = x :=
  TopCat.id_app X x

/-- Leinster 1.1.3 (Categories of mathematical structures — **Top**):
composition of morphisms in the category of topological spaces and
continuous maps acts, on elements, as ordinary function composition
(applied in the expected order: `(f ≫ g) x = g (f x)`). -/
theorem topCat_comp_apply {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) :=
  TopCat.comp_app f g x

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
  constructor
  · rintro ⟨g, hfg, hgf⟩
    have hleft : Function.LeftInverse g f := fun x => ConcreteCategory.congr_hom hfg x
    have hright : Function.RightInverse g f := fun y => ConcreteCategory.congr_hom hgf y
    exact ⟨hleft.injective, hright.surjective⟩
  · rintro ⟨hinj, hsurj⟩
    -- `g` is a right inverse of `f` by construction (`surjInv_eq`); injectivity of
    -- `f` upgrades it to a two-sided inverse.
    set g : B → A := Function.surjInv hsurj with hg_def
    have hfg : ∀ y, f (g y) = y := Function.surjInv_eq hsurj
    have hgf : ∀ x, g (f x) = x := fun x => hinj (hfg (f x))
    refine ⟨TypeCat.ofHom g, ConcreteCategory.hom_ext _ _ fun x => ?_,
      ConcreteCategory.hom_ext _ _ fun y => ?_⟩
    · simp only [types_comp_apply, types_id_apply, TypeCat.ofHom_apply]
      exact hgf x
    · simp only [types_comp_apply, types_id_apply, TypeCat.ofHom_apply]
      exact hfg y

end NeSyCat.Pilot
