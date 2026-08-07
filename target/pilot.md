# Pilot target: Leinster, *Basic Category Theory*, Chapter 1

Source: Tom Leinster, *Basic Category Theory*, Cambridge University
Press, 2014. arXiv:1612.09375v3. (Downloaded and read directly from the
arXiv PDF; item numbers below are checked against that text, not
recalled from memory.)

Scope: Chapter 1, "Categories, functors and natural transformations"
(book pp. 9-40), covering §1.1 Categories, §1.2 Functors, §1.3 Natural
transformations, including all end-of-section exercises.

Numbering below follows the book exactly: `<section>.<subsection
counter>` for Definitions/Examples/Constructions/Lemmas/Propositions/
Corollaries, and `<section>.<exercise number>` for exercises (e.g.
`1.1.13` is exercise 13 attached to §1.1).

---

## §1.1 Categories (pp. 10-16)

**1.1.1 — Definition — Category.** A category `A` consists of a
collection `ob(A)` of objects; for each `A, B ∈ ob(A)` a collection
`A(A,B)` of maps/arrows/morphisms from `A` to `B`; a composition
function `A(B,C) × A(A,B) → A(A,C)`, `(g,f) ↦ g∘f`; and for each
`A ∈ ob(A)` an identity element `1_A ∈ A(A,A)`; satisfying
associativity `(h∘g)∘f = h∘(g∘f)` and the identity laws
`f∘1_A = f = 1_B∘f`.

**1.1.3 — Example — Categories of mathematical structures.** There are
categories **Set** (sets and functions), **Grp** (groups and group
homomorphisms), **Ring** (rings and ring homomorphisms),
**Vect_k** (vector spaces over a field `k` and `k`-linear maps), and
**Top** (topological spaces and continuous maps), in each case with the
evident composition and identities.

**1.1.4 — Definition — Isomorphism.** A map `f : A → B` in a category
`A` is an **isomorphism** if there exists `g : B → A` with
`g∘f = 1_A` and `f∘g = 1_B`; such `g` is unique and is called `f⁻¹`. If
an isomorphism `A → B` exists, `A` and `B` are **isomorphic**,
`A ≅ B`.

**1.1.5 — Example — Isomorphisms in Set.** The isomorphisms in **Set**
are exactly the bijections.

**1.1.6 — Example — Isomorphisms in Grp/Ring.** The isomorphisms in
**Grp** are exactly the group isomorphisms (bijective homomorphisms,
with the fact that the set-theoretic inverse is automatically a
homomorphism); likewise for **Ring**.

**1.1.7 — Example — Isomorphisms in Top.** The isomorphisms in **Top**
are exactly the homeomorphisms; unlike **Grp**/**Ring**, a bijective
continuous map need not be an isomorphism (e.g.
`t ↦ e^(2πit) : [0,1) → {z ∈ ℂ : |z|=1}` is a continuous bijection that
is not a homeomorphism).

**1.1.8 — Examples — Categories as mathematical structures.**
(a) There is a category `∅` with no objects or maps, and a category
`1` with one object and only its identity map, and a category with two
objects and exactly one non-identity map `A → B`.
(c) A group is essentially the same thing as a one-object category in
which every map is an isomorphism (composition = group multiplication,
identity = group unit). (d) A monoid is essentially the same thing as a
one-object category (no invertibility required). (e) A preordered set
`(S, ≤)` is essentially the same thing as a category in which each
hom-set has at most one element, with `A ≤ B` iff there is a map
`A → B`.

**1.1.9 — Construction — Opposite category.** Every category `A` has
an opposite (dual) category `A^op` with `ob(A^op) = ob(A)` and
`A^op(B,A) = A(A,B)`, identities as in `A`, and composition with the
arguments reversed.

**1.1.11 — Construction — Product category.** Given categories `A` and
`B`, the product category `A × B` has `ob(A×B) = ob(A) × ob(B)` and
`(A×B)((A,B),(A',B')) = A(A,A') × B(B,B')`, with componentwise
composition and identities.

### Exercises (§1.1)

- **1.1.12.** SKIP: "Find three examples of categories not mentioned
  above" — open-ended, not a formalizable statement.
- **1.1.13.** A map in a category can have at most one inverse: given
  `f : A → B`, there is at most one `g : B → A` with `gf = 1_A` and
  `fg = 1_B`.
- **1.1.14.** For categories `A` and `B`, work out the (unique
  sensible) definitions of composition and identities on the product
  category `A × B` from Construction 1.1.11, and verify the category
  axioms hold.
- **1.1.15.** SKIP: the category **Toph** of topological spaces and
  homotopy classes of continuous maps — requires developing homotopy
  theory of maps to state well-definedness of composition; out of
  scope for the pilot's Mathlib-background budget.

**Formalization notes (§1.1):** use `Mathlib.CategoryTheory.Category.Basic`
for the ambient `Category` class and `Mathlib.CategoryTheory.Opposites`
for `Cᵒᵖ`; `Mathlib.CategoryTheory.Category.Preorder` already gives the
preorder-as-category direction of 1.1.8(e) as background, so the target
item is to state/prove the informal correspondence explicitly in
`NeSyCat.Pilot`, not just cite it. `Mathlib.Algebra.Group.Defs`/`Monoid`
for 1.1.8(c)–(d). `Mathlib.CategoryTheory.Products.Basic` gives `A × B` as
background for 1.1.14; the pilot item is to prove the category axioms
by hand for a from-scratch product-category construction, not merely
invoke the Mathlib instance.

---

## §1.2 Functors (pp. 17-27)

**1.2.1 — Definition — Functor.** A functor `F : A → B` consists of a
function `ob(A) → ob(B)`, `A ↦ F(A)`, and for each `A, A' ∈ A` a
function `A(A,A') → B(F(A),F(A'))`, `f ↦ F(f)`, such that
`F(f'∘f) = F(f')∘F(f)` and `F(1_A) = 1_{F(A)}`.

**1.2.3 — Examples — Forgetful functors.** There are forgetful functors
`U : Grp → Set` (send a group to its underlying set, a homomorphism to
itself as a function), `Ring → Set`, and `Vect_k → Set`; and
structure-partially-forgetting functors `Ring → Ab` (ring to its
underlying additive group) and `Ring → Mon` (ring to its underlying
multiplicative monoid); and the inclusion functor `Ab → Grp`.

**1.2.4 — Examples — Free functors.** SKIP for full formalization
(free group/free commutative ring/free vector space constructions are
substantial standalone projects); note as background only. (c) The
free vector space functor `F : Set → Vect_k` sends a set `S` to the
vector space of finitely-supported functions `S → k` (formal
`k`-linear combinations of elements of `S`), which is close enough to
`Mathlib`'s `Finsupp`/free module machinery to be worth stating as a
target item relating `F(S)` to `S →₀ k`.

**1.2.5 — Examples — Functors in algebraic topology.** SKIP: the
fundamental group functor `π₁ : Top_* → Grp` and the homology functors
`H_n : Top → Ab` require substantial algebraic-topology background not
otherwise in scope for the pilot.

**1.2.6 — Example — Functor from a polynomial system.** SKIP: a fairly
elaborate motivating example (a system of polynomial equations gives a
functor **CRing** → **Set**); illustrative rather than a reusable
target lemma.

**1.2.7 — Example — Functors between one-object categories.** A
functor `F : G → H` between monoids `G, H` regarded as one-object
categories is exactly a monoid homomorphism `F : G → H` (in particular,
`F(g'g) = F(g')F(g)` and `F(1) = 1`).

**1.2.8 — Example — Functor from a monoid to Set.** A functor
`F : G → Set` (for `G` a monoid regarded as a one-object category)
amounts to a set `S` together with a function `G × S → S`,
`(g,s) ↦ g·s`, satisfying `(g'g)·s = g'·(g·s)` and `1·s = s`: that is,
a left `G`-set.

**1.2.9 — Example — Functors between preorders.** For preordered sets
`A` and `B` regarded as categories, a functor between the corresponding
categories is exactly an order-preserving map `f : A → B`
(`a ≤ a' ⟹ f(a) ≤ f(a')`). (Assertion proved in Exercise 1.2.22.)

**1.2.10 — Definition — Contravariant functor.** A contravariant
functor from `A` to `B` is (by definition) a functor `A^op → B`; an
ordinary functor is sometimes called *covariant* for emphasis.

**1.2.12 — Example — Hom(-,W) and the dual vector space.** For a fixed
vector space `W` over `k`, there is a contravariant functor
`Hom(-,W) : Vect_k^op → Vect_k` sending `V ↦ Hom(V,W)` and a linear map
`f : V → V'` to `f* : Hom(V',W) → Hom(V,W)`, `f*(q) = q∘f`. The special
case `W = k` gives the contravariant dual-space functor
`(-)* : Vect_k^op → Vect_k`, `V ↦ V*`.

**1.2.14 — Example — Right G-sets.** A contravariant functor
`G^op → Set` (equivalently a functor `G^op → Set`, for `G` a monoid) is
exactly a right `G`-set, dual to Example 1.2.8.

**1.2.15 — Definition — Presheaf.** A presheaf on a category `A` is a
functor `A^op → Set`.

**1.2.16 — Definition — Faithful, full.** A functor `F : A → B` is
**faithful** (resp. **full**) if for each `A, A' ∈ A` the function
`A(A,A') → B(F(A),F(A'))`, `f ↦ F(f)`, is injective (resp. surjective).

**1.2.18 — Definition — Subcategory.** A subcategory `S` of `A`
consists of a subclass `ob(S)` of `ob(A)` together with, for each
`S, S' ∈ ob(S)`, a subclass `S(S,S')` of `A(S,S')`, closed under
composition and identities. It is a **full** subcategory if
`S(S,S') = A(S,S')` for all `S, S' ∈ ob(S)`; the inclusion functor
`I : S → A` is always faithful, and full iff `S` is a full subcategory.

### Exercises (§1.2)

- **1.2.20.** SKIP: "Find three examples of functors not mentioned
  above" — open-ended.
- **1.2.21.** Functors preserve isomorphisms: if `F : A → B` is a
  functor and `A ≅ A'` in `A`, then `F(A) ≅ F(A')` in `B`.
- **1.2.22.** Prove the assertion of Example 1.2.9: given preordered
  sets `A` and `B` (regarded as categories), a functor between the
  corresponding categories amounts to an order-preserving map
  `A → B`.
- **1.2.23(a).** For a group `G` regarded as a one-object category
  with `G^op` also so regarded, `G` is isomorphic (as a category, i.e.
  as a group) to `G^op`, via `g ↦ g⁻¹`.
- **1.2.23(b).** SKIP: "find a monoid not isomorphic to its opposite" —
  existence-of-example exercise, not a reusable target statement.
- **1.2.24.** SKIP: "is there a functor `Z : Grp → Grp` with
  `Z(G)` = the centre of `G` for all groups `G`?" — the interesting
  content is a negative existence result (no functorial choice of
  centre map is compatible with all homomorphisms), which is a
  research-level side question outside the pilot's scope.
- **1.2.25(a)-(c).** A functor `F : A × B → C` out of a product category
  corresponds to families of functors `Fᴬ : B → C` (`A ∈ A`) and
  `F_B : A → C` (`B ∈ B`), defined by `Fᴬ(B) = F(A,B) = F_B(A)`,
  satisfying compatibility conditions on maps; conversely, such a
  compatible pair of families determines a unique functor
  `F : A × B → C`.
- **1.2.26.** SKIP: "fill in the details of Example 1.2.11" — asks to
  redo the construction of the contravariant functor
  `C : Top^op → Ring` sending `X` to its ring of continuous real-valued
  functions; largely duplicates the content of 1.2.12 in a different
  concrete setting and is not essential to capture separately.
- **1.2.27.** There exists a faithful functor `F : A → B` and distinct
  maps `f₁ ≠ f₂` in `A` with `F(f₁) = F(f₂)` (on *different* pairs of
  objects) — faithfulness does not imply injectivity of `F` on the
  union of all hom-sets.
- **1.2.28(a)-(b).** SKIP: "of the examples in this section, which are
  full/faithful" and "give one example of each combination" —
  classification/search exercises rather than a single provable
  statement.
- **1.2.29(a)-(b).** SKIP: "what are the subcategories of an ordered
  set / of a group?" — open-ended descriptive questions.

**Formalization notes (§1.2):** use
`Mathlib.CategoryTheory.Functor.Basic` for `Functor`/`CategoryTheory.Functor`
as background, and `Mathlib.CategoryTheory.Functor.FullyFaithful` for
`Full`/`Faithful` classes (background only — 1.2.16 must still be
stated and unpacked as a `NeSyCat.Pilot` item). Use
`Mathlib.CategoryTheory.Category.Basic`'s `CategoryTheory.Cat` /
one-object-category constructions plus `Mathlib.Algebra.Group.Defs`
for 1.2.7/1.2.8. `Mathlib.CategoryTheory.Products.Basic` for background
on 1.2.25's product-category universal property (`Functor.prod`), but
prove the correspondence directly. `Mathlib.CategoryTheory.Functor.Basic`
`Functor.op`/`Functor.leftOp` are background for 1.2.10.

---

## §1.3 Natural transformations (pp. 27-40)

**1.3.1 — Definition — Natural transformation.** For functors
`F, G : A → B`, a natural transformation `α : F → G` is a family of
maps `(α_A : F(A) → G(A))_{A∈A}` (the **components**) such that for
every `f : A → A'` in `A`, `G(f) ∘ α_A = α_{A'} ∘ F(f)` (the naturality
square commutes).

**1.3.4 — Example — G-equivariant maps.** For `G` a monoid and
`S, T : G → Set` two `G`-sets (functors from the one-object category
`G`), a natural transformation `α : S → T` is exactly a single function
`α : S → T` satisfying `α(g·s) = g·α(s)` for all `s ∈ S, g ∈ G`: a
`G`-equivariant map.

**1.3.5/1.3.6 — Example & Construction — Determinant as a natural
transformation; composition of natural transformations.** For fixed
`n`, `det_R : Mₙ(R) → U(R)` (the determinant of `n×n` matrices,
`det_R(XY) = det_R(X)det_R(Y)`, `det_R(I)=1`) assembles into a natural
transformation `det : Mₙ → U` between the functors `Mₙ, U : CRing → Mon`.
Natural transformations compose: given `α : F → G` and `β : G → H`,
`(β∘α)_A = β_A ∘ α_A` defines `β∘α : F → H`, and `1_F` with
`(1_F)_A = 1_{F(A)}` is an identity for this composition; functors
`A → B` and natural transformations between them form the **functor
category** `[A,B]`.

**1.3.7 — Example — Functor category out of the 2-object discrete
category.** For `2` the discrete category with two objects, the
functor category `[2, B]` is isomorphic to the product category
`B × B`.

**1.3.9 — Example — Natural transformations between order-preserving
maps.** For ordered sets `A, B` viewed as categories and order-
preserving maps `f, g : A → B` viewed as functors, there is at most one
natural transformation `f → g`, and one exists iff `f(a) ≤ g(a)` for
all `a ∈ A`; hence `[A,B]` is itself an ordered set, with
`f ≤ g ⟺ ∀a, f(a) ≤ g(a)`.

**1.3.10 — Definition — Natural isomorphism.** A natural isomorphism
between functors `F, G : A → B` is an isomorphism between `F` and `G`
in the functor category `[A,B]`.

**1.3.11 — Lemma — Componentwise criterion.** A natural transformation
`α : F → G` is a natural isomorphism if and only if `α_A : F(A) → G(A)`
is an isomorphism for every `A ∈ A`.

**1.3.14 — Example — Double dual.** For `FDVect` the category of
finite-dimensional vector spaces over `k`, there is a natural
isomorphism `α : 1_{FDVect} → (-)**` (from the identity functor to the
double-dual functor) with component `α_V : V → V**`,
`α_V(v)(φ) = φ(v)`; equivalently `V ≅ V**` naturally in `V`.

**1.3.15 — Definition — Equivalence of categories.** An equivalence
between categories `A` and `B` consists of functors `F : A → B`,
`G : B → A`, together with natural isomorphisms `η : 1_A → G∘F` and
`ε : F∘G → 1_B`. If such data exists, `A ≃ B` and `F, G` are called
**equivalences**.

**1.3.17 — Definition — Essentially surjective on objects.** A functor
`F : A → B` is essentially surjective on objects if for all `B ∈ B`
there exists `A ∈ A` with `F(A) ≅ B`.

**1.3.18 — Proposition — Characterization of equivalences.** A functor
is an equivalence if and only if it is full, faithful, and essentially
surjective on objects.

**1.3.19 — Corollary — Full+faithful gives an equivalence onto its
image.** If `F : C → D` is full and faithful, then `C` is equivalent to
the full subcategory `C'` of `D` on the objects of the form `F(C)` for
`C ∈ C`.

**1.3.20 — Example — FinSet and a skeleton.** For `FinSet` the category
of finite sets and functions, and `B` the full subcategory on one chosen
set of each finite cardinality `n`, the inclusion `B ↪ FinSet` is an
equivalence `B ≃ FinSet`.

**1.3.21 — Example — Mon and one-object categories.** The full
subcategory `C` of `CAT` whose objects are one-object categories is
equivalent to `Mon` (the category of monoids), via the functor sending
a one-object category to its monoid of endomorphisms.

### Exercises (§1.3)

- **1.3.25.** SKIP: "Find three examples of natural transformations not
  mentioned above" — open-ended.
- **1.3.26.** Prove Lemma 1.3.11 (natural transformation is a natural
  isomorphism iff every component is an isomorphism).
- **1.3.27.** For categories `A, B`: `[A^op, B^op] ≅ [A,B]^op`.
- **1.3.28(a)-(b).** For sets `A, B`, writing `Bᴬ` for the set of
  functions `A → B`: (a) there is a canonical evaluation function
  `A × Bᴬ → B`; (b) there is a canonical function `A → B^(Bᴬ)` (double
  evaluation).
- **1.3.29.** For functors `F, G : A × B → C`, a family
  `α_{A,B} : F(A,B) → G(A,B)` is a natural transformation `F → G` iff
  it is natural in each variable separately (natural in `B` for each
  fixed `A`, and natural in `A` for each fixed `B`).
- **1.3.30.** SKIP: for a group `G`, natural isomorphism defines an
  equivalence relation on functors `ℤ → G` (equivalently, on elements
  `g ∈ G` via `φ(1) = g`); asks the reader to *identify* this relation
  as conjugacy, which is an open-ended "guess the relation" exercise
  rather than a single target statement — though the underlying fact
  ("`φ ≅ ψ` as functors `ℤ → G` iff `φ(1)` and `ψ(1)` are conjugate in
  `G`") would be a good stretch item if time permits.
- **1.3.31(a)-(c).** SKIP: `Sym(X) ≅ Ord(X)` for finite `X` (both have
  `n!` elements) but *not naturally* in `X`; proving a *non-existence*
  of any natural transformation is a substantially harder
  formalization (quantifying over all possible natural
  transformations) and is deferred.
- **1.3.32(a)-(b).** Prove Proposition 1.3.18: a functor is an
  equivalence iff it is full, faithful, and essentially surjective on
  objects (both directions).
- **1.3.33.** SKIP: `Mat` (objects = natural numbers, `Mat(m,n)` =
  `n×m` matrices over `k`, composition = matrix multiplication) is
  equivalent to `FDVect`; substantial standalone construction
  (defining the `Mat` category from scratch) beyond the pilot's time
  budget, noted as a stretch item.
- **1.3.34.** Equivalence of categories is an equivalence relation
  (reflexive, symmetric, transitive).

**Formalization notes (§1.3):** use `Mathlib.CategoryTheory.NatTrans`
for the ambient `NatTrans`/`whiskerLeft`/`whiskerRight` machinery and
`Mathlib.CategoryTheory.Functor.Category` for `[A,B]` /
`CategoryTheory.Functor.category` as background, but 1.3.1's naturality
square and 1.3.10/1.3.11's iso-in-functor-category characterization
must be restated and proved as `NeSyCat.Pilot` items, not merely cited.
`Mathlib.CategoryTheory.Equivalence` gives `CategoryTheory.Equivalence`
and the full/faithful/ess.-surjective characterization as background
for 1.3.15/1.3.17/1.3.18/1.3.19 — the pilot proof of 1.3.18 should be
constructed directly (building the inverse functor and unit/counit by
hand from fullness+faithfulness+essential surjectivity), since citing
`Equivalence.ofFullyFaithfullyEssImage`-style Mathlib lemmas directly
would defeat the purpose. `Mathlib.LinearAlgebra.Dual` /
`Module.evalEquiv` are background for 1.3.14 (double dual).
