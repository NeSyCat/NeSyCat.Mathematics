import Mathlib.CategoryTheory.Category.Basic

/-!
# Pilot Smoke Check

This file is a scaffold smoke-check for the NeSyCat Lean project. It exists
solely to confirm that the Lean 4 toolchain, `lake` build, and the pinned
Mathlib dependency are wired up correctly end to end. It imports a basic
Mathlib category-theory module and proves one trivial lemma about
identities in a category.
-/

namespace NeSyCat.Pilot

open CategoryTheory

/-- Smoke test: left-composing with the identity morphism is the identity
function on morphisms. This is trivial by the category axioms and confirms
that Mathlib's category theory library type-checks and compiles. -/
theorem smoke_id_comp {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) :
    𝟙 X ≫ f = f := by
  simp

end NeSyCat.Pilot
