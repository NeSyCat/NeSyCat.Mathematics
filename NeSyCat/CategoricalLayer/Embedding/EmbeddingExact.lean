/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr

/-!
# Exact embedded chaining

Blueprint item `thm:embedding-exact`
(`blueprint/src/content.tex`, §"Embedding-space reasoning", C3-TL-A; see
that section's own citation comment for the Domingos provenance).

A finite relation between finite sets is a Boolean matrix; cast into `ℝ` it
becomes a real matrix `R` with `0`/`1` entries, and "chaining" it against a
value `v` is matrix-vector multiplication `R *ᵥ v` (the same operation
`lem:bind-matrix-mult` identifies `MS S`'s `bind` with). An embedding matrix
`E`, mapping the relation's index set into a `d`-dimensional latent space,
lets that same value be represented instead by its embedded code `E *ᵥ v`.
`embedding_exact` states the theorem below at its natural generality, for
an arbitrary real matrix `R`; the finite-relation case is the instance where
every entry of `R` is `0` or `1`.
-/

namespace NeSyCat

open Matrix

/-- Blueprint `thm:embedding-exact` (exact embedded chaining): let `E` be a
`d × Y` embedding matrix over `ℝ` with orthonormal columns, `Eᵀ * E = 1`.
Then retrieval is exact, `Eᵀ *ᵥ (E *ᵥ v) = v` for every `v : Y → ℝ`, and
chaining a relation `R` against an embedded-then-retrieved value equals
chaining `R` against the value directly:
`(R * Eᵀ) *ᵥ (E *ᵥ v) = R *ᵥ v`. -/
theorem embedding_exact {X Y : Type*} [Fintype Y] [DecidableEq Y] {d : ℕ}
    (E : Matrix (Fin d) Y ℝ) (hE : Eᵀ * E = (1 : Matrix Y Y ℝ))
    (R : Matrix X Y ℝ) (v : Y → ℝ) :
    (Eᵀ *ᵥ (E *ᵥ v) = v) ∧ ((R * Eᵀ) *ᵥ (E *ᵥ v) = R *ᵥ v) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]
  · rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hE, Matrix.mul_one]

end NeSyCat
