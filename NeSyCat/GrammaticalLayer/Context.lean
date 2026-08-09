/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.DomainLayer.DomainLayer

/-!
# Contexts

Blueprint item `def:context` (`blueprint/src/content.tex`, §"Grammatical
layer", `NeSyCat Theory v2`, `new.tex` 1--396): a context `x⃗` is a finite
list of *distinct* variable symbols from `Var` (`DomSignature.Var`),
including the empty context. This is the Elephant-style presentation of
contexts (Johnstone): a context is a `List` refined by a `Nodup` side
condition, not a `Finset`, since the document's later constructions
(quantifier position-splitting, `[φ]`) genuinely use the list's order.
-/

namespace NeSyCat

/-- Blueprint `def:context` (Context): a context `x⃗` is a finite list
`[x₁,…,xₙ]` of *distinct* variable symbols from `Var`
(`DomSignature.Var`), including the empty context `[]`. -/
def Context (sigG : DomSignature) := { l : List sigG.Var // l.Nodup }

end NeSyCat
