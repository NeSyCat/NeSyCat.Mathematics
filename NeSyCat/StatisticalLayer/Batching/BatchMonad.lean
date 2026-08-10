/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr

/-!
# The batch monad `Bmon`

Blueprint item `def:batch-monad`
(`blueprint/src/content.tex`, §"Batching", `[NeSy26, §5]`).

For a batch size `B`, the batch index set `Bidx := {1,...,B}` of the
blueprint is realized as `Fin B`. `Bmon B X := Fin B → X` is the reader
monad on `Fin B`: `Bmon.ret` is the batch-constant family, `Bmon.bind`
is DIAGONAL — the continuation at index `b` sees only index `b`'s own
value, never another index's.

**Encoding pin (disclosed, ticket C3-B6):** this is a PLAIN-FUNCTION
encoding (`Fin B → X`), not Lean/Mathlib's `ReaderT` transformer
applied to `Id`. `Bmon.ret`/`Bmon.bind` are bare functions with their
own hand-stated formulas, matching
`NeSyCat/CategoricalLayer/SemiringMonads/SemiringMonad.lean`'s own
`ret`/`bind` pattern (no `Monad`/`LawfulMonad` instance is registered
for `MS S` anywhere in this library, so routing the effect-free case
through `ReaderT (Fin B) Id` would buy nothing here). `BatchTransformer.lean`
DOES use Lean's own `ReaderT`, `MonadLift`, and the core `LawfulMonad
(ReaderT ρ m)` instance once an inner effect monad `M` is in the
picture (`thm:batch-transformer`) — `Bmon B X` and `ReaderT (Fin B) Id
X` agree definitionally (`Id X = X`), so no information is lost by
keeping the effect-free case in plain-function form here.
-/

namespace NeSyCat

/-- Blueprint `def:batch-monad` (Batch monad, carrier): for a batch
size `B`, `Bmon B X := Fin B → X`, the reader monad on the batch index
set `Bidx := Fin B`. -/
-- (A1 bijection-law companion of `Bmon.bind`, content.tex def:batch-monad)
@[blueprint_internal]
abbrev Bmon (B : ℕ) (X : Type*) := Fin B → X

variable {B : ℕ} {X Y : Type*}

/-- Blueprint `def:batch-monad` (Batch monad, unit): `Ret(x) := const
x`, the batch-constant family. -/
-- (A1 bijection-law companion of `Bmon.bind`, content.tex def:batch-monad)
@[blueprint_internal]
def Bmon.ret (x : X) : Bmon B X := fun _ => x

/-- Blueprint `def:batch-monad` (Batch monad, bind): `(m bind f)(b) :=
f(m(b))(b)`, the DIAGONAL bind — the continuation `f` at index `b` sees
only `m`'s own value at `b`, never another index's value. -/
def Bmon.bind (m : Bmon B X) (f : X → Bmon B Y) : Bmon B Y :=
  fun b => f (m b) b

end NeSyCat
