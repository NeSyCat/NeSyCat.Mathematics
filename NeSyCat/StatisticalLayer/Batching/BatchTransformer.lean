/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.StatisticalLayer.Batching.BatchMonad

/-!
# The batch transformer `Bmon M` and pointwise evaluation

Blueprint items `thm:batch-transformer` and `thm:pointwise-eval` (part
1: `ev_i` is a monad morphism)
(`blueprint/src/content.tex`, §"Batching", `[NeSy26, §5]`).

**Encoding pin (disclosed, ticket C3-B6).** Once an inner effect monad
`M` enters the picture, `BmonT B M X := Bidx → M X` is realized as
Lean/Mathlib's own `ReaderT (Fin B) M X` (definitionally `Fin B → M
X`, matching `Bmon`'s own carrier). This lets the "the reader
transformer is again a monad" half of `thm:batch-transformer` cite
Lean core's `instance [Monad m] [LawfulMonad m] : LawfulMonad (ReaderT
ρ m)` (`Init/Control/Lawful/Instances.lean`) directly as BACKGROUND
machinery (FORMALIZE.md's "Mathlib/core may be used freely as
background machinery" clause) — its own proof already reduces
`ReaderT`'s bind/pure laws pointwise (via `ReaderT.ext`) to `M`'s own
`LawfulMonad` laws, exactly the blueprint's own proof sketch. The two
CANONICAL LIFTS are new content built here: `liftM` corresponds to the
`MonadLift`-shaped embedding (Lean core's own `instance : MonadLift m
(ReaderT ρ m)` is definitionally `liftM`, `fun x _ => x`); `liftBmon`
corresponds in spirit to a `MonadFunctor`-shaped lift along `M`'s unit
`pure : Id ⟶ M`, DISCLOSED as not literally an instance of Lean core's
`MonadFunctor` class (whose `monadMap` signature is restricted to
same-monad endo-transformations `{β} → m β → m β`, not a
monad-changing map `Id ⟶ M`) — `liftBmon` and its two morphism laws
(`liftBmon_ret`/`liftBmon_bind`) are proved by hand below, reducing to
`M`'s own left-unit law (`pure_bind`, the `Monad`-class shadow of
`thm:semiring-monad-laws`'s left unit law).

`ev`/`ev_isMonadMorphism` below is `thm:pointwise-eval`'s PART 1 ONLY
(`ev_i` is a monad morphism, unconditional). Part 2 (commutation with
the Kleisli interpretation of `def:kleisli-interpretation`, under the
batch-naturality hypothesis) is NOT formalized here: it needs a
generic account of the Kleisli interpretation over an ARBITRARY strong
monad `M` (so it can be instantiated at both `M` and `Bmon M`), which
does not exist yet in `NeSyCat/GrammaticalLayer/Kleisli.lean` (built
there only for the library's own concrete interpretations). Split
honestly per the ticket spec: `content.tex`'s `thm:pointwise-eval-kleisli`
env states part 2 with its own (informal) proof, carries no `\lean`/
`\leanok` mark, and is left for a rider ticket after that generic
account lands.
-/

namespace NeSyCat

/-- Blueprint `thm:batch-transformer` (batch transformer carrier):
`BmonT B M X := Fin B → M X`, the reader monad transformer at `Fin B`
applied to `M`, realized as Lean/Mathlib's `ReaderT (Fin B) M X`. -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
abbrev BmonT (B : ℕ) (M : Type → Type*) (X : Type) := ReaderT (Fin B) M X

variable {B : ℕ} {M : Type → Type*} {X Y : Type}

/-- Blueprint `thm:batch-transformer` (`lift_M`): the batch-constant
embedding of a bare `M`-effect, `lift_M := const` — definitionally
Lean core's own `MonadLift.monadLift` for `ReaderT`. -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
def liftM (m : M X) : BmonT B M X := fun _ => m

/-- Blueprint `thm:batch-transformer` (`lift_Bmon`): the certain-value
embedding of a plain batch `m : Bmon B X` (no inner effect yet),
`lift_Bmon(m) := m \seq Ret_M`, postcomposing with `M`'s own unit. -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
def liftBmon [Monad M] (m : Bmon B X) : BmonT B M X := fun b => pure (m b)

variable [Monad M] [LawfulMonad M]

omit [LawfulMonad M] in
/-- Blueprint `thm:batch-transformer` (`lift_M` is a monad morphism,
unit clause): `lift_M(Ret_M(a)) = Ret_{Bmon M}(a)`, since a constant
family trivially commutes with the diagonal bind. -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
theorem liftM_ret (x : X) : (liftM (pure x) : BmonT B M X) = pure x := rfl

omit [LawfulMonad M] in
/-- Blueprint `thm:batch-transformer` (`lift_M` is a monad morphism,
bind clause): `lift_M(m \bind k) = lift_M(m) \bind (lift_M \circ k)`. -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
theorem liftM_bind (m : M X) (k : X → M Y) :
    (liftM (m >>= k) : BmonT B M Y) = liftM m >>= fun x => liftM (k x) := rfl

omit [LawfulMonad M] in
/-- Blueprint `thm:batch-transformer` (`lift_Bmon` is a monad morphism,
unit clause): `lift_Bmon(Ret_{Bmon}(x)) = Ret_{Bmon M}(x)`. -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
theorem liftBmon_ret (x : X) : (liftBmon (Bmon.ret x) : BmonT B M X) = pure x := rfl

/-- Blueprint `thm:batch-transformer` (`lift_Bmon` is a monad morphism,
bind clause): `lift_Bmon(m \bind f) = lift_Bmon(m) \bind (lift_Bmon
\circ f)`, using `Ret_M`'s naturality and `M`'s own left unit law
(`pure_bind`). -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
theorem liftBmon_bind (m : Bmon B X) (f : X → Bmon B Y) :
    (liftBmon (Bmon.bind m f) : BmonT B M Y) =
      liftBmon m >>= fun x => liftBmon (f x) := by
  apply ReaderT.ext
  intro b
  change pure ((Bmon.bind m f) b) = pure (m b) >>= fun x => pure (f x b)
  rw [Bmon.bind, pure_bind]

/-- Blueprint `thm:batch-transformer` (Batch transformer): for every
strong monad `M` (`[Monad M] [LawfulMonad M]`, in particular for `M =
MS S` of `thm:semiring-monad-laws`, or `M = Idmon`), `BmonT B M` is
again a monad (Lean core's `LawfulMonad (ReaderT (Fin B) M)` instance,
BACKGROUND machinery — see the module doc above), and the two
canonical lifts `liftM`/`liftBmon` are monad morphisms. -/
theorem batchTransformer :
    (∀ x : X, (liftM (pure x) : BmonT B M X) = pure x) ∧
      (∀ (m : M X) (k : X → M Y),
        (liftM (m >>= k) : BmonT B M Y) = liftM m >>= fun x => liftM (k x)) ∧
      (∀ x : X, (liftBmon (Bmon.ret x) : BmonT B M X) = pure x) ∧
      (∀ (m : Bmon B X) (f : X → Bmon B Y),
        (liftBmon (Bmon.bind m f) : BmonT B M Y) =
          liftBmon m >>= fun x => liftBmon (f x)) :=
  ⟨liftM_ret, liftM_bind, liftBmon_ret, liftBmon_bind⟩

/-! ### `thm:pointwise-eval`, part 1: `ev_i` is a monad morphism -/

/-- Blueprint `thm:pointwise-eval` (evaluation): `ev_i(m) := m(i)`,
evaluating a batched `M`-computation at index `i`. -/
-- (A1 bijection-law companion of `ev_isMonadMorphism`, content.tex thm:pointwise-eval)
@[blueprint_internal]
def ev (i : Fin B) (m : BmonT B M X) : M X := m i

omit [LawfulMonad M] in
/-- Blueprint `thm:pointwise-eval` (`ev_i` is a monad morphism, PART 1
ONLY — unconditional, no batch-naturality hypothesis needed): `ev_i`
commutes with `Ret` and `\bind`. Part 2 (commutation with the Kleisli
interpretation under batch-naturality) is `content.tex`'s
`thm:pointwise-eval-kleisli`, left unformalized — see the module doc
above. -/
theorem ev_isMonadMorphism (i : Fin B) :
    (∀ x : X, ev i (pure x : BmonT B M X) = pure x) ∧
      (∀ (m : BmonT B M X) (f : X → BmonT B M Y),
        ev i (m >>= f) = ev i m >>= fun x => ev i (f x)) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

end NeSyCat
