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
batch-naturality hypothesis) is not formalized HERE, but it IS proved:
`pointwise_eval_kleisli` in `PointwiseKleisli.lean`, cited by
`thm:pointwise-eval-kleisli`, which carries `\lean`/`\leanok` as of
C4-T3. The route was not the one this doc once predicted: rather than a
generic Kleisli interpretation over an arbitrary strong monad, it goes
through `def:interpretation-morphism` and `lem:kleisli-formula-natural`,
instantiated at `ev i`.
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

omit [LawfulMonad M] in
/-- Blueprint `thm:batch-transformer` (`lift_Bmon` is a monad morphism,
bind clause): `lift_Bmon(m \bind f) = lift_Bmon(m) \bind (lift_Bmon
\circ f)`, using `Ret_M`'s naturality and `M`'s own left unit law.

MINIMAL HYPOTHESIS (C3-EXEC-FIX2). This is the ONLY clause of the batch
layer that uses a monad law at all, and the law it uses is the LEFT UNIT
law alone — not associativity of `\bind`, and not the right unit law. It
is therefore stated with that one law as an explicit hypothesis `hleft`,
at exactly the two value types `X`/`Y` it is applied at, rather than with
the whole `[LawfulMonad M]` bundle: under `[LawfulMonad M]` the
hypothesis is discharged by Mathlib/core's `pure_bind` (see
`batchTransformer_of_lawful` below, which is the pre-C3-EXEC-FIX2
statement recovered verbatim). -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
theorem liftBmon_bind (hleft : ∀ (x : X) (g : X → M Y), (pure x : M X) >>= g = g x)
    (m : Bmon B X) (f : X → Bmon B Y) :
    (liftBmon (Bmon.bind m f) : BmonT B M Y) =
      liftBmon m >>= fun x => liftBmon (f x) := by
  apply ReaderT.ext
  intro b
  change pure ((Bmon.bind m f) b) = pure (m b) >>= fun x => pure (f x b)
  rw [Bmon.bind, hleft]

omit [LawfulMonad M] in
/-- Blueprint `thm:batch-transformer` (Batch transformer): for `M` a
monad (in particular for `M = MS S` of `thm:semiring-monad-laws`, or `M
= Idmon`), `BmonT B M` is again a monad (Lean core's `LawfulMonad
(ReaderT (Fin B) M)` instance, BACKGROUND machinery — see the module
doc above), and the two canonical lifts `liftM`/`liftBmon` are monad
morphisms.

MINIMAL HYPOTHESIS (C3-EXEC-FIX2). `[LawfulMonad M]` is NOT assumed.
Three of the four morphism clauses are definitional (`liftM_ret`,
`liftM_bind`, `liftBmon_ret`, each `rfl`); the fourth, `liftBmon_bind`,
consumes `M`'s left unit law and nothing else, carried here as the
explicit hypothesis `hleft`. `batchTransformer_of_lawful` below recovers
the pre-C3-EXEC-FIX2 statement verbatim by discharging `hleft` with
`pure_bind`, so this statement implies that one. Note that the "`BmonT B
M` is again a monad" half of the informal reading is background
machinery cited in the module doc, not a conjunct of this theorem's own
Lean statement; that half does need `[LawfulMonad M]`, which is why the
blueprint's own sentence still names a lawful `M` for it. -/
theorem batchTransformer
    (hleft : ∀ (x : X) (g : X → M Y), (pure x : M X) >>= g = g x) :
    (∀ x : X, (liftM (pure x) : BmonT B M X) = pure x) ∧
      (∀ (m : M X) (k : X → M Y),
        (liftM (m >>= k) : BmonT B M Y) = liftM m >>= fun x => liftM (k x)) ∧
      (∀ x : X, (liftBmon (Bmon.ret x) : BmonT B M X) = pure x) ∧
      (∀ (m : Bmon B X) (f : X → Bmon B Y),
        (liftBmon (Bmon.bind m f) : BmonT B M Y) =
          liftBmon m >>= fun x => liftBmon (f x)) :=
  ⟨liftM_ret, liftM_bind, liftBmon_ret, liftBmon_bind hleft⟩

/-- The pre-C3-EXEC-FIX2 form of `batchTransformer`, recovered verbatim:
under `[LawfulMonad M]` the left unit hypothesis is `pure_bind`. Kept as
a machine-checked witness that the weakened statement implies the one it
replaced. -/
-- (A1 bijection-law companion of `batchTransformer`, content.tex thm:batch-transformer)
@[blueprint_internal]
theorem batchTransformer_of_lawful :
    (∀ x : X, (liftM (pure x) : BmonT B M X) = pure x) ∧
      (∀ (m : M X) (k : X → M Y),
        (liftM (m >>= k) : BmonT B M Y) = liftM m >>= fun x => liftM (k x)) ∧
      (∀ x : X, (liftBmon (Bmon.ret x) : BmonT B M X) = pure x) ∧
      (∀ (m : Bmon B X) (f : X → Bmon B Y),
        (liftBmon (Bmon.bind m f) : BmonT B M Y) =
          liftBmon m >>= fun x => liftBmon (f x)) :=
  batchTransformer fun x g => pure_bind x g

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

/-! ### `thm:batch-exactness`: the batch layer's laws hold for an
arbitrary carrier -/

omit [LawfulMonad M] in
/-- Blueprint `thm:batch-exactness` (Batching is exact): every clause of
`thm:batch-transformer` and `thm:pointwise-eval`, bundled, for the value
types `X Y : Type` completely unconstrained (no `Semiring`/`LatCSRng`/
lattice hypothesis, no hypothesis whatsoever on the value carrier) and
`M` an arbitrary monad, NOT assumed lawful. The value types are `Type`,
NOT `Type*`: the
file's `variable` block fixes `{X Y : Type}` because the inner monad is
taken at `M : Type → Type*`, so its value types are small. Cited verbatim
from `batchTransformer`/`ev_isMonadMorphism`, per the calibrated reuse
principle: nothing new is proved here, the point is that the statement
names no algebraic class and no already-structured carrier at all —
mechanically confirmed by `scripts/blueprint.sh`'s classification gate
(C3-EXEC item 2, corrected and gated at C3-EXEC-FIX), which finds zero
algebraic markers anywhere in this declaration's type. `[Monad M]` is
not counted as such a marker, deliberately: it constrains the AMBIENT
monad, not the value carrier, and this theorem assumes rather than
proves it.

MINIMAL HYPOTHESIS (C3-EXEC-FIX2). `[LawfulMonad M]` is NOT assumed.
Five of the six clauses are definitional — see `batch_layer_exact_lawFree`
below, which states exactly those five with no monad law whatsoever — and
the sixth, `liftBmon`'s bind clause, consumes `M`'s LEFT UNIT law and
nothing else, carried here as the explicit hypothesis `hleft` at exactly
the two value types it is applied at. In particular no clause uses
associativity of `\bind`. `batch_layer_exact_of_lawful` below recovers
the pre-C3-EXEC-FIX2 statement verbatim by discharging `hleft` with
`pure_bind`, so this statement implies that one. -/
theorem batch_layer_exact (i : Fin B)
    (hleft : ∀ (x : X) (g : X → M Y), (pure x : M X) >>= g = g x) :
    (∀ x : X, (liftM (pure x) : BmonT B M X) = pure x) ∧
      (∀ (m : M X) (k : X → M Y),
        (liftM (m >>= k) : BmonT B M Y) = liftM m >>= fun x => liftM (k x)) ∧
      (∀ x : X, (liftBmon (Bmon.ret x) : BmonT B M X) = pure x) ∧
      (∀ (m : Bmon B X) (f : X → Bmon B Y),
        (liftBmon (Bmon.bind m f) : BmonT B M Y) =
          liftBmon m >>= fun x => liftBmon (f x)) ∧
      (∀ x : X, ev i (pure x : BmonT B M X) = pure x) ∧
      (∀ (m : BmonT B M X) (f : X → BmonT B M Y),
        ev i (m >>= f) = ev i m >>= fun x => ev i (f x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (batchTransformer (X := X) (Y := Y) hleft).1
  · exact (batchTransformer (X := X) (Y := Y) hleft).2.1
  · exact (batchTransformer (X := X) (Y := Y) hleft).2.2.1
  · exact (batchTransformer (X := X) (Y := Y) hleft).2.2.2
  · exact (ev_isMonadMorphism (X := X) (Y := Y) i).1
  · exact (ev_isMonadMorphism (X := X) (Y := Y) i).2

omit [LawfulMonad M] in
/-- The five clauses of `batch_layer_exact` that hold with NO monad law
at all — `liftM`'s two morphism clauses, `liftBmon`'s unit clause, and
both of `ev_i`'s — for an arbitrary `[Monad M]`. Every one of them is
closed by `rfl` at its own declaration (`liftM_ret`, `liftM_bind`,
`liftBmon_ret`, `ev_isMonadMorphism`): they are identities of the
`ReaderT` encoding itself, true of any bind whatever, lawful or not.
This is the statement behind the rendered document's claim that only one
clause of the batch layer consumes a monad law. -/
-- (A1 bijection-law companion of `batch_layer_exact`, content.tex thm:batch-exactness)
@[blueprint_internal]
theorem batch_layer_exact_lawFree (i : Fin B) :
    (∀ x : X, (liftM (pure x) : BmonT B M X) = pure x) ∧
      (∀ (m : M X) (k : X → M Y),
        (liftM (m >>= k) : BmonT B M Y) = liftM m >>= fun x => liftM (k x)) ∧
      (∀ x : X, (liftBmon (Bmon.ret x) : BmonT B M X) = pure x) ∧
      (∀ x : X, ev i (pure x : BmonT B M X) = pure x) ∧
      (∀ (m : BmonT B M X) (f : X → BmonT B M Y),
        ev i (m >>= f) = ev i m >>= fun x => ev i (f x)) :=
  ⟨liftM_ret, liftM_bind, liftBmon_ret,
    (ev_isMonadMorphism (X := X) (Y := Y) i).1,
    (ev_isMonadMorphism (X := X) (Y := Y) i).2⟩

/-- The pre-C3-EXEC-FIX2 form of `batch_layer_exact`, recovered verbatim:
under `[LawfulMonad M]` the left unit hypothesis is `pure_bind`. Kept as
a machine-checked witness that the weakened statement implies the one it
replaced. -/
-- (A1 bijection-law companion of `batch_layer_exact`, content.tex thm:batch-exactness)
@[blueprint_internal]
theorem batch_layer_exact_of_lawful (i : Fin B) :
    (∀ x : X, (liftM (pure x) : BmonT B M X) = pure x) ∧
      (∀ (m : M X) (k : X → M Y),
        (liftM (m >>= k) : BmonT B M Y) = liftM m >>= fun x => liftM (k x)) ∧
      (∀ x : X, (liftBmon (Bmon.ret x) : BmonT B M X) = pure x) ∧
      (∀ (m : Bmon B X) (f : X → Bmon B Y),
        (liftBmon (Bmon.bind m f) : BmonT B M Y) =
          liftBmon m >>= fun x => liftBmon (f x)) ∧
      (∀ x : X, ev i (pure x : BmonT B M X) = pure x) ∧
      (∀ (m : BmonT B M X) (f : X → BmonT B M Y),
        ev i (m >>= f) = ev i m >>= fun x => ev i (f x)) :=
  batch_layer_exact i fun x g => pure_bind x g

end NeSyCat
