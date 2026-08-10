/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.StatisticalLayer.Batching.BatchTransformer

/-!
# Pointwise evaluation commutes with feed-forward composites (C3-B4b)

Toward blueprint item `thm:pointwise-eval-kleisli`
(`blueprint/src/content.tex`, §"Batching"): under the batch-naturality
hypothesis, evaluation `ev_i` commutes with the Kleisli interpretation
of feed-forward composites.

**Honest scope (disclosed, C3-B4b).** The env's parenthetical cites
`def:kleisli-interpretation`, whose Lean form (`Fm.sem`,
`NeSyCat/GrammaticalLayer/Kleisli.lean`) lives over an abstract
`CatInterpretation`; instantiating it at the concrete `M`/`BmonT B M`
pair needs a full CD-category instance at `Type` (cartesian monoidal
structure, chosen diagonal comonoids, `CategoryTheory.Monad`
realizations of `M` and `BmonT B M`, a strong monad morphism `ev_i`
between them) plus a monad-morphism commutation theorem proved by
mutual induction over `Tm.sem`/`Fm.sem`'s six tactic-elaborated
clauses — infrastructure beyond this ticket (see
`.foreman/scratch/C3-B4b-report.md` for the exact remainder). What IS
proved here is the env's own proof plan at the concrete level the
batched reading lives at: a feed-forward program model `BatchProgram`
(the `PulloutChain` precedent, C3-B8) whose constructors mirror the
clause SHAPES of `def:kleisli-interpretation` — `ret` (`η`, the
variable clause), `sym` (a bound symbol continuation, the
functional-term/atomic-formula clauses' `⨟_∘`), `comp` (Kleisli
sequencing, the substitution clause), `pair` (shared-context tensor
via double strength, the argument-list clauses), `node` (an `n`-ary
connective/quantifier interpretation consuming the sub-results, the
compound/quantified-formula clauses) — with TWO readings: `run` (the
`M`-reading) and `runB` (the `BmonT B M`-reading, where each symbol
leaf is `lift_M`-embedded and each `node` op is applied index by
index — batch-naturality embodied structurally, exactly the env's
"defined pointwise across the batch" hypothesis). The theorem
`BatchProgram.ev_runB` proves `ev i ∘ runB = run` by structural
induction — `thm:pointwise-eval` (`ev_isMonadMorphism`) gives the
`ret`/`comp`/`pair` cases, batch-naturality the `sym`/`node` cases,
one clause shape at a time, exactly the env's own proof sketch — and
`BatchProgram.runBatch_apply` derives the env's display equation
`⟦φ⟧^{Bmon M}(s)(i) = ⟦φ⟧^{M}(s_i)` for a batch `s : Fin B → X` of
inputs. The env carries NO `\lean`/`\leanok` mark: this model is
faithful to the clause structure but is not literally `Fm.sem`, and
marking over less than the env states is not an option.
-/

namespace NeSyCat

universe u

variable {B : ℕ} {M : Type → Type u}

/-- Toward `thm:pointwise-eval-kleisli` (C3-B4b): the feed-forward
program model over an effect monad `M`, constructors mirroring the
clause shapes of `def:kleisli-interpretation` (module doc above). A
`sym` leaf stores the UNBATCHED symbol interpretation `k : X → M Y`; a
`node` stores the unbatched `n`-ary connective/quantifier
interpretation `op : (M Ω)^n → M Ω`. The batched reading `runB` below
embeds each of them per the batch-naturality hypothesis, so the model
quantifies exactly over batch-natural symbol data. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the
-- feed-forward program model (PulloutChain precedent), env unmarked
inductive BatchProgram (M : Type → Type u) : Type → Type → Type (u + 1)
  | ret {X : Type} : BatchProgram M X X
  | sym {X Y : Type} (k : X → M Y) : BatchProgram M X Y
  | comp {X Y Z : Type} (p : BatchProgram M X Y) (q : BatchProgram M Y Z) :
      BatchProgram M X Z
  | pair {X Y Z : Type} (p : BatchProgram M X Y) (q : BatchProgram M X Z) :
      BatchProgram M X (Y × Z)
  | node {X W : Type} (n : ℕ) (op : (Fin n → M W) → M W)
      (ps : Fin n → BatchProgram M X W) : BatchProgram M X W

variable [Monad M]

/-- Toward `thm:pointwise-eval-kleisli`: the plain `M`-reading
`⟦·⟧^{M}` of a feed-forward program — `η` at `ret`, the symbol's own
continuation at `sym`, Kleisli sequencing at `comp`, the do-form
double strength at `pair`, the `n`-ary interpretation applied to the
sub-results at `node`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the
-- M-reading of the program model
def BatchProgram.run : BatchProgram M X Y → X → M Y
  | .ret => fun x => pure x
  | .sym k => k
  | .comp p q => fun x => p.run x >>= q.run
  | .pair p q => fun x => p.run x >>= fun y => q.run x >>= fun z => pure (y, z)
  | .node _ op ps => fun x => op fun t => (ps t).run x

/-- Toward `thm:pointwise-eval-kleisli`: the batched
`Bmon M`-reading `⟦·⟧^{Bmon M}` — every `sym` leaf is `lift_M`-embedded
(`𝓘^{Bmon M}(f) = 𝓘^{M}(f) ⨟ lift_M`) and every `node` op is applied
index by index, the env's batch-naturality hypothesis embodied
structurally; `ret`/`comp`/`pair` use `BmonT B M`'s own monad
structure (`thm:batch-transformer`). -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the
-- batched Bmon-M-reading, batch-naturality structural
def BatchProgram.runB (B : ℕ) : BatchProgram M X Y → X → BmonT B M Y
  | .ret => fun x => pure x
  | .sym k => fun x => liftM (k x)
  | .comp p q => fun x => p.runB B x >>= q.runB B
  | .pair p q => fun x =>
      p.runB B x >>= fun y => q.runB B x >>= fun z => pure (y, z)
  | .node _ op ps => fun x b => op fun t => (ps t).runB B x b

/-- Toward `thm:pointwise-eval-kleisli` (C3-B4b), the commutation
theorem at the program model: `ev_i` commutes with the batched reading
of every feed-forward program of batch-natural symbols,
`ev_i(⟦p⟧^{Bmon M}(x)) = ⟦p⟧^{M}(x)`. Structural induction: the
`ret`/`comp`/`pair` cases are `thm:pointwise-eval`'s monad-morphism
clauses (`ev_isMonadMorphism`, definitional at `ReaderT`'s diagonal
bind), the `sym` case is `ev_i ∘ lift_M = id`, the `node` case is the
index-by-index application evaluated at `i` — one clause shape at a
time, the env's own proof sketch. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the
-- ev-commutation theorem at the program model, env stays unmarked
theorem BatchProgram.ev_runB (i : Fin B) :
    ∀ (p : BatchProgram M X Y) (x : X), ev i (p.runB B x) = p.run x
  | .ret, x => rfl
  | .sym _, x => rfl
  | .comp p q, x => by
    change p.runB B x i >>= (fun y => q.runB B y i) = p.run x >>= q.run
    rw [show p.runB B x i = p.run x from ev_runB i p x]
    exact bind_congr fun y => ev_runB i q y
  | .pair p q, x => by
    change (p.runB B x i >>= fun y => q.runB B x i >>= fun z => pure (y, z)) =
      (p.run x >>= fun y => q.run x >>= fun z => pure (y, z))
    rw [show p.runB B x i = p.run x from ev_runB i p x,
      show q.runB B x i = q.run x from ev_runB i q x]
  | .node n op ps, x => congrArg op (funext fun t => ev_runB i (ps t) x)

/-- Toward `thm:pointwise-eval-kleisli`: the batched reading run over
a batch `s : Fin B → X` of inputs, each index reading its own input —
the `⟦φ⟧^{Bmon M}(s)` of the env's display equation. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the
-- batched-input reading feeding the display equation
def BatchProgram.runBatch (p : BatchProgram M X Y) (s : Fin B → X) :
    BmonT B M Y :=
  fun b => p.runB B (s b) b

/-- Toward `thm:pointwise-eval-kleisli`: the env's display equation,
`⟦p⟧^{Bmon M}(s)(i) = ⟦p⟧^{M}(s_i)` for a batch `s : Fin B → X` —
immediate from `BatchProgram.ev_runB` at `x := s i`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the
-- display equation at a batch of inputs
theorem BatchProgram.runBatch_apply (p : BatchProgram M X Y)
    (s : Fin B → X) (i : Fin B) : p.runBatch s i = p.run (s i) :=
  p.ev_runB i (s i)

-- (completeness census: compiler byproducts of `BatchProgram`'s
-- inductive, post-hoc tagged per the `Tm`/`Fm`/`PulloutChain`
-- precedent -- not blueprint-cited, plumbing)
attribute [blueprint_internal] BatchProgram.brecOn.go BatchProgram.brecOn.eq
  BatchProgram.ctorElimType

end NeSyCat
