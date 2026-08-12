/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.StatisticalLayer.Batching.BatchTransformer
import NeSyCat.StatisticalLayer.Batching.TypeInstantiation
import NeSyCat.GrammaticalLayer.InterpretationMorphism

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
inputs. That model carried no blueprint mark, since it is faithful to
the clause structure but is not literally `Fm.sem`.

## The theorem itself (C4-T3)

`pointwise_eval_kleisli` below IS `thm:pointwise-eval-kleisli`, over
`Fm.sem` itself. `BatchNaturalReading` bundles an unbatched Kleisli
interpretation at `def:type-cat-interpretation`'s realization of `𝓜`
together with a batched one at `Bmon 𝓜`, and the four batch-naturality
laws relating their symbol data; `evMorphism` turns that bundle into a
morphism of interpretations (`def:interpretation-morphism`) at `ev i`,
and `lem:kleisli-formula-natural` (`Fm.sem_natural`) does the induction.

**Where the batch lives (disclosed modelling choice).** The two readings
assign the SAME object to a domain symbol, the same truth object, the
same variable enumeration and the same parameter spaces; only the monad
differs. This is what makes the env's own hypothesis formula
`𝓘^{Bmon 𝓜}(f) = 𝓘^{𝓜}(f) ⨟ lift_{𝓜}` typecheck: `lift_M` embeds an
`𝓜`-effect into a `Bmon 𝓜`-effect and leaves the value object alone. The
batch of inputs enters at the top, index by index (`semBatchOn`), exactly
as `BatchProgram.runBatch` above already does, and `⟦φ⟧^{Bmon 𝓜}(s)(i)`
then means what the env writes: run the batched reading on the batch's
`i`-th input and read the result at index `i`.

**Why the object family is not batched (a corrected expectation).** The
alternative reading, in which a domain symbol is sent to `Bidx → 𝓘(S)`
while the truth object stays shared, makes the hypothesis UNSATISFIABLE
whenever the signature has a relation symbol and `B ≥ 2`: `𝓘(R)` lands in
`Ω`, so `relMorK_compat` would demand one truth value equal to the
unbatched reading of every slice of the batch at once, and slices differ.
Batching the truth object too repairs satisfiability but changes the
env's display, which then needs a second read at `i`. The reading used
here is the only one of the three that keeps both the env's hypothesis
formula and the env's display equation.

**Scope disclosure.** Batch-naturality is satisfiable symbol by symbol
whenever a symbol's domain and codomain carry the same monad marker, or
its domain is pure and its codomain effectful: at a `○`-marked codomain
the batch-constant lift `𝓘(f) ⨟ lift_M` works, and at matching markers
the index-by-index application works. It is NOT satisfiable for `B ≥ 2`
at a symbol that consumes an effect and returns a pure value, that is, a
relation symbol with a `○`-marked argument, or a function symbol with a
`○`-marked argument and an `Id`-marked result: reading the argument at
index `i` and producing one shared pure value forces that value to be
independent of `i`. Such a symbol has no batch-natural batched reading,
and this theorem says nothing about a signature that uses one.
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

section BatchInstantiation

open CategoryTheory MonoidalCategory

variable {sigA : CatSignature} {sigB : LogSignature} {sigG : DomSignature}
variable {B : ℕ} {M : Type → Type} [Monad M] [LawfulMonad M]

attribute [local instance] CDCategory.instCat CDCategory.instMonoidal CDCategory.instSymmetric

/-- Toward `thm:pointwise-eval-kleisli`: the canonical strength of
`def:type-strength` read as the strength datum
`def:feed-forward` needs, at `def:type-cat-interpretation`'s realization. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: typeStrength as
-- a StrongCatInterpretation
noncomputable def typeStrongCat (sigA : CatSignature) (M : Type → Type) [Monad M]
    [LawfulMonad M] : StrongCatInterpretation (typeCatInterpretation sigA M) where
  strength {X Y} := ↾ fun p : X × M Y => (typeStrength p : M (X × Y))

/-- Toward `thm:pointwise-eval-kleisli`: naturality of the canonical
strength in both slots, at the level of values. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: naturality of
-- the canonical strength in both slots at once
theorem typeStrength_natural_pair {X₁ X₂ Y₁ Y₂ : Type} (a : X₁ → X₂) (b : Y₁ → Y₂)
    (x : X₁) (my : M Y₁) :
    typeStrength (a x, b <$> my) = Prod.map a b <$> typeStrength (x, my) := by
  simp [typeStrength]

/-- Toward `thm:pointwise-eval-kleisli`: the batched categorical
interpretation, `def:type-cat-interpretation` at the batch transform
`Bmon 𝓜` in place of `𝓜`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- categorical interpretation
noncomputable abbrev batchCat (sigA : CatSignature) (B : ℕ) (M : Type → Type)
    [Monad M] [LawfulMonad M] : CatInterpretation sigA :=
  typeCatInterpretation sigA (BmonT B M)
/-- Toward `thm:pointwise-eval-kleisli`: `ev_i` at one marked slot. Both
readings assign the same object to a domain symbol, so an `Id`-marked slot
is carried by the identity; a `○`-marked slot carries a batched
computation, read at index `i`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i at one
-- marked slot
noncomputable def evAt (i : Fin B) (X : Type) :
    (m : MonSym) → ((batchCat sigA B M).interpretMon m).obj X ⟶
      ((typeCatInterpretation sigA M).interpretMon m).obj X
  | .id => 𝟙 X
  | .mon => ↾ fun c : BmonT B M X => ev i c

/-- Toward `thm:pointwise-eval-kleisli`: `ev_i` on a marked-symbol list's
tensor, slot by slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i on a
-- marked-symbol list's tensor
noncomputable def evMS {sigG : DomSignature} (i : Fin B) (dom : sigG.Dom → Type) :
    (l : List (MonSym × sigG.Dom)) →
      interpretMS (batchCat sigA B M) dom l ⟶
        interpretMS (typeCatInterpretation sigA M) dom l
  | [] => 𝟙 (𝟙_ (batchCat sigA B M).cd.C)
  | p :: l => evAt i (dom p.2) p.1 ⊗ₘ evMS i dom l

/-- Toward `thm:pointwise-eval-kleisli`: `ev_i` on a tensor power of the
truth object, slot by slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i on a
-- tensor power of the truth object
noncomputable def evPow (i : Fin B) (Om : Type) (m : MonSym) :
    (n : ℕ) → interpretPow (batchCat sigA B M) Om m n ⟶
      interpretPow (typeCatInterpretation sigA M) Om m n
  | 0 => 𝟙 (𝟙_ (batchCat sigA B M).cd.C)
  | n + 1 => evAt i Om m ⊗ₘ evPow i Om m n

/-- Toward `thm:pointwise-eval-kleisli`: the per-slot transport of
`def:interpretation-morphism` at `ev_i`'s data is `ev_i` at that slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: markerMor at
-- ev_i's data
theorem markerMor_ev (i : Fin B) (X : Type) (m : MonSym) :
    markerMor (I := batchCat sigA B M) (M₂ := CategoryTheory.ofTypeMonad M)
        (evMonadHom i).toNatTrans m (𝟙 X) = evAt i X m := by
  cases m with
  | id => rfl
  | mon =>
    rw [markerMor_mon,
      CategoryTheory.Functor.map_id (self := (CategoryTheory.ofTypeMonad M).toFunctor) (X := X)]
    exact Category.comp_id _

/-- Toward `thm:pointwise-eval-kleisli`: the induced morphism on a tensor
power of the truth object is `ev_i` slot by slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: interpretPowMor
-- at ev_i's data
theorem interpretPowMor_ev (i : Fin B) (Om : Type) (m : MonSym) :
    ∀ n : ℕ,
      interpretPowMor (I := batchCat sigA B M) (M₂ := CategoryTheory.ofTypeMonad M)
          (evMonadHom i).toNatTrans (𝟙 Om) m n = evPow i Om m n
  | 0 => rfl
  | n + 1 => by
    change markerMor _ m (𝟙 Om) ⊗ₘ
        interpretPowMor (I := batchCat sigA B M) (M₂ := CategoryTheory.ofTypeMonad M)
          (evMonadHom i).toNatTrans (𝟙 Om) m n
      = evAt i Om m ⊗ₘ evPow i Om m n
    rw [markerMor_ev i Om m, interpretPowMor_ev i Om m n]
    rfl

/-- Toward `thm:pointwise-eval-kleisli`: an unbatched reading of a grammar
together with a batched one that is BATCH-NATURAL over it. The unbatched
reading is a Kleisli interpretation (`def:kleisli-interpretation`) at
`def:type-cat-interpretation`'s realization of `𝓜`. The batched reading is
the same interpretation with `Bmon 𝓜` in place of `𝓜`: the objects, the
truth object, the variable enumeration and the parameter spaces are shared,
only the monad changes, and the batched reading has its own symbol data.
Batch-naturality is the four laws below, each saying that the batched
interpretation of a symbol, read at index `i`, is the unbatched one. At a
symbol whose codomain is `○`-marked and whose domain is not, the canonical
solution is the env's own formula, the batch-constant lift
`𝓘^{Bmon 𝓜}(f) = 𝓘^{𝓜}(f) ⨟ lift_{𝓜}`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the two readings
-- and the batch-naturality hypothesis, bundled
structure BatchNaturalReading (sigA : CatSignature) (sigB : LogSignature)
    (sigG : DomSignature) (B : ℕ) (M : Type → Type) [Monad M] [LawfulMonad M] where
  /-- The unbatched logical interpretation. -/
  J : LogInterpretation (typeCatInterpretation sigA M) sigB
  /-- The unbatched domain interpretation. -/
  D : DomInterpretation (typeCatInterpretation sigA M) J sigG
  /-- The unbatched Kleisli interpretation. -/
  K : KleisliInterpretation (typeCatInterpretation sigA M) (typeStrongCat sigA M) J D
  /-- The batched interpretation of each connective symbol. -/
  connMorB : ∀ c : sigB.Conn,
    interpretPow (batchCat sigA B M) J.Ω (sigB.connMonad c) (sigB.connArity c) ⟶
      ((batchCat sigA B M).interpretMon (sigB.connMonad c)).obj J.Ω
  /-- The batched interpretation of each quantifier symbol, at every arity. -/
  quanMorB : ∀ (Q : sigB.Quan) (n : ℕ),
    interpretPow (batchCat sigA B M) J.Ω (sigB.quanMonad Q) n ⟶
      ((batchCat sigA B M).interpretMon (sigB.quanMonad Q)).obj J.Ω
  /-- The batched parameter-threaded morphism of each function symbol. No law
  constrains it: the grammar supplies no syntax for passing parameters, so
  no clause of the formula semantics reads it. -/
  funMorB : ∀ f : sigG.Fun,
    (batchCat sigA B M).act (interpretSpc (batchCat sigA B M) D.spcObj (sigG.fpar f))
        (interpretMS (batchCat sigA B M) D.domObj (sigG.fdom f)) ⟶
      interpretMS (batchCat sigA B M) D.domObj (sigG.fcod f)
  /-- The batched parameter-threaded morphism of each relation symbol,
  unconstrained for the same reason. -/
  relMorB : ∀ R : sigG.Rel,
    (batchCat sigA B M).act (interpretSpc (batchCat sigA B M) D.spcObj (sigG.rpar R))
        (interpretMS (batchCat sigA B M) D.domObj (sigG.rari R)) ⟶ J.Ω
  /-- The batched interpretation of each function symbol at its
  parameter-free instance. -/
  funMorKB : ∀ f : sigG.Fun,
    interpretMS (batchCat sigA B M) D.domObj (sigG.fdom f) ⟶
      interpretMS (batchCat sigA B M) D.domObj (sigG.fcod f)
  /-- The batched interpretation of each relation symbol at its
  parameter-free instance. -/
  relMorKB : ∀ R : sigG.Rel,
    interpretMS (batchCat sigA B M) D.domObj (sigG.rari R) ⟶ J.Ω
  /-- Batch-naturality at every function symbol: applying the batched
  interpretation and then reading index `i` is reading index `i` and then
  applying the unbatched interpretation. -/
  funMorK_batchNatural : ∀ (i : Fin B) (f : sigG.Fun),
    funMorKB f ≫ evMS i D.domObj (sigG.fcod f)
      = evMS i D.domObj (sigG.fdom f) ≫ K.funMorK f
  /-- Batch-naturality at every relation symbol. -/
  relMorK_batchNatural : ∀ (i : Fin B) (R : sigG.Rel),
    relMorKB R = evMS i D.domObj (sigG.rari R) ≫ K.relMorK R
  /-- Batch-naturality at every connective symbol. -/
  connMor_batchNatural : ∀ (i : Fin B) (c : sigB.Conn),
    connMorB c ≫ evAt i J.Ω (sigB.connMonad c)
      = evPow i J.Ω (sigB.connMonad c) (sigB.connArity c) ≫ J.connMor c
  /-- Batch-naturality at every quantifier symbol, at every arity. -/
  quanMor_batchNatural : ∀ (i : Fin B) (Q : sigB.Quan) (n : ℕ),
    quanMorB Q n ≫ evAt i J.Ω (sigB.quanMonad Q)
      = evPow i J.Ω (sigB.quanMonad Q) n ≫ J.quanMor Q n

namespace BatchNaturalReading

variable (P : BatchNaturalReading sigA sigB sigG B M)

/-- Toward `thm:pointwise-eval-kleisli`: the batched logical
interpretation. Both readings share one truth object. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- logical interpretation
noncomputable def logB : LogInterpretation (batchCat sigA B M) sigB where
  Ω := P.J.Ω
  connMor := P.connMorB
  quanMor := P.quanMorB

/-- Toward `thm:pointwise-eval-kleisli`: the batched domain interpretation.
Both readings assign the same object to a domain symbol and the same object
to a parameter space; the batch lives in the monad. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- domain interpretation
noncomputable def domB : DomInterpretation (batchCat sigA B M) P.logB sigG where
  domObj := P.D.domObj
  spcObj := P.D.spcObj
  funMor := P.funMorB
  relMor := P.relMorB

/-- Toward `thm:pointwise-eval-kleisli`: the batched Kleisli interpretation.
Its variable enumeration is the unbatched one: a quantifier ranges over a
domain fixed by the signature, the same domain at every index. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- Kleisli interpretation
noncomputable def kleisliB :
    KleisliInterpretation (batchCat sigA B M) (typeStrongCat sigA (BmonT B M))
      P.logB P.domB where
  decEqVar := P.K.decEqVar
  funMorK := P.funMorKB
  relMorK := P.relMorKB
  varCard := P.K.varCard
  varPt := P.K.varPt

/-- Toward `thm:pointwise-eval-kleisli`: the induced morphism on a
marked-symbol list's tensor is `ev_i` slot by slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: interpretMSMor
-- at ev_i's data
theorem interpretMSMor_ev (i : Fin B) :
    ∀ l : List (MonSym × sigG.Dom),
      interpretMSMor P.domB P.D (evMonadHom i).toNatTrans (fun S => 𝟙 (P.D.domObj S)) l
        = evMS i P.D.domObj l
  | [] => rfl
  | p :: l => by
    change interpretMSMor P.domB P.D (evMonadHom i).toNatTrans
          (fun S => 𝟙 (P.D.domObj S)) (p :: l)
      = evAt (sigA := sigA) (M := M) i (P.D.domObj p.2) p.1 ⊗ₘ evMS i P.D.domObj l
    rw [← markerMor_ev (sigA := sigA) (M := M) i (P.D.domObj p.2) p.1,
      ← interpretMSMor_ev i l]
    rfl

end BatchNaturalReading

omit [LawfulMonad M] in
/-- Toward `thm:pointwise-eval-kleisli`: the two readings' strengths agree
along `ev_i`, `lem:ev-strength-natural` in morphism form. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: strength
-- compatibility along ev_i, in morphism form
theorem typeStrength_compat_hom (i : Fin B) (X Y : Type) :
    (↾ fun p : X × BmonT B M Y => typeStrength p) ≫ (↾ fun c : BmonT B M (X × Y) => ev i c)
      = ((𝟙 X) ⊗ₘ (↾ fun c : BmonT B M Y => ev i c)) ≫
        (↾ fun p : X × M Y => typeStrength p) := by
  refine ConcreteCategory.hom_ext _ _ fun p => ?_
  exact ev_strength_natural i p.1 p.2

/-- Toward `thm:pointwise-eval-kleisli`: the unbatched strength is natural
in both slots, `lem:type-strength-laws` in morphism form. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: naturality of
-- the unbatched strength, in morphism form
theorem typeStrength_natural_hom {X₁ X₂ Y₁ Y₂ : Type} (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) :
    (a ⊗ₘ (CategoryTheory.ofTypeMonad M).map b) ≫ (↾ fun p : X₂ × M Y₂ => typeStrength p)
      = (↾ fun p : X₁ × M Y₁ => typeStrength p) ≫
        (CategoryTheory.ofTypeMonad M).map (a ⊗ₘ b) := by
  refine ConcreteCategory.hom_ext _ _ fun p => ?_
  exact typeStrength_natural_pair (M := M) (⇑a) (⇑b) p.1 p.2

/-- Blueprint `thm:pointwise-eval-kleisli` (the morphism at `ev_i`): under
batch-naturality, `ev_i` is a morphism of interpretations
(`def:interpretation-morphism`) from the batched reading to the unbatched
one. Its object-level family and its truth-object morphism are identities,
both readings assigning the same objects, and its monad morphism is
`def:ev-monad-hom`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i as a
-- morphism of interpretations
noncomputable def evMorphism (P : BatchNaturalReading sigA sigB sigG B M) (i : Fin B) :
    InterpretationMorphism (M₂ := CategoryTheory.ofTypeMonad M)
      (typeStrongCat sigA (BmonT B M)) P.kleisliB (typeStrongCat sigA M) P.K where
  domMor := fun S => 𝟙 (P.D.domObj S)
  omegaMor := 𝟙 P.J.Ω
  domMor_comul := fun _ => rfl
  domMor_counit := fun _ => rfl
  monadMor := evMonadHom i
  strength_compat := fun {X Y} => typeStrength_compat_hom i X Y
  strength_natural := fun a b => typeStrength_natural_hom a b
  funMorK_compat := fun f => by
    rw [P.interpretMSMor_ev i (sigG.fcod f), P.interpretMSMor_ev i (sigG.fdom f)]
    exact P.funMorK_batchNatural i f
  relMorK_compat := fun R => by
    have h := P.relMorK_batchNatural i R
    rw [← P.interpretMSMor_ev i (sigG.rari R)] at h
    exact (Category.comp_id _).trans h
  connMor_compat := fun c => by
    have h := P.connMor_batchNatural i c
    rw [← markerMor_ev i P.J.Ω (sigB.connMonad c),
      ← interpretPowMor_ev i P.J.Ω (sigB.connMonad c) (sigB.connArity c)] at h
    exact h
  quanMor_compat := fun Q n => by
    have h := P.quanMor_batchNatural i Q n
    rw [← markerMor_ev i P.J.Ω (sigB.quanMonad Q),
      ← interpretPowMor_ev i P.J.Ω (sigB.quanMonad Q) n] at h
    exact h
  varCard_compat := fun _ => rfl
  varPt_compat := fun _ _ => rfl

namespace BatchNaturalReading

variable (P : BatchNaturalReading sigA sigB sigG B M) [DecidableEq sigG.Var]

/-- Toward `thm:pointwise-eval-kleisli`: `⟦φ⟧^{Bmon 𝓜}`, the batched reading
of a formula, as a function of one input. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- reading, as a function
noncomputable def semBatch (φ : Fm sigG sigB) (h : φ.KTyped) :
    ctxObj P.domB φ.on → BmonT B M P.J.Ω :=
  TypeCat.homEquiv (Fm.sem P.kleisliB φ h)

/-- Toward `thm:pointwise-eval-kleisli`: `⟦φ⟧^{𝓜}`, the unbatched reading of
a formula, as a function. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the unbatched
-- reading, as a function
noncomputable def semPlain (φ : Fm sigG sigB) (h : φ.KTyped) :
    ctxObj (I := typeCatInterpretation sigA M) (J := P.J) P.D φ.on → M P.J.Ω :=
  TypeCat.homEquiv (Fm.sem P.K φ h)

/-- Toward `thm:pointwise-eval-kleisli`: `s_i`, an input of the batch read
into the unbatched reading's own context object. Every context slot is
`Id`-marked, so this map is the identity on values; it exists only because
the two readings compute the same context object through their own
interpretations of the identity marker. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: an input carried
-- to the unbatched reading's context object
noncomputable def ctxAt (i : Fin B) (l : List sigG.Var) :
    ctxObj P.domB l → ctxObj (I := typeCatInterpretation sigA M) (J := P.J) P.D l :=
  TypeCat.homEquiv ((evMorphism P i).ctxMor l)

/-- Toward `thm:pointwise-eval-kleisli`: `⟦φ⟧^{Bmon 𝓜}(s)`, the batched
reading run over a batch `s` of inputs, each index reading its own input. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- reading of a batch of inputs
noncomputable def semBatchOn (φ : Fm sigG sigB) (h : φ.KTyped)
    (s : Fin B → ctxObj P.domB φ.on) : BmonT B M P.J.Ω :=
  fun i => P.semBatch φ h (s i) i

/-- Toward `thm:pointwise-eval-kleisli`: the point-free form of the theorem,
`lem:kleisli-formula-natural` read at `evMorphism`. The target reading's
transport of the identity on the truth object collapses, leaving `ev_i`
alone. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the point-free
-- commutation, Fm.sem_natural at evMorphism
theorem sem_ev_comm (i : Fin B) (φ : Fm sigG sigB) (h : φ.KTyped) :
    Fm.sem P.kleisliB φ h ≫ evAt i P.J.Ω MonSym.mon
      = (evMorphism P i).ctxMor φ.on ≫ Fm.sem P.K φ h := by
  have formula_natural := Fm.sem_natural (evMorphism P i) φ h
  rw [← markerMor_ev i P.J.Ω MonSym.mon]
  exact formula_natural

end BatchNaturalReading

/-- Blueprint `thm:pointwise-eval-kleisli` (Pointwise evaluation commutes
with the Kleisli interpretation), the env's one cited principal
declaration: assume every symbol and quantifier interpretation used in the
batched reading is batch-natural, that is, defined pointwise across the
batch (`BatchNaturalReading`). Then for a batch `s` of inputs and every
formula `φ` of `def:grammatical-signature`'s grammar,
`⟦φ⟧^{Bmon 𝓜}(s)(i) = ⟦φ⟧^{𝓜}(s_i)` at every index `i`.

The proof is `lem:kleisli-formula-natural` at the morphism of
interpretations `ev_i` becomes under batch-naturality (`evMorphism`), read
at the batch's own `i`-th input. -/
theorem pointwise_eval_kleisli [DecidableEq sigG.Var]
    (P : BatchNaturalReading sigA sigB sigG B M) (i : Fin B)
    (φ : Fm sigG sigB) (h : φ.KTyped) (s : Fin B → ctxObj P.domB φ.on) :
    P.semBatchOn φ h s i = P.semPlain φ h (P.ctxAt i φ.on (s i)) := by
  have formula_natural := P.sem_ev_comm i φ h
  exact congrArg (fun t => TypeCat.homEquiv t (s i)) formula_natural

end BatchInstantiation

/-! ### A witness that batch-naturality is satisfiable

`thm:pointwise-eval-kleisli` is an implication, so it is worth nothing if
nothing satisfies its hypothesis. The declarations below exhibit a
signature, a pair of readings satisfying all four batch-naturality laws,
and a formula of the grammar, at every batch size: one domain symbol
interpreted by `Bool`, one relation symbol reading its single pure
argument, one nullary `○`-marked connective returning the batch-constant
`true`, and one variable over a two-point domain. -/

section Witness

open CategoryTheory MonoidalCategory

/-- Witness for `thm:pointwise-eval-kleisli`: the categorical signature. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
def witCat : CatSignature where
  catSymbol := "C"
  actorSymbol := "A"
  monadSymbol := "o"

/-- Witness for `thm:pointwise-eval-kleisli`: the logical signature, one
nullary connective carrying the monad marker and no quantifiers. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
def witLog : LogSignature where
  tauSymbol := "tau"
  Conn := Unit
  connArity := fun _ => 0
  connMonad := fun _ => MonSym.mon
  Quan := Empty
  quanMonad := fun Q => Q.elim

/-- Witness for `thm:pointwise-eval-kleisli`: the domain signature, one
domain symbol, one variable over it, one relation symbol of pure arity
one, and no function symbols. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
def witDom : DomSignature where
  Dom := Unit
  Spc := Empty
  Fun := Empty
  Rel := Unit
  Var := Unit
  Par := Empty
  fdom := fun f => f.elim
  fcod := fun f => f.elim
  fpar := fun f => f.elim
  rari := fun _ => [(MonSym.id, ())]
  rpar := fun _ => []
  varOver := fun _ => ()
  parOver := fun p => p.elim

/-- Witness for `thm:pointwise-eval-kleisli`: decidable equality on the
one variable symbol. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
instance witVarDecEq : DecidableEq witDom.Var := fun _ _ => isTrue rfl

/-- Witness for `thm:pointwise-eval-kleisli`: the unbatched logical
interpretation, truth object `Bool`, the connective returning `true`. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
noncomputable def witLogItp : LogInterpretation (typeCatInterpretation witCat Id) witLog where
  Ω := Bool
  connMor := fun _ => ↾ fun _ : PUnit => (true : Id Bool)
  quanMor := fun Q _ => Q.elim

/-- Witness for `thm:pointwise-eval-kleisli`: the unbatched domain
interpretation, the one domain symbol interpreted by `Bool`. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
noncomputable def witDomItp :
    DomInterpretation (typeCatInterpretation witCat Id) witLogItp witDom where
  domObj := fun _ => Bool
  spcObj := fun s => s.elim
  funMor := fun f => f.elim
  relMor := fun _ => ↾ fun p : PUnit × (Bool × PUnit) => p.2.1

/-- Witness for `thm:pointwise-eval-kleisli`: the unbatched Kleisli
interpretation, the relation reading its argument and the variable
enumerated over the two Booleans. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
noncomputable def witKleisli :
    KleisliInterpretation (typeCatInterpretation witCat Id) (typeStrongCat witCat Id)
      witLogItp witDomItp where
  decEqVar := witVarDecEq
  funMorK := fun f => f.elim
  relMorK := fun _ => ↾ fun p : Bool × PUnit => p.1
  varCard := fun _ => 2
  varPt := fun _ j => ↾ fun _ : PUnit => decide (j.val = 1)

/-- Witness for `thm:pointwise-eval-kleisli`: the batched reading over the
unbatched one, at every batch size. The connective's batched reading is
the batch-constant lift of its unbatched one, the relation's is the
unbatched one itself since its arity is pure, and all four
batch-naturality laws hold by computation. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
noncomputable def witReading (B : ℕ) : BatchNaturalReading witCat witLog witDom B Id where
  J := witLogItp
  D := witDomItp
  K := witKleisli
  connMorB := fun _ => ↾ fun _ : PUnit => (liftM (true : Id Bool) : BmonT B Id Bool)
  quanMorB := fun Q _ => Q.elim
  funMorB := fun f => f.elim
  relMorB := fun _ => ↾ fun p : PUnit × (Bool × PUnit) => p.2.1
  funMorKB := fun f => f.elim
  relMorKB := fun _ => ↾ fun p : Bool × PUnit => p.1
  funMorK_batchNatural := fun _ f => f.elim
  relMorK_batchNatural := fun _ _ => rfl
  connMor_batchNatural := fun _ _ => rfl
  quanMor_batchNatural := fun _ Q _ => Q.elim

/-- Witness for `thm:pointwise-eval-kleisli`: the atomic formula `R(x)`. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
def witFormula : Fm witDom witLog := Fm.rel () [Tm.var ()]

/-- Witness for `thm:pointwise-eval-kleisli`: `R(x)` is well typed. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
theorem witFormula_ktyped : witFormula.KTyped := by
  -- `Fm.KTyped` is a `def` matching on the formula, not a structure, so the
  -- anonymous constructor cannot see the conjunction until the match on
  -- `witFormula`'s own `.rel` head is reduced.
  unfold witFormula Fm.KTyped
  refine ⟨rfl, fun a ha => ?_⟩
  rw [List.mem_singleton.mp ha]
  -- `Tm.KTyped` recurses over a nested inductive, so its variable clause is
  -- propositional rather than definitional: `trivial` and `exact True.intro`
  -- both fail to see that it is `True`. Same idiom as `Tm.inn_var`.
  simp [Tm.KTyped]

/-- Witness for `thm:pointwise-eval-kleisli`: the theorem applies, at every
batch size, to a genuine formula of a genuine signature. Its hypothesis is
therefore satisfiable, not merely unrefuted. -/
@[blueprint_internal] -- non-vacuity witness for thm:pointwise-eval-kleisli
theorem pointwise_eval_kleisli_witness (B : ℕ) (i : Fin B)
    (s : Fin B → ctxObj (witReading B).domB witFormula.on) :
    (witReading B).semBatchOn witFormula witFormula_ktyped s i
      = (witReading B).semPlain witFormula witFormula_ktyped
          ((witReading B).ctxAt i witFormula.on (s i)) :=
  pointwise_eval_kleisli (witReading B) i witFormula witFormula_ktyped s

end Witness

end NeSyCat
