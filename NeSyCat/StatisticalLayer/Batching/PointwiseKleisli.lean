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

/-- Toward `thm:pointwise-eval-kleisli`: the batched reading of a domain
interpretation's objects, `S ↦ (Bidx → 𝓘(S))`. The batched reading
consumes a batch of inputs, so its object family is batched too. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- object family on domain symbols
def batchObj {sigG : DomSignature} (B : ℕ) (dom : sigG.Dom → Type) :
    sigG.Dom → Type := fun S => Fin B → dom S

/-- Toward `thm:pointwise-eval-kleisli`: the batch-constant embedding
`X → (Bidx → X)`, the same value at every index. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the
-- batch-constant embedding
def constBatch (B : ℕ) (X : Type) : X ⟶ (Fin B → X) := ↾ fun v _ => v

/-- Toward `thm:pointwise-eval-kleisli`: `ev_i` on a domain symbol's
batched object, the projection `(Bidx → 𝓘(S)) → 𝓘(S)` at slot `i`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the object-level
-- half of ev_i
def evDom {sigG : DomSignature} {dom : sigG.Dom → Type} (i : Fin B) (S : sigG.Dom) :
    batchObj B dom S ⟶ dom S :=
  ↾ fun g : Fin B → dom S => g i

/-- Toward `thm:pointwise-eval-kleisli`: `ev_i` at one marked slot. An
`Id`-marked slot carries a batch, read at index `i`. A `○`-marked slot
carries a batched computation of a batched value: the computation is run
at index `i`, and its value read at index `i` too. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i at one
-- marked slot
noncomputable def evMarker {sigG : DomSignature} (i : Fin B) (dom : sigG.Dom → Type) :
    (m : MonSym) → (S : sigG.Dom) →
      ((batchCat sigA B M).interpretMon m).obj (batchObj B dom S) ⟶
        ((typeCatInterpretation sigA M).interpretMon m).obj (dom S)
  | .id, S => evDom i S
  | .mon, S => ↾ fun c : BmonT B M (Fin B → dom S) =>
      (((fun g => g i) <$> ev i c : M (dom S)))

/-- Toward `thm:pointwise-eval-kleisli`: `ev_i` on a marked-symbol list's
tensor, slot by slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i on a
-- marked-symbol list's tensor
noncomputable def evMS {sigG : DomSignature} (i : Fin B) (dom : sigG.Dom → Type) :
    (l : List (MonSym × sigG.Dom)) →
      interpretMS (batchCat sigA B M) (batchObj B dom) l ⟶
        interpretMS (typeCatInterpretation sigA M) dom l
  | [] => 𝟙 (𝟙_ (batchCat sigA B M).cd.C)
  | p :: l => evMarker i dom p.1 p.2 ⊗ₘ evMS i dom l

/-- Toward `thm:pointwise-eval-kleisli`: `ev_i` at one marked slot of the
truth object. Both readings share one truth object, so an `Id`-marked slot
is carried by the identity and a `○`-marked one by `ev_i`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i at one
-- marked slot of the shared truth object
noncomputable def evOmega (i : Fin B) (Om : Type) :
    (m : MonSym) → ((batchCat sigA B M).interpretMon m).obj Om ⟶
      ((typeCatInterpretation sigA M).interpretMon m).obj Om
  | .id => 𝟙 Om
  | .mon => ↾ fun c : BmonT B M Om => ev i c

/-- Toward `thm:pointwise-eval-kleisli`: `ev_i` on a tensor power of the
truth object, slot by slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i on a
-- tensor power of the shared truth object
noncomputable def evPow (i : Fin B) (Om : Type) (m : MonSym) :
    (n : ℕ) → interpretPow (batchCat sigA B M) Om m n ⟶
      interpretPow (typeCatInterpretation sigA M) Om m n
  | 0 => 𝟙 (𝟙_ (batchCat sigA B M).cd.C)
  | n + 1 => evOmega i Om m ⊗ₘ evPow i Om m n

/-- Toward `thm:pointwise-eval-kleisli`: the per-slot transport of
`def:interpretation-morphism` at the shared truth object is `ev_i` there. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: markerMor at the
-- shared truth object
theorem markerMor_omega (i : Fin B) (Om : Type) (m : MonSym) :
    markerMor (I := batchCat sigA B M) (M₂ := CategoryTheory.ofTypeMonad M)
        (evMonadHom i).toNatTrans m (𝟙 Om) = evOmega i Om m := by
  cases m with
  | id => rfl
  | mon =>
    rw [markerMor_mon,
      CategoryTheory.Functor.map_id (self := (CategoryTheory.ofTypeMonad M).toFunctor) (X := Om)]
    exact Category.comp_id _

/-- Toward `thm:pointwise-eval-kleisli`: the induced morphism on a tensor
power of the shared truth object is `ev_i` slot by slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: interpretPowMor
-- at ev_i's data
theorem interpretPowMor_omega (i : Fin B) (Om : Type) (m : MonSym) :
    ∀ n : ℕ,
      interpretPowMor (I := batchCat sigA B M) (M₂ := CategoryTheory.ofTypeMonad M)
          (evMonadHom i).toNatTrans (𝟙 Om) m n = evPow i Om m n
  | 0 => rfl
  | n + 1 => by
    change markerMor _ m (𝟙 Om) ⊗ₘ
        interpretPowMor (I := batchCat sigA B M) (M₂ := CategoryTheory.ofTypeMonad M)
          (evMonadHom i).toNatTrans (𝟙 Om) m n
      = evOmega i Om m ⊗ₘ evPow i Om m n
    rw [markerMor_omega i Om m, interpretPowMor_omega i Om m n]
    rfl

/-- Toward `thm:pointwise-eval-kleisli`: an unbatched reading of a grammar
together with a batched one that is BATCH-NATURAL over it. The unbatched
reading is a Kleisli interpretation (`def:kleisli-interpretation`) at
`def:type-cat-interpretation`'s realization of `𝓜`. The batched reading is
the same interpretation with `Bmon 𝓜` in place of `𝓜`, the batched object
family `S ↦ (Bidx → 𝓘(S))` in place of `𝓘(S)`, one shared truth object, and
its own symbol data; batch-naturality is the four laws below, each saying
that the batched interpretation of a symbol, read at index `i`, is the
unbatched one read at index `i` first.

The variable enumeration is not batched: a quantifier ranges over a domain
fixed by the signature, so the two readings enumerate the same points and
the batched enumeration is the batch-constant embedding of the unbatched
one (`kleisliB` below). Parameter spaces are not batched either. -/
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
        (interpretMS (batchCat sigA B M) (batchObj B D.domObj) (sigG.fdom f)) ⟶
      interpretMS (batchCat sigA B M) (batchObj B D.domObj) (sigG.fcod f)
  /-- The batched parameter-threaded morphism of each relation symbol,
  unconstrained for the same reason. -/
  relMorB : ∀ R : sigG.Rel,
    (batchCat sigA B M).act (interpretSpc (batchCat sigA B M) D.spcObj (sigG.rpar R))
        (interpretMS (batchCat sigA B M) (batchObj B D.domObj) (sigG.rari R)) ⟶ J.Ω
  /-- The batched interpretation of each function symbol at its
  parameter-free instance. -/
  funMorKB : ∀ f : sigG.Fun,
    interpretMS (batchCat sigA B M) (batchObj B D.domObj) (sigG.fdom f) ⟶
      interpretMS (batchCat sigA B M) (batchObj B D.domObj) (sigG.fcod f)
  /-- The batched interpretation of each relation symbol at its
  parameter-free instance. -/
  relMorKB : ∀ R : sigG.Rel,
    interpretMS (batchCat sigA B M) (batchObj B D.domObj) (sigG.rari R) ⟶ J.Ω
  /-- Batch-naturality at every function symbol: applying the batched
  interpretation and then reading index `i` is reading index `i` and then
  applying the unbatched interpretation. -/
  funMorK_batchNatural : ∀ (i : Fin B) (f : sigG.Fun),
    funMorKB f ≫ evMS i D.domObj (sigG.fcod f)
      = evMS i D.domObj (sigG.fdom f) ≫ K.funMorK f
  /-- Batch-naturality at every relation symbol. The truth object is shared,
  so no reading of the value side is needed on the left. -/
  relMorK_batchNatural : ∀ (i : Fin B) (R : sigG.Rel),
    relMorKB R = evMS i D.domObj (sigG.rari R) ≫ K.relMorK R
  /-- Batch-naturality at every connective symbol. -/
  connMor_batchNatural : ∀ (i : Fin B) (c : sigB.Conn),
    connMorB c ≫ evOmega i J.Ω (sigB.connMonad c)
      = evPow i J.Ω (sigB.connMonad c) (sigB.connArity c) ≫ J.connMor c
  /-- Batch-naturality at every quantifier symbol, at every arity. -/
  quanMor_batchNatural : ∀ (i : Fin B) (Q : sigB.Quan) (n : ℕ),
    quanMorB Q n ≫ evOmega i J.Ω (sigB.quanMonad Q)
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
Its object family is batched, `S ↦ (Bidx → 𝓘(S))`; parameter spaces are
not. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- domain interpretation
noncomputable def domB : DomInterpretation (batchCat sigA B M) P.logB sigG where
  domObj := batchObj B P.D.domObj
  spcObj := P.D.spcObj
  funMor := P.funMorB
  relMor := P.relMorB

/-- Toward `thm:pointwise-eval-kleisli`: the batched Kleisli
interpretation. Its variable enumeration is the batch-constant embedding
of the unbatched one: a quantifier ranges over a domain fixed by the
signature, the same domain at every index. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: the batched
-- Kleisli interpretation
noncomputable def kleisliB :
    KleisliInterpretation (batchCat sigA B M) (typeStrongCat sigA (BmonT B M))
      P.logB P.domB where
  decEqVar := P.K.decEqVar
  funMorK := P.funMorKB
  relMorK := P.relMorKB
  varCard := P.K.varCard
  varPt := fun x j => P.K.varPt x j ≫ constBatch B (P.D.domObj (sigG.varOver x))

/-- Toward `thm:pointwise-eval-kleisli`: the per-slot transport of
`def:interpretation-morphism` at `ev_i`'s data is `ev_i` at that slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: markerMor at
-- ev_i's data
theorem markerMor_evDom (i : Fin B) (m : MonSym) (S : sigG.Dom) :
    markerMor (I := batchCat sigA B M) (M₂ := CategoryTheory.ofTypeMonad M)
        (evMonadHom i).toNatTrans m (evDom (dom := P.D.domObj) i S)
      = evMarker i P.D.domObj m S := by
  cases m with
  | id => rfl
  | mon => rfl

/-- Toward `thm:pointwise-eval-kleisli`: the induced morphism on a
marked-symbol list's tensor is `ev_i` slot by slot. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: interpretMSMor
-- at ev_i's data
theorem interpretMSMor_evDom (i : Fin B) :
    ∀ l : List (MonSym × sigG.Dom),
      interpretMSMor P.domB P.D (evMonadHom i).toNatTrans (fun S => evDom i S) l
        = evMS i P.D.domObj l
  | [] => rfl
  | p :: l => by
    change markerMor _ p.1 (evDom i p.2) ⊗ₘ
        interpretMSMor P.domB P.D (evMonadHom i).toNatTrans (fun S => evDom i S) l
      = evMarker i P.D.domObj p.1 p.2 ⊗ₘ evMS i P.D.domObj l
    rw [markerMor_evDom P i p.1 p.2, interpretMSMor_evDom i l]
    rfl

end BatchNaturalReading

/-- Toward `thm:pointwise-eval-kleisli`: reading a batch-constant family at
any index returns the value it was built from. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i undoes the
-- batch-constant embedding
theorem constBatch_evDom {sigG : DomSignature} (i : Fin B) (dom : sigG.Dom → Type)
    (S : sigG.Dom) : constBatch B (dom S) ≫ evDom (dom := dom) i S = 𝟙 (dom S) := rfl

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
one. Its object-level family is the projection at slot `i`, its truth-object
morphism is the identity, and its monad morphism is `def:ev-monad-hom`. -/
@[blueprint_internal] -- toward thm:pointwise-eval-kleisli: ev_i as a
-- morphism of interpretations
noncomputable def evMorphism (P : BatchNaturalReading sigA sigB sigG B M) (i : Fin B) :
    InterpretationMorphism (M₂ := CategoryTheory.ofTypeMonad M)
      (typeStrongCat sigA (BmonT B M)) P.kleisliB (typeStrongCat sigA M) P.K where
  domMor := fun S => evDom i S
  omegaMor := 𝟙 P.J.Ω
  domMor_comul := fun _ => rfl
  domMor_counit := fun _ => rfl
  monadMor := evMonadHom i
  strength_compat := fun {X Y} => typeStrength_compat_hom i X Y
  strength_natural := fun a b => typeStrength_natural_hom a b
  funMorK_compat := fun f => by
    rw [P.interpretMSMor_evDom i (sigG.fcod f), P.interpretMSMor_evDom i (sigG.fdom f)]
    exact P.funMorK_batchNatural i f
  relMorK_compat := fun R => by
    have h := P.relMorK_batchNatural i R
    rw [← P.interpretMSMor_evDom i (sigG.rari R)] at h
    exact (Category.comp_id _).trans h
  connMor_compat := fun c => by
    have h := P.connMor_batchNatural i c
    rw [← markerMor_omega i P.J.Ω (sigB.connMonad c),
      ← interpretPowMor_omega i P.J.Ω (sigB.connMonad c) (sigB.connArity c)] at h
    exact h
  quanMor_compat := fun Q n => by
    have h := P.quanMor_batchNatural i Q n
    rw [← markerMor_omega i P.J.Ω (sigB.quanMonad Q),
      ← interpretPowMor_omega i P.J.Ω (sigB.quanMonad Q) n] at h
    exact h
  varCard_compat := fun _ => rfl
  varPt_compat := fun _ _ => rfl

end BatchInstantiation

end NeSyCat
