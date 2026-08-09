/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.GrammaticalLayer.Grammar
import NeSyCat.GrammaticalLayer.WireAdapters

/-!
# Kleisli interpretation

Blueprint item `def:kleisli-interpretation` (`blueprint/src/content.tex`,
§"Grammatical layer", `NeSyCat Theory v2`, `new.tex` 1--396): fixing a
categorical interpretation with its strong monad, a domain interpretation,
and a logical interpretation, the Kleisli interpretation `⟦·⟧` assigns to
every term `ξ` a morphism `⟦ξ⟧ : 𝓘(inn ξ) → 𝓜𝓘(out ξ)` and to every
formula `φ` a morphism `⟦φ⟧ : 𝓘([φ]) → 𝓜Ω`, by structural recursion over
`def:grammatical-signature`'s six-rule grammar.
-/

open CategoryTheory MonoidalCategory

universe u u' v v'

namespace NeSyCat

variable {sigA : CatSignature} {I : CatInterpretation sigA}
  {sigB : LogSignature} {J : LogInterpretation I sigB}
  {sigG : DomSignature} {D : DomInterpretation I J sigG}

/-- Companion of `def:kleisli-interpretation`: a term's **value object**,
sidestepping `Tm.out`'s `List Var` shape (`Grammar.lean`'s module doc: the
typing table reads a functional term's codomain off `sigG.fcod f`
directly, never off a second, independently-computed `out`) — `[(Id, ovr
x)]` for a variable term (matching `inn(ξ)=out(ξ)`), `sigG.fcod f` for a
functional term. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: a
-- term's value-object list, feeding both the functional-term and
-- substitution clauses
def Tm.kcod : Tm sigG sigB → List (MonSym × sigG.Dom)
  | .var x => [(.id, sigG.varOver x)]
  | .app f _ => sigG.fcod f

/-- Companion of `def:kleisli-interpretation`: `𝓘(l)` for a list of
variables `l`, the tensor of their (always pure, `Id`-marked) domain
interpretations. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: a
-- variable-list context's interpretation
def ctxObj (D : DomInterpretation I J sigG) (l : List sigG.Var) :
    letI := I.cd.instCat; I.cd.C :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  interpretMS I D.domObj (l.map fun x => (MonSym.id, sigG.varOver x))

/-- Companion of `def:kleisli-interpretation`, resolving the mismatch
between `def:domain-interpretation`'s parameter-threading `funMor`/
`relMor` (through the actegory action `I.act(𝓘(Θ⃗))(-)`) and this
environment's own typing table, which types `𝓘(f)`/`𝓘(R)` directly as
`𝓘(dom f) → 𝓘(cod f)`/`𝓘(dom R) → Ω` — matching `def:wire-adapters`' own
elision of the parameter subscript from a typed symbol's arrow. This
grammar's six rules (`def:grammatical-signature`) supply no syntax for
passing parameter arguments to a functional-term or atomic-formula node,
so every function/relation symbol actually consumed by this grammar is
used at its parameter-free instance — `funMorK`/`relMorK` below are the
document's `𝓘(f)`/`𝓘(R)` at that instance, disclosed extra plumbing (the
STRENGTH TRAP precedent, `WireAdapters.lean`'s `StrongCatInterpretation`,
already established that this environment needs data beyond what any
single earlier environment states). `varCard`/`varPt` supply the
quantifier clause's own "the product state space is again finite,
enumerated lexicographically" datum, per variable domain symbol. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- extra plumbing (parameter-free symbol morphisms, finite variable-domain
-- enumeration) this environment's own typing table needs beyond
-- def:domain-interpretation's stated data — not itself blueprint-cited
structure KleisliInterpretation {sigA : CatSignature} (I : CatInterpretation sigA)
    (SI : StrongCatInterpretation I) {sigB : LogSignature} (J : LogInterpretation I sigB)
    {sigG : DomSignature} (D : DomInterpretation I J sigG) where
  /-- Decidable equality on variable symbols, needed for context filtering
  (`Fm.on`, this file's insertion machinery). -/
  decEqVar : DecidableEq sigG.Var
  /-- `𝓘(f) : 𝓘(dom f) → 𝓘(cod f)`, the function symbol's morphism at its
  parameter-free instance. -/
  funMorK : ∀ f : sigG.Fun, letI := I.cd.instCat; letI := I.cd.instMonoidal;
      interpretMS I D.domObj (sigG.fdom f) ⟶ interpretMS I D.domObj (sigG.fcod f)
  /-- `𝓘(R) : 𝓘(dom R) → Ω`, the relation symbol's morphism at its
  parameter-free instance. -/
  relMorK : ∀ R : sigG.Rel, letI := I.cd.instCat; letI := I.cd.instMonoidal;
      interpretMS I D.domObj (sigG.rari R) ⟶ J.Ω
  /-- `|𝓘([x])|`, the finite cardinality of a variable domain symbol's
  interpretation. -/
  varCard : sigG.Var → ℕ
  /-- `𝓘([x])_i : I → 𝓘([x])`, the lexicographic enumeration of a
  variable domain symbol's (finite) interpretation. -/
  varPt : ∀ x : sigG.Var, letI := I.cd.instCat; letI := I.cd.instMonoidal;
      Fin (varCard x) → (𝟙_ I.cd.C ⟶ D.domObj (sigG.varOver x))

variable {SI : StrongCatInterpretation I}

/-- Companion of `def:kleisli-interpretation`'s insertion machinery: a
context `L`, split by a predicate `p`, merges its "off" part and its
"on" part back into `𝓘(L)` — by structural recursion on `L`, sliding
each variable past the recursively-built rest via the CD category's
symmetry. The building block for both the substituted-formula's single-
position insertion and the quantified-formula's product-state insertion
(`p := (· ∈ xs)`), matching `Fm.on`'s own filter-based context
bookkeeping (`Grammar.lean`). -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- insertion machinery's context-merge primitive, structural on L
def ctxMerge (D : DomInterpretation I J sigG) (p : sigG.Var → Bool) :
    (l : List sigG.Var) → letI := I.cd.instCat; letI := I.cd.instMonoidal;
      ctxObj D (l.filter (fun x => !p x)) ⊗ ctxObj D (l.filter p) ⟶ ctxObj D l
  | [] => letI := I.cd.instCat; letI := I.cd.instMonoidal; (λ_ (𝟙_ I.cd.C)).hom
  | y :: l' =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal; letI := I.cd.instSymmetric
    match hpy : p y with
    | true =>
      have e1 : (y :: l').filter (fun x => !p x) = l'.filter (fun x => !p x) :=
        List.filter_cons_of_neg (by simp [hpy])
      have e2 : (y :: l').filter p = y :: l'.filter p := List.filter_cons_of_pos hpy
      e1 ▸ e2 ▸
        ((α_ (ctxObj D (l'.filter (fun x => !p x))) (D.domObj (sigG.varOver y))
              (ctxObj D (l'.filter p))).inv ≫
          ((β_ (ctxObj D (l'.filter (fun x => !p x))) (D.domObj (sigG.varOver y))).hom ⊗ₘ
              𝟙 (ctxObj D (l'.filter p))) ≫
          (α_ (D.domObj (sigG.varOver y)) (ctxObj D (l'.filter (fun x => !p x)))
              (ctxObj D (l'.filter p))).hom ≫
          (𝟙 (D.domObj (sigG.varOver y)) ⊗ₘ ctxMerge D p l'))
    | false =>
      have e1 : (y :: l').filter (fun x => !p x) = y :: l'.filter (fun x => !p x) :=
        List.filter_cons_of_pos (by simp [hpy])
      have e2 : (y :: l').filter p = l'.filter p := List.filter_cons_of_neg (by simp [hpy])
      e1 ▸ e2 ▸
        ((α_ (D.domObj (sigG.varOver y)) (ctxObj D (l'.filter (fun x => !p x)))
              (ctxObj D (l'.filter p))).hom ≫
          (𝟙 (D.domObj (sigG.varOver y)) ⊗ₘ ctxMerge D p l'))

/-- Companion of `def:kleisli-interpretation`'s quantifier clause: `|𝓘([x⃗])|
= ∏_j |𝓘([x_{p_j}])|`, the product-state cardinality of a variable list,
folded from `KleisliInterpretation.varCard`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- product state space's cardinality
def listCard (K : KleisliInterpretation I SI J D) : List sigG.Var → ℕ
  | [] => 1
  | x :: xs => K.varCard x * listCard K xs

/-- Companion of `def:kleisli-interpretation`'s quantifier clause:
`𝓘([x⃗])_i : I → 𝓘([x⃗])`, the lexicographic enumeration of the product
state space, folded from `KleisliInterpretation.varPt` via
`finProdFinEquiv`'s decomposition of `i` into lexicographic components. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- product state space's lexicographic enumeration
def listPt (K : KleisliInterpretation I SI J D) :
    (l : List sigG.Var) → letI := I.cd.instCat; letI := I.cd.instMonoidal;
      Fin (listCard K l) → (𝟙_ I.cd.C ⟶ ctxObj D l)
  | [], _ => letI := I.cd.instCat; letI := I.cd.instMonoidal; 𝟙 (𝟙_ I.cd.C)
  | x :: xs, i =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (λ_ (𝟙_ I.cd.C)).inv ≫
      (K.varPt x (finProdFinEquiv.symm i).1 ⊗ₘ listPt K xs (finProdFinEquiv.symm i).2)

/-- Companion of `def:kleisli-interpretation`: `𝓘(l₁+l₂) ≅ 𝓘(l₁) ⊠ 𝓘(l₂)`
for a concatenated variable context, by structural recursion on `l₁`
threading the associator — the reassociation `⟦ξ⃗⟧`/`⟦φ⃗⟧` need to match
`Tm.inn`/`Fm.on`'s own concatenation-based (not deduplicated) contexts
(`Grammar.lean`). -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- context-concatenation associator
def ctxAppendIso (D : DomInterpretation I J sigG) :
    (l1 l2 : List sigG.Var) → letI := I.cd.instCat; letI := I.cd.instMonoidal;
      ctxObj D (l1 ++ l2) ≅ ctxObj D l1 ⊗ ctxObj D l2
  | [], l2 => letI := I.cd.instCat; letI := I.cd.instMonoidal; (λ_ (ctxObj D l2)).symm
  | x :: l1', l2 =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (whiskerLeftIso (D.domObj (sigG.varOver x)) (ctxAppendIso D l1' l2)) ≪≫
      (α_ (D.domObj (sigG.varOver x)) (ctxObj D l1') (ctxObj D l2)).symm

/-- Companion of `def:kleisli-interpretation`: `𝓘(l₁+l₂) ≅ 𝓘(l₁) ⊠ 𝓘(l₂)`
for a concatenated marked-symbol list (a function/relation symbol's
domain/codomain, or a term's value list `Tm.kcod`), the `interpretMS`
analogue of `ctxAppendIso`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- marked-symbol-list concatenation associator
def kcodAppendIso (D : DomInterpretation I J sigG) :
    (l1 l2 : List (MonSym × sigG.Dom)) → letI := I.cd.instCat; letI := I.cd.instMonoidal;
      interpretMS I D.domObj (l1 ++ l2) ≅ interpretMS I D.domObj l1 ⊗ interpretMS I D.domObj l2
  | [], l2 => letI := I.cd.instCat; letI := I.cd.instMonoidal;
      (λ_ (interpretMS I D.domObj l2)).symm
  | p :: l1', l2 =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (whiskerLeftIso ((I.interpretMon p.1).obj (D.domObj p.2)) (kcodAppendIso D l1' l2)) ≪≫
      (α_ ((I.interpretMon p.1).obj (D.domObj p.2)) (interpretMS I D.domObj l1')
          (interpretMS I D.domObj l2)).symm

/-- Companion of `def:kleisli-interpretation`'s quantifier clause: the
`n`-ary self-copy `X ⟶ X^{⊗n}` of an object `X`, built from the CD
category's chosen comonoid (`CDCategory.comon`, discard at `n = 0`,
comultiplication then recurse at `n + 1`) — duplicates a single context
into the `n` parallel copies the product-state enumeration `⊠_i` needs. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- quantifier clause's n-ary context duplication
def comulN (X : letI := I.cd.instCat; I.cd.C) :
    (n : ℕ) → letI := I.cd.instCat; letI := I.cd.instMonoidal;
      X ⟶ tensorList (List.replicate n X)
  | 0 => letI := I.cd.instCat; letI := I.cd.instMonoidal; letI := I.cd.comon X;
      ComonObj.counit
  | n + 1 =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal; letI := I.cd.comon X
    ComonObj.comul ≫ (𝟙 X ⊗ₘ comulN X n)

/-- Companion of `def:kleisli-interpretation`'s quantifier clause: given
`n` morphisms out of the same object `X`, tensors them together —
`⊠_i f_i : X^{⊗n} → Ω_1^{⊗?} ⊠ ⋯`, the per-index piece of the product-
state semantics `⊠_i ⟦φ⟧_{[⋯]}`, structural on `n`. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- quantifier clause's indexed tensor of per-state semantics
def tensorFin (X Y : letI := I.cd.instCat; I.cd.C) :
    (n : ℕ) → (Fin n → letI := I.cd.instCat; X ⟶ Y) →
    letI := I.cd.instCat; letI := I.cd.instMonoidal;
      tensorList (List.replicate n X) ⟶ tensorList (List.replicate n Y)
  | 0, _ => letI := I.cd.instCat; letI := I.cd.instMonoidal; 𝟙 (𝟙_ I.cd.C)
  | n + 1, f =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    f 0 ⊗ₘ tensorFin X Y n (fun i => f i.succ)

/-- Companion of `def:kleisli-interpretation`, an extrinsic typing side
condition beyond `Tm.WellFormed`/`Fm.WellFormed` (`Grammar.lean`): the
grammar's own well-formedness only checks arity length, never that an
argument's value type (`Tm.kcod`) actually matches the symbol's declared
slot. `Tm.KTyped`/`Fm.KTyped` below state exactly the extra match this
environment's typing table needs — the pin's "extrinsic WF hypotheses
enter as Prop side-conditions on the interpretation's clauses" doctrine,
applied to a condition `def:grammatical-signature` itself does not state. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- extrinsic value-type-matching side condition, beyond Tm.WellFormed
def Tm.KTyped : Tm sigG sigB → Prop
  | .var _ => True
  | .app f args => (args.map Tm.kcod).flatten = sigG.fdom f ∧ ∀ a ∈ args, a.KTyped

mutual

/-- Companion of `def:kleisli-interpretation`: `⟦ξ⃗⟧`, the tensor of a
term list's own semantics (matching `Tm.inn`'s flatten convention — no
`copy` needed, since a flattened, not-deduplicated context already gives
each occurrence its own tensor slot, `Grammar.lean`'s module doc),
collapsing the per-term `𝓜`-wraps into one via `StrongCatInterpretation.dst`
at each step, structural on the list. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- term-list semantics `⟦ξ⃗⟧`
def TmList.sem (K : KleisliInterpretation I SI J D) :
    (ts : List (Tm sigG sigB)) → (∀ a ∈ ts, a.KTyped) →
    letI := I.cd.instCat; letI := I.cd.instMonoidal;
      ctxObj D (ts.map Tm.inn).flatten ⟶
      I.monad.obj (interpretMS I D.domObj (ts.map Tm.kcod).flatten)
  | [], _ => letI := I.cd.instCat; letI := I.cd.instMonoidal; I.monad.η.app (𝟙_ I.cd.C)
  | t :: ts, hts =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (ctxAppendIso D t.inn (ts.map Tm.inn).flatten).hom ≫
      (Tm.sem K t (hts t List.mem_cons_self) ⊗ₘ
          TmList.sem K ts (fun a ha => hts a (List.mem_cons_of_mem t ha))) ≫
      SI.dst ≫
      I.monad.map (kcodAppendIso D t.kcod (ts.map Tm.kcod).flatten).inv

/-- Companion of `def:kleisli-interpretation`, the term-semantics half:
`⟦ξ⟧ : 𝓘(inn ξ) → 𝓜𝓘(kcod ξ)` by structural recursion on `Tm` — `η` at a
variable term (`⟦x⟧ := η_{𝓘(x)}`); the tensored argument semantics `⟦ξ⃗⟧`
(`TmList.sem`) composed with `𝓘(f)`'s parameter-free morphism
(`KleisliInterpretation.funMorK`) for a functional term
(`⟦f(ξ⃗)⟧ := ⟦ξ⃗⟧ ⨟_∘ 𝓘(f)`), consuming `Tm.KTyped`'s value-match witness
to align `⟦ξ⃗⟧`'s tensored codomain with `sigG.fdom f`. The env's one
cited principal is `Fm.sem` below (the bijection law: one name per env);
`Tm.sem` is its mutually-needed term-side half. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- term-semantics half (⟦ξ⟧), Fm.sem is the cited principal (⟦φ⟧)
def Tm.sem (K : KleisliInterpretation I SI J D) :
    ∀ ξ : Tm sigG sigB, ξ.KTyped → letI := I.cd.instCat; letI := I.cd.instMonoidal;
      ctxObj D ξ.inn ⟶ I.monad.obj (interpretMS I D.domObj ξ.kcod)
  | .var x, _ => by
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    simp only [Tm.inn, Tm.kcod]
    exact I.monad.η.app _
  | .app f args, ht => by
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    simp only [Tm.inn, Tm.kcod]
    simp only [Tm.KTyped] at ht
    exact (ht.1 ▸ TmList.sem K args ht.2) ≫ I.monad.map (K.funMorK f)

end

/-- Companion of `def:kleisli-interpretation`, the formula-side companion
of `Tm.KTyped` (module doc above): beyond `Fm.WellFormed`'s arity checks,
an atomic formula's arguments must value-match `sigG.rari R`
(`Tm.kcod`-based, as `Tm.KTyped`'s function-symbol case); a compound
formula's connective is taken at its `○`-marked instance (disclosed
below); a quantified formula's quantifier likewise; a substituted
formula's term must value-match the substituted variable's own domain
(the natural well-typedness condition for substitution). **Disclosed
simplification**: the `connMonad c = ○`/`quanMonad Q = ○` conjuncts
restrict this environment's compound/quantified clauses to the `○`-marked
instance of a connective/quantifier symbol — the case every one of this
theory's four running quantifier families (Max, Min, the Σ-Π pair, their
log twins) and its running connectives actually are (effectful,
`○`-marked). `def:logical-signature` itself allows `Id`-marked
connectives/quantifiers too; encoding that case needs an extra per-marker
normalization this ticket does not build (`Kleisli.lean`'s module doc
records the exact deviation). The substituted-formula case's own filter
conjunct further restricts to a variable occurring **exactly once** in
`body.on` — the document's "single-position insertion" reading; the
general "copy the computation's value into every occurrence of `x`"
reading it also describes (the dice-or-die example) needs an `n`-ary
copy this ticket does not build, also disclosed in the module doc. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- formula-side extrinsic typing side condition
def Fm.KTyped [DecidableEq sigG.Var] : Fm sigG sigB → Prop
  | .rel R args => (args.map Tm.kcod).flatten = sigG.rari R ∧ ∀ a ∈ args, a.KTyped
  | .conn c args =>
    sigB.connArity c = args.length ∧ sigB.connMonad c = MonSym.mon ∧ ∀ a ∈ args, a.KTyped
  | .quant Q _ body => sigB.quanMonad Q = MonSym.mon ∧ body.KTyped
  | .subst body x t =>
    Tm.kcod t = [(MonSym.id, sigG.varOver x)] ∧
      body.on.filter (fun v => decide (v = x)) = [x] ∧ body.KTyped ∧ t.KTyped

mutual

/-- Companion of `def:kleisli-interpretation`: `⟦φ⃗⟧`, the tensor of a
formula list's own semantics — matching `Fm.on`'s flatten convention (no
`copy` needed, same reasoning as `TmList.sem`), left uncollapsed (a plain
tensor of `𝓜Ω`-valued factors, not bound into one `𝓜(Ω^{⊗n})`) since the
connective clause consumes it directly against `connMor`'s own
`(𝓘(M)Ω)^{⊠n}`-shaped domain. -/
@[blueprint_internal] -- companion of def:kleisli-interpretation: the
-- formula-list semantics `⟦φ⃗⟧`
def FmList.sem [DecidableEq sigG.Var] (K : KleisliInterpretation I SI J D) :
    (fs : List (Fm sigG sigB)) → (∀ a ∈ fs, a.KTyped) →
    letI := I.cd.instCat; letI := I.cd.instMonoidal;
      ctxObj D (fs.map Fm.on).flatten ⟶ tensorList (fs.map (fun _ => I.monad.obj J.Ω))
  | [], _ => letI := I.cd.instCat; letI := I.cd.instMonoidal; 𝟙 (𝟙_ I.cd.C)
  | t :: ts, hts =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (ctxAppendIso D t.on (ts.map Fm.on).flatten).hom ≫
      (Fm.sem K t (hts t List.mem_cons_self) ⊗ₘ
          FmList.sem K ts (fun a ha => hts a (List.mem_cons_of_mem t ha)))

/-- Blueprint `def:kleisli-interpretation` (Kleisli interpretation), the
env's one cited principal declaration (the bijection law): the Kleisli
interpretation `⟦·⟧ : 𝓘([φ]) → 𝓜Ω` of the grammatical signature's
formulas, by structural recursion on `Fm` (mutually with `Tm.sem`'s
`⟦·⟧ : 𝓘(inn ξ) → 𝓜𝓘(kcod ξ)` on terms) over all six of
`def:grammatical-signature`'s rules — variable and functional terms in
`Tm.sem`; here, an atomic formula (`⟦R(ξ⃗)⟧ := ⟦ξ⃗⟧ ⨟_∘ 𝓘(R)`, the tensored
argument semantics `TmList.sem` composed with `𝓘(R)`, `Tm.KTyped`'s
value-match witness aligning `⟦ξ⃗⟧` with `sigG.rari R`); a compound
formula (`⟦*(φ⃗)⟧ := ⟦φ⃗⟧ ⨟ 𝓘(*)`, `FmList.sem` composed with `𝓘(*)`, at
the `○`-marked instance `Fm.KTyped` witnesses); a quantified formula
(`⟦Qx⃗(φ)⟧ = ⊠_i ⟦φ⟧_{[⋯]} ⨟ 𝓘(Q)_N`, the product-state enumeration
`listCard`/`listPt` over the positions of `x⃗` in `body.on`, `N`-ary
self-copy `comulN` of the remaining context, per-state insertion via
`ctxMerge`, `tensorFin`'s indexed tensor of the resulting semantics
feeding `𝓘(Q)_N`); a substituted formula (`⟦φ[x:=ξ]⟧ = ⟦ξ⟧^{(p)} ⨟_∘
⟦φ⟧`, the term's semantics tensored into `x`'s single-position slot via
`ctxAppendIso`/`SI.strength`, joined into `body`'s own semantics via
`ctxMerge` and `SI.bind`). -/
def Fm.sem [DecidableEq sigG.Var] (K : KleisliInterpretation I SI J D) :
    ∀ φ : Fm sigG sigB, φ.KTyped → letI := I.cd.instCat; letI := I.cd.instMonoidal;
      ctxObj D φ.on ⟶ I.monad.obj J.Ω
  | .rel R args, ht => by
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    simp only [Fm.on]
    simp only [Fm.KTyped] at ht
    exact (ht.1 ▸ TmList.sem K args ht.2) ≫ I.monad.map (K.relMorK R)
  | .conn c args, ht => by
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    simp only [Fm.on]
    simp only [Fm.KTyped] at ht
    obtain ⟨harity, hmon, hargs⟩ := ht
    have hsrc := FmList.sem K args hargs
    rw [List.map_const'] at hsrc
    have hcm := J.connMor c
    rw [hmon, harity] at hcm
    exact hsrc ≫ hcm
  | .quant Q xs body, ht => by
    letI := I.cd.instCat; letI := I.cd.instMonoidal; letI := I.cd.instSymmetric
    simp only [Fm.on, decide_not]
    simp only [Fm.KTyped] at ht
    obtain ⟨hQmon, hbody⟩ := ht
    have hquant :
        tensorList (List.replicate (listCard K (body.on.filter (fun v => decide (v ∈ xs))))
            (I.monad.obj J.Ω)) ⟶ I.monad.obj J.Ω := by
      have hqm := J.quanMor Q (listCard K (body.on.filter (fun v => decide (v ∈ xs))))
      rw [hQmon] at hqm
      exact hqm
    exact comulN (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs))))
        (listCard K (body.on.filter (fun v => decide (v ∈ xs)))) ≫
      tensorFin (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs)))) (I.monad.obj J.Ω)
        (listCard K (body.on.filter (fun v => decide (v ∈ xs))))
        (fun i =>
          ((ρ_ (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs))))).inv ≫
              (𝟙 (ctxObj D (body.on.filter (fun v => !decide (v ∈ xs)))) ⊗ₘ
                listPt K (body.on.filter (fun v => decide (v ∈ xs))) i) ≫
              ctxMerge D (fun v => decide (v ∈ xs)) body.on) ≫
            Fm.sem K body hbody) ≫
      hquant
  | .subst body x t, ht => by
    letI := I.cd.instCat; letI := I.cd.instMonoidal; letI := I.cd.instSymmetric
    simp only [Fm.on, ne_eq, decide_not]
    simp only [Fm.KTyped] at ht
    obtain ⟨hkcod, hocc, hbody, ht⟩ := ht
    have hT : ctxObj D t.inn ⟶ I.monad.obj (interpretMS I D.domObj [(MonSym.id, sigG.varOver x)]) :=
      hkcod ▸ Tm.sem K t ht
    have hins :
        ctxObj D (body.on.filter (fun v => !decide (v = x))) ⊗ ctxObj D [x] ⟶ ctxObj D body.on :=
      hocc ▸ ctxMerge D (fun v => decide (v = x)) body.on
    exact (ctxAppendIso D (body.on.filter (fun v => !decide (v = x))) t.inn).hom ≫
      (𝟙 (ctxObj D (body.on.filter (fun v => !decide (v = x)))) ⊗ₘ hT) ≫
      SI.strength ≫
      I.monad.map hins ≫
      SI.bind (Fm.sem K body hbody)

end

-- (completeness census, same pattern as `Tm.WellFormed.eq_def`/
-- `Fm.WellFormed.eq_def` in `NeSyCat/GrammaticalLayer/Grammar.lean`:
-- equation-lemma/congr byproducts of `Tm.KTyped`/`Fm.KTyped`'s pattern
-- match, with no attribute site of their own, tagged post-hoc -- not
-- blueprint-cited, plumbing of the extrinsic typing side conditions)
attribute [blueprint_internal] Tm.KTyped.eq_def Fm.KTyped.eq_def Fm.KTyped.congr_simp

end NeSyCat
