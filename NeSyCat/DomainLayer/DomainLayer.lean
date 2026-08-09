/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.Signatures.Signatures
import NeSyCat.LogicalLayer.LogicalSignatures.LogicalSignatures

/-!
# Domain signatures and interpretations

Blueprint items `def:domain-signature`, `def:domain-signature-notation`,
`def:domain-interpretation` (`blueprint/src/content.tex`, §"Domain layer",
`NeSyCat Theory v2`, `new.tex` 1--396) — the theory's third
signature/interpretation layer, built on `def:categorical-signature`
(`NeSyCat/CategoricalLayer/Signatures/Signatures.lean`): a domain
signature names sets of domain, (parameter) space, function, relation,
variable, and parameter symbols with typing data attached to each; a
writing convention displays a typed function/relation/variable/parameter
symbol the library's way; a domain interpretation assigns objects to
domain/space symbols and morphisms, valued in the actegory action `⋉`, to
function/relation symbols, with variable/parameter symbols interpreted as
identities.

**The `def:domain-signature-notation` no-Lean exemption, retired.**
`FORMALIZE.md`'s "Total Lean-mirror purity" law pins this environment as
the one `definition` with no Lean counterpart, by explicit prior user
decision. This ticket (C3-B2) attempted the honest counterpart the pin
itself invites — a `String`-valued display function realizing exactly the
written convention — and it lands cleanly:
`DomSignature.TypedSymbol.display` below. The environment is accordingly
given `\lean`/`\leanok` marks in `blueprint/src/content.tex`; the
`FORMALIZE.md` pin text itself is process documentation outside this
ticket's write set (`NeSyCat/**`, `blueprint/src/content.tex` marks,
`PROGRESS.md`) and is left for a follow-up documentation ticket to update
(recorded here and in `PROGRESS.md`).
-/

open CategoryTheory MonoidalCategory

universe u u' v v'

namespace NeSyCat

/-- Blueprint `def:domain-signature` (Domain signature): a domain
signature `Σ_γ` is given by a set of domain symbols `Dom` and a set of
(parameter) space symbols `Spc`; a set of function symbols `Fun` with
functions `dom, cod : Fun → List (Mon × Dom)` (one monad/domain marker per
argument, for the domain and codomain respectively) and
`par : Fun → List Spc` (its parameter spaces); a set of relation symbols
`Rel` with a function `ari : Rel → List (Mon × Dom)` and a function
`par : Rel → List Spc`; a set of variable symbols `Var` with a function
`ovr : Var → Dom`; and a set of parameter symbols `Par` with a function
`ovr : Par → Spc`. -/
structure DomSignature where
  /-- The set of domain symbols. -/
  Dom : Type
  /-- The set of (parameter) space symbols. -/
  Spc : Type
  /-- The set of function symbols. -/
  Fun : Type
  /-- The set of relation symbols. -/
  Rel : Type
  /-- The set of variable symbols. -/
  Var : Type
  /-- The set of parameter symbols. -/
  Par : Type
  /-- `dom : Fun → List (Mon × Dom)`, a function symbol's domain: a list
  of monad/domain-symbol pairs, one per argument. -/
  fdom : Fun → List (MonSym × Dom)
  /-- `cod : Fun → List (Mon × Dom)`, a function symbol's codomain. -/
  fcod : Fun → List (MonSym × Dom)
  /-- `par : Fun → List Spc`, a function symbol's list of parameter
  spaces. -/
  fpar : Fun → List Spc
  /-- `ari : Rel → List (Mon × Dom)`, a relation symbol's list of
  monad/domain-symbol pairs. -/
  rari : Rel → List (MonSym × Dom)
  /-- `par : Rel → List Spc`, a relation symbol's list of parameter
  spaces. -/
  rpar : Rel → List Spc
  /-- `ovr : Var → Dom`, a variable symbol's domain symbol. -/
  varOver : Var → Dom
  /-- `ovr : Par → Spc`, a parameter symbol's parameter space. -/
  parOver : Par → Spc

/-- Companion of `def:domain-signature-notation`: a domain-signature
symbol together with enough of its typing data to display it — a function
symbol, a relation symbol, a variable symbol, or a parameter symbol
(`DomSignature.TypedSymbol.display` interprets each case). -/
@[blueprint_internal] -- companion sum type for
-- DomSignature.TypedSymbol.display's domain; not itself cited
inductive DomSignature.TypedSymbol (sigG : DomSignature) where
  | fun_ (f : sigG.Fun)
  | rel (R : sigG.Rel)
  | var (x : sigG.Var)
  | par (θ : sigG.Par)

-- (completeness census, same pattern as `MonSym` in
-- `NeSyCat/CategoricalLayer/Signatures/Signatures.lean`: an
-- inductive-elaborator byproduct with no attribute site of its own, so it
-- is tagged post-hoc -- not blueprint-cited, plumbing of `TypedSymbol`)
attribute [blueprint_internal] DomSignature.TypedSymbol.ctorElimType

/-- Companion of `def:domain-signature-notation`: displays a single
monad/domain-symbol pair `M S` the way the environment writes it, "the
identity monad symbol `Id` is omitted from the display" — `S` alone when
`M = Id`, `name ++ S` (the ambient signature's own monad symbol name,
e.g. `"○"`) otherwise. -/
@[blueprint_internal] -- companion display helper for a single `M S`
-- pair, shared by the function- and relation-symbol display cases; not
-- itself cited
def displayMonDom {D : Type*} [ToString D] (name : String) :
    MonSym × D → String
  | (.id, S) => toString S
  | (.mon, S) => name ++ toString S

/-- Blueprint `def:domain-signature-notation` (Writing convention for
typed symbols): for a function symbol `f` with domain
`(M₁,S₁),…,(Mₙ,Sₙ)`, codomain `(N₁,T₁),…,(Nₘ,Tₘ)`, and parameter spaces
`Θ₁,…,Θₖ`, this library displays `f` as
`f_{Θ₁,…,Θₖ} : M₁S₁,…,MₙSₙ → N₁T₁,…,NₘTₘ`, subscripting the parameters,
and likewise `R_{Θ₁,…,Θₖ} : M₁S₁,…,MₙSₙ → τ` for a relation symbol `R`,
`Id` omitted in both from the display (`displayMonDom`). A variable
symbol `x` over domain symbol `S` is displayed `x : S`, and a parameter
symbol `θ` over parameter space `Θ` is displayed `θ : Θ`. -/
def DomSignature.TypedSymbol.display {sigG : DomSignature}
    [ToString sigG.Fun] [ToString sigG.Rel] [ToString sigG.Var]
    [ToString sigG.Par] [ToString sigG.Dom] [ToString sigG.Spc]
    (monName : String) : sigG.TypedSymbol → String
  | .fun_ f =>
    toString f ++
      "_{" ++ String.intercalate "," ((sigG.fpar f).map toString) ++ "} : " ++
      String.intercalate "," ((sigG.fdom f).map (displayMonDom monName)) ++
      " → " ++
      String.intercalate "," ((sigG.fcod f).map (displayMonDom monName))
  | .rel R =>
    toString R ++
      "_{" ++ String.intercalate "," ((sigG.rpar R).map toString) ++ "} : " ++
      String.intercalate "," ((sigG.rari R).map (displayMonDom monName)) ++
      " → τ"
  | .var x => toString x ++ " : " ++ toString (sigG.varOver x)
  | .par θ => toString θ ++ " : " ++ toString (sigG.parOver θ)

/-- Companion of `def:domain-interpretation`: `𝓘(M₁S₁,…,MₙSₙ) := 𝓘(M₁S₁)
⊠_C ⋯ ⊠_C 𝓘(MₙSₙ)` with `𝓘(MS) := 𝓘_α(M) 𝓘(S)`, the `⊠_C`-fold
interpretation of a list of monad/domain-symbol pairs against a chosen
categorical interpretation `I` and object-assignment `dObj`. -/
@[blueprint_internal] -- companion abbreviation,
-- `𝓘(M₁S₁,…,MₙSₙ) := 𝓘(M₁S₁) ⊠_C ⋯ ⊠_C 𝓘(MₙSₙ)`; not itself cited
def interpretMS {sigA : CatSignature} (I : CatInterpretation sigA)
    {Dom : Type} (dObj : Dom → I.cd.C) (l : List (MonSym × Dom)) :
    letI := I.cd.instCat; I.cd.C :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  tensorList (l.map (fun p => (I.interpretMon p.1).obj (dObj p.2)))

/-- Companion of `def:domain-interpretation`: `𝓘(Θ₁,…,Θₖ) := 𝓘(Θ₁) ⊠_A
⋯ ⊠_A 𝓘(Θₖ)`, the `⊠_A`-fold interpretation of a list of space symbols
against a chosen categorical interpretation `I` and object-assignment
`sObj`. -/
@[blueprint_internal] -- companion abbreviation,
-- `𝓘(Θ₁,…,Θₖ) := 𝓘(Θ₁) ⊠_A ⋯ ⊠_A 𝓘(Θₖ)`; not itself cited
def interpretSpc {sigA : CatSignature} (I : CatInterpretation sigA)
    {Spc : Type} (sObj : Spc → I.A) (l : List Spc) :
    letI := I.instCatA; I.A :=
  letI := I.instCatA; letI := I.instMonoidalA
  tensorList (l.map sObj)

/-- Blueprint `def:domain-interpretation` (Domain interpretation): a
domain interpretation `𝓘_γ` of a domain signature `Σ_γ` (`DomSignature`)
into the CD category `𝓘(C)` with its actegory `(𝓘(A), ⋉)` (a chosen
categorical interpretation `𝓘_α`, `CatInterpretation`) sets
`𝓘(M₁S₁,…,MₙSₙ) := 𝓘(M₁S₁) ⊠_C ⋯ ⊠_C 𝓘(MₙSₙ)` with
`𝓘(MS) := 𝓘_α(M)𝓘(S)` (`interpretMS`), and
`𝓘(Θ₁,…,Θₖ) := 𝓘(Θ₁) ⊠_A ⋯ ⊠_A 𝓘(Θₖ)` (`interpretSpc`), and assigns: an
object `𝓘(S) ∈ Ob_C` for each domain symbol `S`, and an object
`𝓘(Θ) ∈ Ob_A` for each space symbol `Θ`; for each function symbol
`f_{Θ₁,…,Θₖ} : M₁S₁,…,MₙSₙ → N₁T₁,…,NₘTₘ` a morphism
`𝓘(f) : 𝓘(Θ₁,…,Θₖ) ⋉ 𝓘(M₁S₁,…,MₙSₙ) → 𝓘(N₁T₁,…,NₘTₘ)` in `C`; for each
relation symbol `R_{Θ₁,…,Θₖ} : M₁S₁,…,MₙSₙ → τ` a morphism
`𝓘(R) : 𝓘(Θ₁,…,Θₖ) ⋉ 𝓘(M₁S₁,…,MₙSₙ) → Ω` in `C`, with `Ω` as in
`def:logical-interpretation` (`LogInterpretation`); and
`𝓘(x) := id_{𝓘(S)}` for each variable symbol `x : S`, and
`𝓘(θ) := id_{𝓘(Θ)}` for each parameter symbol `θ : Θ`
(`DomInterpretation.interpretVar`/`DomInterpretation.interpretPar`). -/
structure DomInterpretation {sigA : CatSignature} (I : CatInterpretation sigA)
    {sigB : LogSignature} (J : LogInterpretation I sigB) (sigG : DomSignature) where
  /-- The interpretation `𝓘(S) ∈ Ob_C` of a domain symbol `S`. -/
  domObj : sigG.Dom → I.cd.C
  /-- The interpretation `𝓘(Θ) ∈ Ob_A` of a space symbol `Θ`. -/
  spcObj : sigG.Spc → I.A
  /-- The morphism
  `𝓘(f) : 𝓘(Θ₁,…,Θₖ) ⋉ 𝓘(M₁S₁,…,MₙSₙ) → 𝓘(N₁T₁,…,NₘTₘ)` in `C` for each
  function symbol `f`. -/
  funMor : ∀ f : sigG.Fun, letI := I.cd.instCat;
      I.act (interpretSpc I spcObj (sigG.fpar f))
        (interpretMS I domObj (sigG.fdom f)) ⟶
      interpretMS I domObj (sigG.fcod f)
  /-- The morphism `𝓘(R) : 𝓘(Θ₁,…,Θₖ) ⋉ 𝓘(M₁S₁,…,MₙSₙ) → Ω` in `C` for
  each relation symbol `R`. -/
  relMor : ∀ R : sigG.Rel, letI := I.cd.instCat;
      I.act (interpretSpc I spcObj (sigG.rpar R))
        (interpretMS I domObj (sigG.rari R)) ⟶
      J.Ω

/-- Companion of `def:domain-interpretation`'s closing clause,
`𝓘(x) := id_{𝓘(S)}` for a variable symbol `x : S`: the identity morphism
on `x`'s domain interpretation. -/
@[blueprint_internal] -- definitional companion of
-- def:domain-interpretation's `𝓘(x) := id_{𝓘(S)}` clause
def DomInterpretation.interpretVar {sigA : CatSignature}
    {I : CatInterpretation sigA} {sigB : LogSignature}
    {J : LogInterpretation I sigB} {sigG : DomSignature}
    (D : DomInterpretation I J sigG) (x : sigG.Var) :
    letI := I.cd.instCat; D.domObj (sigG.varOver x) ⟶ D.domObj (sigG.varOver x) :=
  letI := I.cd.instCat; 𝟙 _

/-- Companion of `def:domain-interpretation`'s closing clause,
`𝓘(θ) := id_{𝓘(Θ)}` for a parameter symbol `θ : Θ`: the identity morphism
on `θ`'s space interpretation. -/
@[blueprint_internal] -- definitional companion of
-- def:domain-interpretation's `𝓘(θ) := id_{𝓘(Θ)}` clause
def DomInterpretation.interpretPar {sigA : CatSignature}
    {I : CatInterpretation sigA} {sigB : LogSignature}
    {J : LogInterpretation I sigB} {sigG : DomSignature}
    (D : DomInterpretation I J sigG) (θ : sigG.Par) :
    letI := I.instCatA; D.spcObj (sigG.parOver θ) ⟶ D.spcObj (sigG.parOver θ) :=
  letI := I.instCatA; 𝟙 _

end NeSyCat
