/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.BlueprintAttr
import NeSyCat.CategoricalLayer.Signatures.Signatures

/-!
# Logical signatures and interpretations

Blueprint items `def:logical-signature`, `def:logical-interpretation`
(`blueprint/src/content.tex`, §"Logical signatures", `NeSyCat Theory v2`,
`new.tex` 1--396) — the theory's second signature/interpretation layer,
built on `def:categorical-signature`/`def:categorical-interpretation`
(`NeSyCat/CategoricalLayer/Signatures/Signatures.lean`): a logical
signature names a truth symbol, a set of connective symbols (each with an
arity and a monad symbol), and a set of quantifier symbols (each with a
monad symbol); a logical interpretation assigns an object `Ω` to the truth
symbol, an `n`-ary morphism to each connective symbol, and an
`ℕ`-indexed family of `n`-ary morphisms to each quantifier symbol.

**The comparison-symbol gap (disclosed, not resolved here).** The
environment's prose additionally names a "comparison symbol" `≺` with
arity `n` and monad symbol `M`, written `≺ : Mτⁿ → MBool` rather than the
plain connective's `Mτⁿ → Mτ`. The `def:logical-signature` "consists of"
sentence, however, itemizes only `τ`, `Conn` (arity + monad), and `Quan`
(monad) as data — it never introduces a field distinguishing which
elements of `Conn` are "comparison" symbols targeting a `Bool`-sorted
codomain versus the ordinary `τ`-sorted one; the `≺ : Mτⁿ → MBool`
sentence reads as a display convention alongside the plain-connective and
quantifier ones, not as new signature data (paralleling
`def:domain-signature-notation`'s role for the domain layer, only folded
into the same environment rather than split out). `LogSignature.Conn`
below is accordingly encoded with exactly the stated data (arity, monad),
no `Bool`-codomain marker. `def:logical-interpretation` confirms this
reading is at least consistent: it interprets every connective symbol
uniformly via `I(*) : (I(M)Ω)^{⊠n} → I(M)Ω`, with no separate clause for
a `Bool`-valued morphism anywhere — so nothing downstream ever needs a
comparison/plain distinction either. `LogInterpretation.connMor` below
states exactly this, uniformly over all of `Conn`. This is flagged, not
silently resolved: the source document does not fully specify, as data,
how a reader is meant to tell a comparison symbol apart from a plain
connective symbol; if a future revision of the document adds a
`Bool`-codomain marker to `Conn`'s data (or a genuine Bool-valued
interpretation clause), this file's encoding will need revisiting.
-/

open CategoryTheory MonoidalCategory

universe u u' v v'

namespace NeSyCat

/-- Blueprint `def:logical-signature` (Logical signature): a logical
signature `Σ_β` consists of a truth symbol `τ`, a set of connective
symbols `Conn` each with an arity `n : ℕ` and a monad symbol `M ∈ Mon`,
and a set of (finite) quantifier symbols `Quan` each with a monad symbol
`M ∈ Mon`. See this file's module doc for why `Conn`'s data stops at
arity + monad symbol, with no separate field for the "comparison symbol"
notation the environment also describes. -/
structure LogSignature where
  /-- The truth symbol `τ`, a bare name (pure data, codes doctrine). -/
  tauSymbol : String
  /-- The set of connective symbols. -/
  Conn : Type
  /-- The arity `n` of a connective symbol. -/
  connArity : Conn → ℕ
  /-- The monad symbol `M` of a connective symbol. -/
  connMonad : Conn → MonSym
  /-- The set of (finite) quantifier symbols. -/
  Quan : Type
  /-- The monad symbol `M` of a quantifier symbol. -/
  quanMonad : Quan → MonSym

/-- Companion of `def:logical-interpretation`: the `⊠`-fold `X^{⊠n} := X
⊠ ⋯ ⊠ X` (`n` copies) and, more generally, `def:domain-interpretation`'s
list-indexed tensor `Y₁ ⊠ ⋯ ⊠ Yₙ`, folded right with the monoidal unit as
the base case. Shared companion infrastructure for both interpretation
environments; not itself blueprint-cited. -/
@[blueprint_internal] -- companion tensor-fold helper (codomain of both
-- def:logical-interpretation's `(I(M)Ω)^⊠n` and def:domain-interpretation's
-- list-indexed `⊠`-folds); not itself cited by any environment
def tensorList {C : Type u} [Category.{v} C] [MonoidalCategory C] :
    List C → C
  | [] => 𝟙_ C
  | X :: Xs => X ⊗ tensorList Xs

/-- Companion of `def:logical-interpretation`/`def:domain-interpretation`:
`(I(M)Ω)^{⊠n}`, the `n`-fold tensor power of the monad-symbol-`M`
interpretation of a fixed object `Ω`, via `tensorList` and
`CatInterpretation.interpretMon`. -/
@[blueprint_internal] -- companion abbreviation, `(I(M)Ω)^⊠n`; not itself
-- cited by any environment
def interpretPow {sigA : CatSignature} (I : CatInterpretation sigA)
    (Ω : I.cd.C) (M : MonSym) (n : ℕ) : letI := I.cd.instCat; I.cd.C :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  tensorList (List.replicate n ((I.interpretMon M).obj Ω))

/-- Blueprint `def:logical-interpretation` (Logical interpretation): a
logical interpretation `𝓘_β` of a logical signature `Σ_β`
(`LogSignature`) in a CD category `𝓘(C)` (via a chosen categorical
interpretation `𝓘_α`, `CatInterpretation`) is given by an object
`Ω := 𝓘(τ)`, a morphism
`𝓘(*) : (𝓘(M)Ω)^{⊠n} → 𝓘(M)Ω` for each connective symbol `* : Mτⁿ → Mτ`
of arity `n`, and a family of morphisms `{𝓘(Q)_n}_{n ∈ ℕ}`,
`𝓘(Q)_n : (𝓘(M)Ω)^{⊠n} → 𝓘(M)Ω`, for each quantifier symbol `Q` with
monad symbol interpreted as `𝓘(M)`. See this file's module doc for the
comparison-symbol gap: `connMor` interprets every connective symbol
uniformly, exactly as the environment states, with no separate
`Bool`-valued clause. -/
structure LogInterpretation {sigA : CatSignature} (I : CatInterpretation sigA)
    (sigB : LogSignature) where
  /-- The interpretation `Ω := 𝓘(τ)` of the truth symbol. -/
  Ω : I.cd.C
  /-- The morphism `𝓘(*) : (𝓘(M)Ω)^{⊠n} → 𝓘(M)Ω` for each connective
  symbol `*` of arity `n` and monad symbol `M`. -/
  connMor : ∀ c : sigB.Conn, letI := I.cd.instCat;
      interpretPow I Ω (sigB.connMonad c) (sigB.connArity c) ⟶
      (I.interpretMon (sigB.connMonad c)).obj Ω
  /-- The family of morphisms `𝓘(Q)_n : (𝓘(M)Ω)^{⊠n} → 𝓘(M)Ω`, one for
  every `n ∈ ℕ`, for each quantifier symbol `Q` with monad symbol `M`. -/
  quanMor : ∀ (Q : sigB.Quan) (n : ℕ), letI := I.cd.instCat;
      interpretPow I Ω (sigB.quanMonad Q) n ⟶
      (I.interpretMon (sigB.quanMonad Q)).obj Ω

end NeSyCat
