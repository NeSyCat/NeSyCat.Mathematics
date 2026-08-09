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
# Wire adapters, the bind set, and the feed-forward composite

Blueprint items `def:wire-adapters` and `def:feed-forward`
(`blueprint/src/content.tex`, §"Grammatical layer", `NeSyCat Theory v2`,
`new.tex` 1--396): composing two composable typed symbols
`f : M₁^f S₁,…,Mₙ^f Sₙ → N₁^f T₁,…,Nₘ^f Tₘ` and
`g : M₁^g T₁,…,Mₘ^g Tₘ → N₁^g U₁,…,Nₖ^g Uₖ`, whose markers on the
`m` shared domain symbols `T₁,…,Tₘ` need not agree, needs one
**adapter** `α_j` per shared wire `j`, and the wires whose markers
mismatch (`N^f_j = ○`, `M^g_j = Id`) form the **bind set** `J`; the
**feed-forward composite** `𝓘(f) ⨟ 𝓘(g)` threads the bind-set wires
through the monad, in list order.

**The STRENGTH TRAP.** `def:categorical-interpretation`
(`NeSyCat/CategoricalLayer/Signatures/Signatures.lean`) bundles only "a
monad" for `CatInterpretation.monad`, no tensorial-strength data — the
section opener's "Kleisli category of a **strong** monad" is scene-
setting prose about the layer as a whole, not itself an environment.
`def:wire-adapters`' own per-wire table needs no strength (`adapter`
below is built from `CatInterpretation.monad`'s unit `η` alone).
`def:feed-forward` is the FIRST environment in the whole document that
actually writes down a strength morphism (`σ^{(j)}`, in its point-free
form) — so this is where strength enters the Lean encoding, as
`StrongCatInterpretation` below: a companion wrapper of
`CatInterpretation`, living in the Grammatical layer (not a field added
to `CatInterpretation` itself, out of this ticket's write set, and a
natural fold candidate for a future ticket once `CatInterpretation`'s
own file is back in scope). Threading multiple tensor-factor wires
through a Kleisli-style bind, at the fully abstract CD-category level
this layer is stated at, is only meaningful via strength: the Do-form
composite below (`feedForward`) uses `StrongCatInterpretation.dst`
internally for exactly this reason, alongside the point-free
reformulation the document itself displays.
-/

open CategoryTheory MonoidalCategory

universe u u' v v'

namespace NeSyCat

/-- Companion of `def:wire-adapters`: which monad symbol a wire's
adapter lands in — `Id` when both markers are `Id` (row 1), `○` in
every other case (rows 2, 3, 4: an output-`○` wire always lands in `○`,
matching the table's own last row, where the adapter still lands in
`𝓜𝓘(T_j)` rather than the mismatched `𝓘(T_j)` the row's `Mᵍ_j = Id`
would expect). -/
@[blueprint_internal] -- companion of def:wire-adapters: which marker
-- the adapter's codomain carries
def adapterTargetMon (Nf Mg : MonSym) : MonSym :=
  match Nf with
  | .mon => .mon
  | .id => Mg

/-- Companion of `def:wire-adapters`: a wire's adapter codomain object,
`𝓘(adapterTargetMon N^f_j M^g_j, T_j)`. -/
@[blueprint_internal] -- companion of def:wire-adapters: the adapter's
-- codomain object
def adapterCod {sigA : CatSignature} (I : CatInterpretation sigA)
    (Nf Mg : MonSym) (X : I.cd.C) : letI := I.cd.instCat; I.cd.C :=
  letI := I.cd.instCat
  (I.interpretMon (adapterTargetMon Nf Mg)).obj X

/-- Blueprint `def:wire-adapters` (Wire adapters and bind set),
principal declaration: for a shared wire with output marker `N^f_j` and
input marker `M^g_j` interpreting a domain symbol as the object `X`,
the **adapter** `α_j` per the four-row table — `id_X` (`Id`/`Id`, pure),
`η_X` (`Id`/`○`, pure, Dirac passed as data), `id_{𝓜X}` (`○`/`○`, pure,
computation passed as data), and again `id_{𝓜X}` (`○`/`Id`, effectful:
`g` expects a value while `f` delivers a computation `𝓜X`, so no
morphism lands in the expected input object, and the wire needs
binding). -/
def adapter {sigA : CatSignature} (I : CatInterpretation sigA)
    (Nf Mg : MonSym) (X : I.cd.C) : letI := I.cd.instCat;
    (I.interpretMon Nf).obj X ⟶ adapterCod I Nf Mg X :=
  letI := I.cd.instCat
  match Nf, Mg with
  | .id, .id => 𝟙 X
  | .id, .mon => I.monad.η.app X
  | .mon, .id => 𝟙 (I.monad.obj X)
  | .mon, .mon => 𝟙 (I.monad.obj X)

/-- Companion of `def:wire-adapters`: a wire is in the **bind set** `J`
exactly on the table's last row, output marker `○` and input marker
`Id` — the row where no adapter lands in the expected input object. -/
@[blueprint_internal] -- companion of def:wire-adapters: bind-set
-- membership test for a single wire
def isBoundWire (Nf Mg : MonSym) : Bool :=
  match Nf, Mg with
  | .mon, .id => true
  | _, _ => false

/-- Companion of `def:wire-adapters`: the **bind set**
`J ⊆ {1,…,m}`, the positions (0-indexed) of the wires whose adapter
does not land in the expected input object. -/
@[blueprint_internal] -- companion of def:wire-adapters: the bind set
-- J as an explicit list of positions
def bindSet (l : List (MonSym × MonSym)) : List ℕ :=
  ((List.range l.length).zip l).filterMap fun p =>
    if isBoundWire p.2.1 p.2.2 then some p.1 else none

/-- Companion of `def:feed-forward`: `𝓘(dom(f)) = 𝓘(M₁^f T₁,…,Mₘ^f Tₘ)`,
the tensor of what `f` actually delivers on each wire, via the shared
`tensorList` companion of `def:logical-interpretation`/
`def:domain-interpretation`. -/
@[blueprint_internal] -- companion of def:feed-forward: the source
-- tensor `𝓘(dom(f))`
def sourceTensor {sigA : CatSignature} (I : CatInterpretation sigA)
    {Dom : Type} (dObj : Dom → I.cd.C) (l : List (MonSym × MonSym × Dom)) :
    letI := I.cd.instCat; I.cd.C :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  tensorList (l.map fun t => (I.interpretMon t.1).obj (dObj t.2.2))

/-- Companion of `def:feed-forward`: `𝓘(cod(g)) = 𝓘(M₁^g T₁,…,Mₘ^g Tₘ)`,
the tensor of what `g` actually expects on each wire. -/
@[blueprint_internal] -- companion of def:feed-forward: the target
-- tensor `𝓘(cod(g))`
def targetTensor {sigA : CatSignature} (I : CatInterpretation sigA)
    {Dom : Type} (dObj : Dom → I.cd.C) (l : List (MonSym × MonSym × Dom)) :
    letI := I.cd.instCat; I.cd.C :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  tensorList (l.map fun t => (I.interpretMon t.2.1).obj (dObj t.2.2))

/-- Companion of `def:feed-forward`: the tensor of the per-wire adapter
codomains, `𝓘(adapterTargetMon N^f_1 M^g_1, T_1),…`. -/
@[blueprint_internal] -- companion of def:feed-forward: the adapted
-- tensor's codomain object
def adaptedTensorCod {sigA : CatSignature} (I : CatInterpretation sigA)
    {Dom : Type} (dObj : Dom → I.cd.C) (l : List (MonSym × MonSym × Dom)) :
    letI := I.cd.instCat; I.cd.C :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  tensorList (l.map fun t => adapterCod I t.1 t.2.1 (dObj t.2.2))

/-- Companion of `def:feed-forward`: `α⃗ := α_1 ⊠ ⋯ ⊠ α_m`, the tensor
of the wire adapters, built by structural recursion on the wire list
(each step tensoring one more `adapter` onto the recursively-built
rest, matching `tensorList`'s own recursion). -/
@[blueprint_internal] -- companion of def:feed-forward: the tensored
-- adapter α⃗
def adaptedTensor {sigA : CatSignature} (I : CatInterpretation sigA)
    {Dom : Type} (dObj : Dom → I.cd.C) :
    (l : List (MonSym × MonSym × Dom)) →
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    sourceTensor I dObj l ⟶ adaptedTensorCod I dObj l
  | [] => letI := I.cd.instCat; letI := I.cd.instMonoidal; 𝟙 (𝟙_ I.cd.C)
  | t :: ts =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (adapter I t.1 t.2.1 (dObj t.2.2)) ⊗ₘ (adaptedTensor I dObj ts)

/-- Companion of `def:feed-forward`, resolving the STRENGTH TRAP (this
file's module doc): the data needed to state and prove the point-free
reformulation of the feed-forward composite — the monad's (right)
tensorial strength `σ : X ⊠ 𝓜Y → 𝓜(X ⊠ Y)` at every pair of objects. A
companion wrapper of `CatInterpretation`, not a field of it. -/
@[blueprint_internal] -- companion of def:feed-forward: the strength
-- datum feeding the point-free reformulation and the Do-form's own
-- recursive wire-sequencing (`bindWires`), not itself blueprint-cited
structure StrongCatInterpretation {sigA : CatSignature} (I : CatInterpretation sigA) where
  /-- `σ : X ⊠ 𝓜Y → 𝓜(X ⊠ Y)`, the monad's strength. -/
  strength : letI := I.cd.instCat; letI := I.cd.instMonoidal;
    ∀ {X Y : I.cd.C}, X ⊗ I.monad.obj Y ⟶ I.monad.obj (X ⊗ Y)

/-- Companion of `def:feed-forward`: the strength on the other side,
`𝓜X ⊠ Y → 𝓜(X ⊠ Y)`, derived from `strength` via the CD category's
symmetry (`β_`, `CDCategory.instSymmetric`). -/
@[blueprint_internal] -- companion of def:feed-forward: left strength,
-- derived from right strength via symmetry
def StrongCatInterpretation.leftStrength {sigA : CatSignature}
    {I : CatInterpretation sigA} (SI : StrongCatInterpretation I) {X Y : I.cd.C} :
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    I.monad.obj X ⊗ Y ⟶ I.monad.obj (X ⊗ Y) :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal; letI := I.cd.instSymmetric
  (β_ (I.monad.obj X) Y).hom ≫ SI.strength ≫ I.monad.map (β_ Y X).hom

/-- Companion of `def:feed-forward`: the double strength
`𝓜X ⊠ 𝓜Y → 𝓜(X ⊠ Y)`, combining `leftStrength`, `strength`, and the
monad's multiplication `μ` — the same left-then-right-then-join pattern
`NeSyCat/CategoricalLayer/SemiringMonads/SemiringMonad.lean`'s concrete
`dstL`/`dstR`/`dst` construction uses for the semiring monad, reused
here abstractly. -/
@[blueprint_internal] -- companion of def:feed-forward: double strength
def StrongCatInterpretation.dst {sigA : CatSignature}
    {I : CatInterpretation sigA} (SI : StrongCatInterpretation I) {X Y : I.cd.C} :
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    I.monad.obj X ⊗ I.monad.obj Y ⟶ I.monad.obj (X ⊗ Y) :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  SI.leftStrength ≫ I.monad.map SI.strength ≫ I.monad.μ.app (X ⊗ Y)

/-- Companion of `def:feed-forward`: `bind k := 𝓜k ⨟ μ` abbreviates
binding a continuation `k` against the monad's multiplication, exactly
as the document's point-free form names it. -/
@[blueprint_internal] -- companion of def:feed-forward: the document's
-- own `bind k := 𝓜k ⨟ μ` abbreviation
def StrongCatInterpretation.bind {sigA : CatSignature}
    {I : CatInterpretation sigA} (_SI : StrongCatInterpretation I) {X Y : I.cd.C}
    (k : letI := I.cd.instCat; X ⟶ I.monad.obj Y) :
    letI := I.cd.instCat; I.monad.obj X ⟶ I.monad.obj Y :=
  letI := I.cd.instCat
  I.monad.map k ≫ I.monad.μ.app Y

/-- Companion of `def:feed-forward`: the Do-form's wire-sequencing
engine, threading the bind-set wires through the monad in list order —
a bound wire (`adapterCod = 𝓜X`) is joined into the still-open
computation via `dst`; a passthrough wire (`adapterCod` already the
expected object `X`) is pushed inside the monad via `strength` alone.
Structural recursion on the wire list, matching a bound/passthrough
case split on the head wire's markers (`isBoundWire`). -/
@[blueprint_internal] -- companion of def:feed-forward: the recursive
-- wire-sequencing engine underlying the Do-form
def StrongCatInterpretation.bindWires {sigA : CatSignature}
    {I : CatInterpretation sigA} (SI : StrongCatInterpretation I)
    {Dom : Type} (dObj : Dom → I.cd.C) :
    (l : List (MonSym × MonSym × Dom)) →
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    adaptedTensorCod I dObj l ⟶ I.monad.obj (targetTensor I dObj l)
  | [] => letI := I.cd.instCat; letI := I.cd.instMonoidal; I.monad.η.app (𝟙_ I.cd.C)
  | (.mon, .id, S) :: ts =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (𝟙 (I.monad.obj (dObj S)) ⊗ₘ SI.bindWires dObj ts) ≫ SI.dst
  | (.id, .id, S) :: ts =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (𝟙 (dObj S) ⊗ₘ SI.bindWires dObj ts) ≫ SI.strength
  | (.id, .mon, S) :: ts =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (𝟙 (I.monad.obj (dObj S)) ⊗ₘ SI.bindWires dObj ts) ≫ SI.strength
  | (.mon, .mon, S) :: ts =>
    letI := I.cd.instCat; letI := I.cd.instMonoidal
    (𝟙 (I.monad.obj (dObj S)) ⊗ₘ SI.bindWires dObj ts) ≫ SI.strength

/-- Blueprint `def:feed-forward` (Feed-forward composite), principal
declaration, Do-form: with `f : Y → 𝓘(dom(f))` and
`g : 𝓘(cod(g)) → Z` composable per `def:wire-adapters`' shared wire
list `l`, the feed-forward composite
`𝓘(f) ⨟ 𝓘(g) : Y → 𝓜Z` adapts the wires (`adaptedTensor`), binds the
bind-set wires in list order (`bindWires`), and finally maps `g` inside
the monad — `𝓜g` in place of `bind(g ⨟ η)`, the two agreeing by the
monad's right unit law (`Monad.right_unit`; see
`feedForward_eq_pointFree` below). -/
def feedForward {sigA : CatSignature} {I : CatInterpretation sigA}
    (SI : StrongCatInterpretation I) {Dom : Type} (dObj : Dom → I.cd.C)
    {Y Z : I.cd.C} (l : List (MonSym × MonSym × Dom))
    (Fmor : letI := I.cd.instCat; Y ⟶ sourceTensor I dObj l)
    (Gmor : letI := I.cd.instCat; targetTensor I dObj l ⟶ Z) :
    letI := I.cd.instCat; Y ⟶ I.monad.obj Z :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  Fmor ≫ adaptedTensor I dObj l ≫ SI.bindWires dObj l ≫ I.monad.map Gmor

/-- Companion of `def:feed-forward`: the point-free reformulation the
document displays alongside the Do-form,
`𝓘(f) ⨟ α⃗ ⨟ bindWires ⨟ bind(𝓘(g) ⨟ η)` — `bindWires` is itself the
`η ⨟ bind σ^{(j₁)} ⨟ ⋯ ⨟ bind σ^{(jᵣ)}` chain the document displays,
threading `bind` (`StrongCatInterpretation.bind`) against the
point-free `strength`/`dst` at each wire in turn (see `bindWires`
above); the final step names `g`'s own contribution the document's own
way, `bind(𝓘(g) ⨟ η)` rather than the Do-form's `𝓜g`. -/
@[blueprint_internal] -- companion of def:feed-forward: the document's
-- own point-free formula, restated via `bind`/`strength`
def StrongCatInterpretation.feedForwardPointFree {sigA : CatSignature}
    {I : CatInterpretation sigA} (SI : StrongCatInterpretation I)
    {Dom : Type} (dObj : Dom → I.cd.C) {Y Z : I.cd.C}
    (l : List (MonSym × MonSym × Dom))
    (Fmor : letI := I.cd.instCat; Y ⟶ sourceTensor I dObj l)
    (Gmor : letI := I.cd.instCat; targetTensor I dObj l ⟶ Z) :
    letI := I.cd.instCat; Y ⟶ I.monad.obj Z :=
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  Fmor ≫ adaptedTensor I dObj l ≫ SI.bindWires dObj l ≫ SI.bind (Gmor ≫ I.monad.η.app Z)

/-- Companion of `def:feed-forward`, the "Equivalently, point-free"
proof obligation: the Do-form composite `feedForward` agrees with its
point-free reformulation `feedForwardPointFree`, by the monad's right
unit law collapsing `bind(g ⨟ η)` back to `𝓜g` (`Monad.right_unit`,
naturality of `μ`). -/
@[blueprint_internal] -- companion of def:feed-forward: the point-free
-- agreement lemma (bijection law, the composite definition is the
-- env's one cited name)
theorem StrongCatInterpretation.feedForward_eq_pointFree {sigA : CatSignature}
    {I : CatInterpretation sigA} (SI : StrongCatInterpretation I)
    {Dom : Type} (dObj : Dom → I.cd.C) {Y Z : I.cd.C}
    (l : List (MonSym × MonSym × Dom))
    (Fmor : letI := I.cd.instCat; Y ⟶ sourceTensor I dObj l)
    (Gmor : letI := I.cd.instCat; targetTensor I dObj l ⟶ Z) :
    feedForward SI dObj l Fmor Gmor = SI.feedForwardPointFree dObj l Fmor Gmor := by
  letI := I.cd.instCat; letI := I.cd.instMonoidal
  unfold feedForward StrongCatInterpretation.feedForwardPointFree StrongCatInterpretation.bind
  erw [Functor.map_comp, Category.assoc, I.monad.right_unit, Category.comp_id]

end NeSyCat
