/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import NeSyCat.Truth.BLat2Mon
import NeSyCat.Monad.LatticeSemiring

/-!
# The Boolean row of the `BLat2Mon` hierarchy

Blueprint item `lem:bool-truth-structure` (`blueprint/src/content.tex`,
§"Truth-value structures", `[NeSy26, App. A]`): `BoolW` (see
`NeSyCat/Monad/LatticeSemiring.lean`), with `parr := ⊔`, `dzero := ⊥`,
`andC := ⊓`, `done := ⊤`, and `dneg := !·`, is a `LinBLat2CMon` with a
`DMStructure` and `UnitBounds` (`ZeroBot`/`OneTop`); the connective pairs
*collapse* onto the lattice/bound structure already on `BoolW` — the
idempotent case, unlike the probability/mass/log rows where `parr`/`andC`
are genuinely different from `⊔`/`⊓`.

Every field is decided by `decide` (`BoolW` is a `Fintype` with
`DecidableEq`, from `NeSyCat.LatticeSemiring`), rather than via general
distributive-lattice lemmas, to avoid depending on whether a
`DistribLattice BoolW` instance happens to be registered.
-/

namespace NeSyCat

namespace BoolW

/-- `BoolW`'s order is decidable (needed for the `decide`-based proofs
below, e.g. `instDMStructure`'s `dneg_antitone`): transported from `Bool`'s
decidable `≤`, since `BoolW`'s `Lattice`/`BoundedOrder` instances are
themselves transported from `Bool` via `inferInstanceAs`. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
instance decLe : DecidableRel ((· ≤ ·) : BoolW → BoolW → Prop) :=
  inferInstanceAs (DecidableRel ((· ≤ ·) : Bool → Bool → Prop))

/-- Blueprint `lem:bool-truth-structure` (`BLat2Mon BoolW`): `parr := ⊔`
(the blueprint's `(∨, 0)`), `andC := ⊓` (the blueprint's `(∧, 1)`),
`dzero := ⊥`, `done := ⊤`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `BoolW.parr_eq_sup`, content.tex lem:bool-truth-structure)
instance instBLat2Mon : BLat2Mon BoolW where
  parr := (· ⊔ ·)
  dzero := ⊥
  andC := (· ⊓ ·)
  done := ⊤
  parr_assoc := by decide
  dzero_parr := by decide
  parr_dzero := by decide
  andC_assoc := by decide
  done_andC := by decide
  andC_done := by decide

/-- Blueprint `lem:bool-truth-structure` (connective collapse, `⅋`): on
`BoolW` the `⅋`-monoid multiplication is exactly the lattice join --- the
"idempotent case" collapse of the connective pairs. -/
@[simp] theorem parr_eq_sup (p q : BoolW) : BLat2Mon.parr p q = p ⊔ q := rfl

/-- Blueprint `lem:bool-truth-structure` (connective collapse, `&`): on
`BoolW` the `&`-monoid multiplication is exactly the lattice meet. -/
-- blueprint: internal (A1 bijection-law companion of
-- `BoolW.parr_eq_sup`, content.tex lem:bool-truth-structure)
@[simp] theorem andC_eq_inf (p q : BoolW) : BLat2Mon.andC p q = p ⊓ q := rfl

/-- Blueprint `lem:bool-truth-structure` (`BLat2CMon BoolW`): both monoids
are commutative on `BoolW` (`⊔`, `⊓` are commutative). -/
-- blueprint: internal (A1 bijection-law companion of
-- `BoolW.parr_eq_sup`, content.tex lem:bool-truth-structure)
instance instBLat2CMon : BLat2CMon BoolW where
  __ := instBLat2Mon
  parr_comm := by decide
  andC_comm := by decide

/-- Blueprint `lem:bool-truth-structure` (`LinBLat2Mon BoolW`): linearity
holds on `BoolW`, checked directly by `decide` on the finite carrier (the
blueprint's own route is `thm:chain-lin` on the two-element chain, out of
scope for this ticket; this instance proves the same content by finite
case analysis instead). -/
-- blueprint: internal (A1 bijection-law companion of
-- `BoolW.parr_eq_sup`, content.tex lem:bool-truth-structure)
instance instLinBLat2Mon : LinBLat2Mon BoolW where
  __ := instBLat2Mon
  andC_sup := by decide
  sup_andC := by decide
  parr_inf := by decide
  inf_parr := by decide
  andC_bot := by decide
  bot_andC := by decide
  parr_top := by decide
  top_parr := by decide

/-- Blueprint `lem:bool-truth-structure` (`LinBLat2CMon BoolW`): the
commutative linear structure, combining `instLinBLat2Mon` and
`instBLat2CMon`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `BoolW.parr_eq_sup`, content.tex lem:bool-truth-structure)
instance instLinBLat2CMon : LinBLat2CMon BoolW where
  __ := instLinBLat2Mon
  parr_comm := by decide
  andC_comm := by decide

/-- Blueprint `lem:bool-truth-structure` (De Morgan structure on `BoolW`):
`dneg := !·` (Boolean negation) is involutive, antitone, and satisfies the
De Morgan law `dneg (andC p q) = parr (dneg q) (dneg p)`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `BoolW.parr_eq_sup`, content.tex lem:bool-truth-structure)
instance instDMStructure : DMStructure BoolW where
  dneg p := !p
  dneg_dneg := by decide
  dneg_antitone := by decide
  dneg_andC := by decide

/-- Blueprint `lem:bool-truth-structure` (ZeroBot on `BoolW`): `dzero = ⊥`
by construction of `instBLat2Mon`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `BoolW.parr_eq_sup`, content.tex lem:bool-truth-structure)
instance instZeroBot : ZeroBot BoolW where
  dzero_eq_bot := rfl

/-- Blueprint `lem:bool-truth-structure` (OneTop on `BoolW`): `done = ⊤`
by construction of `instBLat2Mon`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `BoolW.parr_eq_sup`, content.tex lem:bool-truth-structure)
instance instOneTop : OneTop BoolW where
  done_eq_top := rfl

end BoolW

end NeSyCat
