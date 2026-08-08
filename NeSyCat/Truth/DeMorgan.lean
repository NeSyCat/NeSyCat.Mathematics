/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.Truth.BLat2Mon

/-!
# The De Morgan calculus and its presentations

Blueprint items `lem:dm-lattice-laws`, `lem:dm-dual-law`, `lem:dm-unit-swap`,
`prop:dm-presentations`, `lem:dm-maps-units` (`blueprint/src/content.tex`,
§"Truth-value structures", per `.foreman/C2-T5-spec.md`).

## The DM lemma family (`[DMStructure α]`)

`dneg_inf`/`dneg_sup`/`dneg_bot`/`dneg_top` (`lem:dm-lattice-laws`),
`dneg_parr` (`lem:dm-dual-law`), `dneg_done`/`dneg_dzero`
(`lem:dm-unit-swap`), `dneg_maps_units` (`lem:dm-maps-units`) — all proved
at class level, over an ambient `[DMStructure α]`, matching the blueprint's
own generality ("for a DM structure ...").

**Route for `lem:dm-lattice-laws`**: direct antisymmetry pairs from
`dneg_antitone`/`dneg_dneg` alone (no `OrderIso` built), matching the
blueprint's own proof sketch ("`dneg` is an order-reversing bijection, and
an order-reversing bijection carries meets to joins ... and each bound to
the other") one inequality at a time — searched against building an
explicit `dnegOrderIso : α ≃o αᵒᵈ` and citing Mathlib's
`OrderIso.map_inf`/`map_sup`/`map_bot`/`map_top`, and found the direct route
shorter here (the `OrderIso`'s `map_rel_iff'` obligation fights the
`OrderDual` defeq-unfolding the same amount of work the direct antisymmetry
argument needs anyway).

**Helper for `lem:dm-unit-swap`**: `parr_unit_eq_dzero`, the private
two-sided-unit-is-`dzero` fact the blueprint's proof invokes ("`¬done` is a
two-sided `⅋`-unit, and monoid units are unique"): `e = e ⅋ dzero = dzero`,
the first `=` from the *right*-unit law for `dzero` (`BLat2Mon.parr_dzero`),
the second from `e`'s own *left*-unit hypothesis instantiated at `dzero`
— so, mechanically, only the left-unit hypothesis is consumed, but both are
kept as parameters to match the blueprint's own "two-sided" framing (the
proof site below supplies both, exactly mirroring its two displayed
computations `¬done ⅋ p = p` and `p ⅋ ¬done = p`).

## `prop:dm-presentations` (encoding choice: `List.TFAE`)

Stated as `List.TFAE [Antitone n, (lattice DM law), DMFullCalculus n]` over
raw data `[BLat2Mon α]`, `n : α → α`, `hinv : ∀ p, n (n p) = p`,
`hand : ∀ p q, n (andC p q) = parr (n q) (n p)` — the `Mathlib`
`tfae_have`/`tfae_finish` tactic pair handles the three-cycle bookkeeping
directly, no manual `List.Chain` plumbing needed (the encoding latitude the
pin allows; the fallback three-implication-cycle was not needed). `(a)⇒(c)`
builds `letI : DMStructure α := ⟨n, hinv, hanti, hand⟩` and assembles the
`DMFullCalculus` tuple purely from the class-level family lemmas above
(`dneg_inf`, `dneg_sup`, `dneg_bot`, `dneg_top`, `hand` itself, `dneg_parr`,
`dneg_done`, `dneg_dzero`, `hanti`) — no proof is duplicated. `(c)⇒(b)` is
the first `DMFullCalculus` field, literally `hc.1`. `(b)⇒(a)` is the
blueprint's own two-liner.
-/

namespace NeSyCat

open BLat2Mon DMStructure

section DMFamily

variable {α : Type*} [Lattice α] [BoundedOrder α] [BLat2Mon α] [DMStructure α]

/-- Blueprint `lem:dm-lattice-laws` (De Morgan, meet to join): for a DM
structure, `dneg (p ⊓ q) = dneg p ⊔ dneg q`. Proof: `dneg` is antitone, so
`dneg p, dneg q ≤ dneg (p ⊓ q)` (from `p ⊓ q ≤ p, q`), giving `≥`; for `≤`,
`dneg (dneg p ⊔ dneg q) ≤ dneg (dneg p) = p` and `≤ q` (again antitone, from
`dneg p, dneg q ≤ dneg p ⊔ dneg q`), so `≤ p ⊓ q`, and applying `dneg`
(antitone again) and involution recovers the claim. -/
theorem dneg_inf (p q : α) : dneg (p ⊓ q) = dneg p ⊔ dneg q := by
  apply le_antisymm
  · have h1 : dneg (dneg p ⊔ dneg q) ≤ p := by
      have := dneg_antitone (dneg p) (dneg p ⊔ dneg q) le_sup_left
      rwa [dneg_dneg] at this
    have h2 : dneg (dneg p ⊔ dneg q) ≤ q := by
      have := dneg_antitone (dneg q) (dneg p ⊔ dneg q) le_sup_right
      rwa [dneg_dneg] at this
    have h3 : dneg (dneg p ⊔ dneg q) ≤ p ⊓ q := le_inf h1 h2
    have h4 := dneg_antitone _ _ h3
    rwa [dneg_dneg] at h4
  · exact sup_le (dneg_antitone (p ⊓ q) p inf_le_left) (dneg_antitone (p ⊓ q) q inf_le_right)

/-- Blueprint `lem:dm-lattice-laws` (De Morgan, join to meet), dually:
`dneg (p ⊔ q) = dneg p ⊓ dneg q`. -/
theorem dneg_sup (p q : α) : dneg (p ⊔ q) = dneg p ⊓ dneg q := by
  apply le_antisymm
  · exact le_inf (dneg_antitone p (p ⊔ q) le_sup_left) (dneg_antitone q (p ⊔ q) le_sup_right)
  · have h1 : p ≤ dneg (dneg p ⊓ dneg q) := by
      have := dneg_antitone (dneg p ⊓ dneg q) (dneg p) inf_le_left
      rwa [dneg_dneg] at this
    have h2 : q ≤ dneg (dneg p ⊓ dneg q) := by
      have := dneg_antitone (dneg p ⊓ dneg q) (dneg q) inf_le_right
      rwa [dneg_dneg] at this
    have h3 : p ⊔ q ≤ dneg (dneg p ⊓ dneg q) := sup_le h1 h2
    have h4 := dneg_antitone _ _ h3
    rwa [dneg_dneg] at h4

/-- Blueprint `lem:dm-lattice-laws` (bound swap, bottom to top):
`dneg ⊥ = ⊤`. Proof: for every `p`, `⊥ ≤ dneg p`, so antitonicity gives
`p = dneg (dneg p) ≤ dneg ⊥`; taking `p := ⊤` gives `⊤ ≤ dneg ⊥`. -/
theorem dneg_bot : dneg (⊥ : α) = ⊤ := by
  apply le_antisymm le_top
  have h := dneg_antitone (⊥ : α) (dneg (⊤ : α)) bot_le
  rwa [dneg_dneg] at h

/-- Blueprint `lem:dm-lattice-laws` (bound swap, top to bottom), dually:
`dneg ⊤ = ⊥`. -/
theorem dneg_top : dneg (⊤ : α) = ⊥ := by
  apply le_antisymm _ bot_le
  have h := dneg_antitone (dneg (⊥ : α)) (⊤ : α) le_top
  rwa [dneg_dneg] at h

/-- Blueprint `lem:dm-dual-law` (the dual De Morgan law): for a DM
structure, `dneg (parr p q) = andC (dneg q) (dneg p)`. Proof: applying axiom
(iii) at `(dneg q, dneg p)` and involution gives
`dneg (andC (dneg q) (dneg p)) = parr p q`; applying `dneg` to both sides
and involution again recovers the claim. -/
theorem dneg_parr (p q : α) : dneg (parr p q) = andC (dneg q) (dneg p) := by
  have h : dneg (andC (dneg q) (dneg p)) = parr p q := by
    rw [dneg_andC, dneg_dneg, dneg_dneg]
  calc dneg (parr p q) = dneg (dneg (andC (dneg q) (dneg p))) := by rw [h]
    _ = andC (dneg q) (dneg p) := dneg_dneg _

omit [DMStructure α] in
/-- A two-sided `⅋`-unit equals `dzero` — the blueprint's `lem:dm-unit-swap`
proof helper ("monoid units are unique"): `e = e ⅋ dzero = dzero`, the
first `=` from `dzero`'s own right-unit law, the second from `e`'s
left-unit hypothesis instantiated at `dzero`. Both hypotheses are kept
(matching the blueprint's "two-sided" framing at the call site below),
though only the left one is consumed here. -/
private theorem parr_unit_eq_dzero {e : α}
    (hl : ∀ p, parr e p = p) (_hr : ∀ p, parr p e = p) : e = dzero :=
  (BLat2Mon.parr_dzero e).symm.trans (hl dzero)

/-- Blueprint `lem:dm-unit-swap` (negation swaps `done` to `dzero`): for a
DM structure, `dneg done = dzero`. Proof: `dneg done` is a two-sided
`⅋`-unit — `dneg done ⅋ p = dneg (andC (dneg p) done) = dneg (dneg p) = p`
and symmetrically — so `parr_unit_eq_dzero` applies. -/
theorem dneg_done : dneg (done : α) = dzero := by
  apply parr_unit_eq_dzero
  · intro p
    calc parr (dneg done) p = parr (dneg done) (dneg (dneg p)) := by rw [dneg_dneg]
      _ = dneg (andC (dneg p) done) := (dneg_andC (dneg p) done).symm
      _ = dneg (dneg p) := by rw [BLat2Mon.andC_done]
      _ = p := dneg_dneg p
  · intro p
    calc parr p (dneg done) = parr (dneg (dneg p)) (dneg done) := by rw [dneg_dneg]
      _ = dneg (andC done (dneg p)) := (dneg_andC done (dneg p)).symm
      _ = dneg (dneg p) := by rw [BLat2Mon.done_andC]
      _ = p := dneg_dneg p

/-- Blueprint `lem:dm-unit-swap` (negation swaps `dzero` to `done`), the
converse: `dneg dzero = done`, from `dneg_done` and involution. -/
theorem dneg_dzero : dneg (dzero : α) = done := by
  have h : dneg (dneg (done : α)) = dneg dzero := by rw [dneg_done]
  rw [dneg_dneg] at h
  exact h.symm

/-- Blueprint `lem:dm-maps-units` (negation maps invertibles to
invertibles): for a DM structure, if `p` is `andC`-invertible then `dneg p`
is `parr`-invertible, with witness `dneg q` for any `andC`-inverse `q` of
`p`. Proof: applying `dneg` and axiom (iii) to `andC q p = done` and
`andC p q = done` gives both `parr`-inverse equations directly, the
`dneg done = dzero` step via `dneg_done`. No Mathlib `IsUnit` — that
machinery is `Monoid`-bundled, and `BLat2Mon` deliberately is not
(`NeSyCat/Truth/BLat2Mon.lean`'s module doc comment). -/
theorem dneg_maps_units {p : α} (h : ∃ q, andC p q = done ∧ andC q p = done) :
    ∃ q', parr (dneg p) q' = dzero ∧ parr q' (dneg p) = dzero := by
  obtain ⟨q, hpq, hqp⟩ := h
  refine ⟨dneg q, ?_, ?_⟩
  · rw [← dneg_andC q p, hqp]; exact dneg_done
  · rw [← dneg_andC p q, hpq]; exact dneg_done

end DMFamily

/-! ### `prop:dm-presentations` -/

section Presentations

variable {α : Type*} [Lattice α] [BoundedOrder α] [BLat2Mon α]

/-- Blueprint `prop:dm-presentations` (presentation (c), "the full list"):
both lattice De Morgan pairs, the dual monoid law (matching the standing
hypothesis `hand`), the bound swap, the unit swap, and antitonicity —
exactly the calculus of `lem:dm-lattice-laws`, `lem:dm-dual-law`, and
`lem:dm-unit-swap`, packaged as one `Prop` so `dm_presentations` below can
name it as a single TFAE member. -/
def DMFullCalculus (n : α → α) : Prop :=
  (∀ p q : α, n (p ⊓ q) = n p ⊔ n q) ∧
  (∀ p q : α, n (p ⊔ q) = n p ⊓ n q) ∧
  (n (⊥ : α) = ⊤) ∧
  (n (⊤ : α) = ⊥) ∧
  (∀ p q : α, n (andC p q) = parr (n q) (n p)) ∧
  (∀ p q : α, n (parr p q) = andC (n q) (n p)) ∧
  (n (done : α) = dzero) ∧
  (n (dzero : α) = done) ∧
  Antitone n

/-- Blueprint `prop:dm-presentations` (Presentations of De Morgan
structure): over a BLat2Mon, given `n` satisfying the DM axioms (i)
`n (n p) = p` and (iii) `n (andC p q) = parr (n q) (n p)`, the following
are equivalent: (a) `n` is antitone; (b) `n (p ⊓ q) = n p ⊔ n q` for all
`p, q`; (c) the full De Morgan calculus (`DMFullCalculus n`) — and each
presentation yields all of it. (a)⇒(c): `letI : DMStructure α :=
⟨n, hinv, hanti, hand⟩` and cite the class-level family
(`dneg_inf`/`dneg_sup`/`dneg_bot`/`dneg_top`/`hand`/`dneg_parr`/
`dneg_done`/`dneg_dzero`/`hanti`) verbatim, no re-proof. (c)⇒(b) is the
first `DMFullCalculus` field. (b)⇒(a): if `p ≤ q` then `p = p ⊓ q`, so
`n p = n (p ⊓ q) = n p ⊔ n q ≥ n q`. -/
theorem dm_presentations (n : α → α)
    (hinv : ∀ p, n (n p) = p) (hand : ∀ p q, n (andC p q) = parr (n q) (n p)) :
    List.TFAE [Antitone n, (∀ p q : α, n (p ⊓ q) = n p ⊔ n q), DMFullCalculus n] := by
  tfae_have 1 → 3 := by
    intro hanti
    letI : DMStructure α := ⟨n, hinv, fun p q h => hanti h, hand⟩
    exact ⟨dneg_inf, dneg_sup, dneg_bot, dneg_top, hand, dneg_parr, dneg_done, dneg_dzero, hanti⟩
  tfae_have 3 → 2 := fun hc => hc.1
  tfae_have 2 → 1 := by
    intro hb p q hpq
    have e : p ⊓ q = p := inf_eq_left.mpr hpq
    calc n q ≤ n p ⊔ n q := le_sup_right
      _ = n (p ⊓ q) := (hb p q).symm
      _ = n p := by rw [e]
  tfae_finish

end Presentations

end NeSyCat
