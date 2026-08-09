/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Mathlib
import NeSyCat.Monad.LogIso
import NeSyCat.Truth.BLat2Mon
import NeSyCat.Truth.Lifted

/-!
# No De Morgan structure on the unbounded rows, and the square is not linear

Blueprint items `thm:no-dm-mass`, `thm:no-dm-log`, `thm:square-not-lin`
(`blueprint/src/content.tex`, §"Truth-value structures", per
`.foreman/C2-T5-spec.md`).

## `thm:no-dm-mass`/`thm:no-dm-log` (PINNED shape: the core order fact)

The Lean theorem is the *core order fact* — "there is no involutive
antitone map on `ℝ≥0`/`LogS`" — not a `¬ ∃ (DMStructure carrier), ...`
statement. This is not a weakening: a `DMStructure` mixin
(`NeSyCat/Truth/BLat2Mon.lean`) is only *statable* over a `[BLat2Mon α]`
instance, which itself demands `[Lattice α] [BoundedOrder α]`; `ℝ≥0` and
`LogS` carry no `BoundedOrder` instance at all (both are unbounded above,
matching `inst:massS-latcsrng`/`inst:logS-latcsrng`'s own honesty about
these rows), so "no DM
structure on `ℝ≥0`/`LogS`" is not even a well-formed Lean statement absent
an invented completion. The blueprint's own proof never uses any monoid
data either — only that `dneg` (whatever two-monoid structure it might
sit on top of) would be an involutive antitone self-map of the order — so
`no_antitone_involution_nnreal`/`no_antitone_involution_logS` state and
prove exactly that hypothesis is already impossible, which *subsumes* the
"hence no DM structure" clause: *any* De Morgan structure's `dneg` would in
particular be such a map (`DMStructure.dneg_dneg`/`dneg_antitone`), so its
mere existence already contradicts these theorems, on carriers where the
class could even be posed.

## `thm:square-not-lin` (PINNED shape: raw ops on `ℝ≥0ᵒᵈ × ℝ≥0`)

The carrier is `NeSyCat/Truth/Lifted.lean`'s order-family type at
`S := ℝ≥0`, i.e. `ℝ≥0ᵒᵈ × ℝ≥0` with Mathlib's product lattice — genuinely
*not* a `BLat2Mon` instance: the hard rail forbids registering one (the
carrier is unbounded above in slot `1`, so the class does not even apply —
part of the theorem's own content, "the square rows are BLat2Mon-with-DM
territory, not Lin", is precisely that no bounded/linear structure can be
built here). `andSq`/`parrSq` are the raw two-slot formulas of
`lem:lifted-mass`'s `twoSlot_andM_mass`/`twoSlot_parrM_mass`
(`NeSyCat/Truth/Lifted.lean`) transported through the `toDual`/`ofDual`
wrappers of slot `0`; `swapSq` is the slot swap of `def:order-family`'s
`orderedTwoSlot`. These are *defined* directly by formula (not derived via
`orderedTwoSlot`/`andM` transport) and are *provably* the same operations —
the doc comments below cite the bridging lemmas rather than re-deriving
through them.

The non-monotonicity witness (`andSq_not_monotone_right`) is the
theorem's core: `p = (1,0)`, `r = (5,0)`, `q = (0,10)`, `r ≤ q` in the
order family but `andSq p r = (5,0) ≰ (10,0) = andSq p q`. The blueprint's
proof additionally notes `parr` fails dually (via the cross term in its
*other* slot) "as it must", since `lem:dm-dual-law`'s antitone involution
exchanges the two operations — this dual witness is *not* separately
formalized here (optional per the ticket's own disclosure clause); the
required content for the theorem's conclusion is the `andC`/`andSq`
direction alone, via `andSq_not_lin` (the raw twin of `lem:lin-monotone`:
distributing over `⊔` in an argument forces monotonicity in it, so
non-monotonicity refutes the linear law by contraposition).
-/

namespace NeSyCat

open scoped NNReal ENNReal
open OrderDual

/-! ## `thm:no-dm-mass` -/

/-- Blueprint `thm:no-dm-mass` (No De Morgan structure on the mass row,
core order fact): on `ℝ≥0` there is no involutive antitone map. Proof: for
every `p`, `0 ≤ n p`, so antitonicity gives `p = n (n p) ≤ n 0`; but
`n 0 < n 0 + 1`, contradicting `n 0 + 1 ≤ n 0`. See the module doc comment
for why this core fact — not a `¬ DMStructure ℝ≥0` statement — is the
faithful Lean form. -/
theorem no_antitone_involution_nnreal :
    ¬ ∃ n : ℝ≥0 → ℝ≥0, (∀ p, n (n p) = p) ∧ Antitone n := by
  rintro ⟨n, hinv, hanti⟩
  have htop : ∀ p : ℝ≥0, p ≤ n 0 := fun p => by
    have h := hanti (bot_le : (0 : ℝ≥0) ≤ n p)
    rwa [hinv] at h
  have hlt : (n 0 : ℝ≥0) < n 0 + 1 := lt_add_of_pos_right (n 0) one_pos
  exact absurd (htop (n 0 + 1)) (not_le.mpr hlt)

/-! ## `thm:no-dm-log` -/

/-- Every element of `WithBot ℝ` has a strictly greater element: `⊥` is
beaten by any real coercion, and a finite `a` is beaten by `a + 1`. The
`WithBot ℝ`-level fact underlying `no_antitone_involution_logS` (`LogS`'s
own order is literally `WithBot ℝ`'s, via `NeSyCat/Monad/LogIso.lean`'s
`instLatticeLogS`), proved entirely at the `WithBot ℝ` level per that
file's own "build at `WithBot ℝ`, cast once" technique note. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
private theorem withBot_real_not_bddAbove (t : WithBot ℝ) : ∃ b : WithBot ℝ, t < b := by
  induction t using WithBot.recBotCoe with
  | bot => exact ⟨(0 : ℝ), WithBot.bot_lt_coe 0⟩
  | coe a => exact ⟨((a + 1 : ℝ) : WithBot ℝ), by exact_mod_cast lt_add_one a⟩

/-- Blueprint `thm:no-dm-log` (No De Morgan structure on the log row, core
order fact): on `LogS` (`= ℝ ∪ {-∞}`, `NeSyCat/Monad/LogIso.lean`) there is
no involutive antitone map. Proof: as in `no_antitone_involution_nnreal`,
`n ⊥` would be an upper bound for every `p : LogS`; but `WithBot ℝ` (hence
`LogS`, the same order) has no top element (`withBot_real_not_bddAbove`).
See the module doc comment for why this core fact subsumes the blueprint's
"hence no De Morgan structure" clause. -/
theorem no_antitone_involution_logS :
    ¬ ∃ n : LogS → LogS, (∀ p, n (n p) = p) ∧ Antitone n := by
  rintro ⟨n, hinv, hanti⟩
  have htop : ∀ p : LogS, p ≤ n ⊥ := fun p => by
    have h := hanti (bot_le : (⊥ : LogS) ≤ n p)
    rwa [hinv] at h
  obtain ⟨b, hb⟩ := withBot_real_not_bddAbove (n ⊥)
  exact absurd (htop b) (not_le.mpr hb)

/-! ## `thm:square-not-lin`: the square operations -/

/-- Blueprint `thm:square-not-lin` (the `\&`-lift's raw two-slot formula on
`ℝ≥0ᵒᵈ × ℝ≥0`): `andSq (a₀,a₁) (b₀,b₁) = (a₀b₀+a₀b₁+a₁b₀,\ a₁b₁)`, slot `0`
carried through the `toDual`/`ofDual` wrappers of the order-family type
(`def:order-family`). Provably equal to the lift `andM` transported through
`orderedTwoSlot` — `lem:lifted-mass`'s `twoSlot_andM_mass`
(`NeSyCat/Truth/Lifted.lean`) is exactly this formula at the un-dualized
`twoSlot` — but defined directly by formula here, not via that transport,
per the ticket's own pin. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
noncomputable def andSq (a b : ℝ≥0ᵒᵈ × ℝ≥0) : ℝ≥0ᵒᵈ × ℝ≥0 :=
  (toDual (ofDual a.1 * ofDual b.1 + ofDual a.1 * b.2 + a.2 * ofDual b.1), a.2 * b.2)

/-- Blueprint `thm:square-not-lin` (the `⅋`-lift's raw two-slot formula),
dually to `andSq`: `parrSq (a₀,a₁) (b₀,b₁) = (a₀b₀,\ a₀b₁+a₁b₀+a₁b₁)` —
`lem:lifted-mass`'s `twoSlot_parrM_mass` at the un-dualized `twoSlot`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
noncomputable def parrSq (a b : ℝ≥0ᵒᵈ × ℝ≥0) : ℝ≥0ᵒᵈ × ℝ≥0 :=
  (toDual (ofDual a.1 * ofDual b.1), ofDual a.1 * b.2 + a.2 * ofDual b.1 + a.2 * b.2)

/-- Blueprint `thm:square-not-lin` (the slot swap `dneg (w₀,w₁) = (w₁,w₀)`),
mod the `toDual`/`ofDual` wrappers — `def:order-family`'s slot-swap
negation, the candidate DM structure of this theorem. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
noncomputable def swapSq (w : ℝ≥0ᵒᵈ × ℝ≥0) : ℝ≥0ᵒᵈ × ℝ≥0 := (toDual w.2, ofDual w.1)

/-- Blueprint `thm:square-not-lin` (DM axiom (i), involution): `swapSq` is
its own inverse — immediate, `toDual`/`ofDual` cancel definitionally. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem swapSq_swapSq (w : ℝ≥0ᵒᵈ × ℝ≥0) : swapSq (swapSq w) = w := rfl

/-- Blueprint `thm:square-not-lin` (DM axiom (ii), antitonicity): `swapSq`
is antitone for the order family (slot `0` reversed, `def:order-family`) —
each component of the product order flips into the other under the swap. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem swapSq_antitone : Antitone swapSq := by
  intro a b hab
  exact ⟨toDual_le_toDual.mpr hab.2, ofDual_le_ofDual.mpr hab.1⟩

/-- Blueprint `thm:square-not-lin` (`andSq` commutativity), a ring-level
identity in `ℝ≥0` once the `toDual`/`ofDual` wrappers cancel. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem andSq_comm (a b : ℝ≥0ᵒᵈ × ℝ≥0) : andSq a b = andSq b a := by
  unfold andSq
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · congr 1; ring
  · ring

/-- Blueprint `thm:square-not-lin` (`andSq` associativity): the seven
cross terms of `andSq (andSq a b) c`/`andSq a (andSq b c)`'s slot-`0`
formula are literally the same seven monomials, `ring`-provably equal
(the mechanism `lem:linear-lift`'s `andM_assoc` already exercises one
level up, at general `[CommSemiring S]`). -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem andSq_assoc (a b c : ℝ≥0ᵒᵈ × ℝ≥0) : andSq (andSq a b) c = andSq a (andSq b c) := by
  unfold andSq
  simp only [ofDual_toDual, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · congr 1; ring
  · ring

/-- Blueprint `thm:square-not-lin` (`parrSq` commutativity), dually to
`andSq_comm`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem parrSq_comm (a b : ℝ≥0ᵒᵈ × ℝ≥0) : parrSq a b = parrSq b a := by
  unfold parrSq
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · congr 1; ring
  · ring

/-- Blueprint `thm:square-not-lin` (`parrSq` associativity), dually to
`andSq_assoc`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem parrSq_assoc (a b c : ℝ≥0ᵒᵈ × ℝ≥0) : parrSq (parrSq a b) c = parrSq a (parrSq b c) := by
  unfold parrSq
  simp only [ofDual_toDual, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · congr 1; ring
  · ring

/-- Blueprint `thm:square-not-lin` (`parr`-unit): the image of `Ret 0`
under `orderedTwoSlot` (`lem:lifted-mass`'s `twoSlot_ret_zero_mass`,
dualized in slot `0`), `(toDual 1, 0)`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
noncomputable def parrUnitSq : ℝ≥0ᵒᵈ × ℝ≥0 := (toDual 1, 0)

/-- Blueprint `thm:square-not-lin` (`andC`-unit): the image of `Ret 1`
under `orderedTwoSlot`, `(toDual 0, 1)`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
noncomputable def andUnitSq : ℝ≥0ᵒᵈ × ℝ≥0 := (toDual 0, 1)

/-- Blueprint `thm:square-not-lin` (`⅋`-unit law, left): `parrUnitSq` is a
left unit for `parrSq`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem parrUnitSq_parrSq (w : ℝ≥0ᵒᵈ × ℝ≥0) : parrSq parrUnitSq w = w := by
  unfold parrSq parrUnitSq; simp

/-- Blueprint `thm:square-not-lin` (`⅋`-unit law, right). -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem parrSq_parrUnitSq (w : ℝ≥0ᵒᵈ × ℝ≥0) : parrSq w parrUnitSq = w := by
  unfold parrSq parrUnitSq; simp

/-- Blueprint `thm:square-not-lin` (`&`-unit law, left): `andUnitSq` is a
left unit for `andSq`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem andUnitSq_andSq (w : ℝ≥0ᵒᵈ × ℝ≥0) : andSq andUnitSq w = w := by
  unfold andSq andUnitSq; simp

/-- Blueprint `thm:square-not-lin` (`&`-unit law, right). -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem andSq_andUnitSq (w : ℝ≥0ᵒᵈ × ℝ≥0) : andSq w andUnitSq = w := by
  unfold andSq andUnitSq; simp

/-- Blueprint `thm:square-not-lin` (DM axiom (iii), the dual law):
`swapSq (andSq a b) = parrSq (swapSq b) (swapSq a)`. A ring-level identity
after `toDual`/`ofDual` cancel — the same seven cross terms as `andSq`'s
formula, matched against `parrSq`'s. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem swapSq_dm (a b : ℝ≥0ᵒᵈ × ℝ≥0) : swapSq (andSq a b) = parrSq (swapSq b) (swapSq a) := by
  unfold swapSq andSq parrSq
  simp only [ofDual_toDual, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · congr 1; ring
  · ring

/-- Blueprint `thm:square-not-lin` (the core: `andSq` is not monotone).
Witness `p = (1,0)`, `r = (5,0)`, `q = (0,10)`: `r ≤ q` in the order family
(slot `1`: `0 ≤ 10`; slot `0` reversed: `5 ≥ 0`), but
`andSq p r = (5,0)` and `andSq p q = (10,0)`, and `(5,0) ≰ (10,0)` in the
reversed slot (`10 ≤ 5` is false). The mechanism is the cross term
`a₀b₁` in slot `0`: raising the *for*-weight `b₁` raises the *against*-slot
of the output. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem andSq_not_monotone_right :
    ¬ Monotone (andSq (toDual (1 : ℝ≥0), (0 : ℝ≥0))) := by
  intro hmono
  have hle : ((toDual (5 : ℝ≥0), (0 : ℝ≥0)) : ℝ≥0ᵒᵈ × ℝ≥0) ≤ (toDual (0 : ℝ≥0), (10 : ℝ≥0)) :=
    ⟨toDual_le_toDual.mpr (by norm_num), by norm_num⟩
  have hcontra := hmono hle
  have e1 : andSq (toDual (1 : ℝ≥0), (0 : ℝ≥0)) (toDual (5 : ℝ≥0), (0 : ℝ≥0))
      = (toDual (5 : ℝ≥0), (0 : ℝ≥0)) := by
    unfold andSq; simp
  have e2 : andSq (toDual (1 : ℝ≥0), (0 : ℝ≥0)) (toDual (0 : ℝ≥0), (10 : ℝ≥0))
      = (toDual (10 : ℝ≥0), (0 : ℝ≥0)) := by
    unfold andSq; simp
  rw [e1, e2] at hcontra
  have h1 := hcontra.1
  rw [toDual_le_toDual] at h1
  norm_num at h1

/-- Blueprint `thm:square-not-lin` (the "hence the linear laws fail"
bridge; raw twin of `lem:lin-monotone`): if `f` distributes over `⊔` in an
argument then `f` is monotone in it — on any `SemilatticeSup`, no
`BLat2Mon`/monoid structure needed. Proof: `p ≤ q` gives `p ⊔ q = q`, so
`f p ≤ f p ⊔ f q = f (p ⊔ q) = f q`. -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem monotone_of_distrib_sup {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (f : α → β) (hf : ∀ q r, f (q ⊔ r) = f q ⊔ f r) : Monotone f := by
  intro q r hqr
  calc f q ≤ f q ⊔ f r := le_sup_left
    _ = f (q ⊔ r) := (hf q r).symm
    _ = f r := by rw [sup_eq_right.mpr hqr]

/-- Blueprint `thm:square-not-lin` (conclusion: the linear laws fail):
`andSq` does not distribute over `⊔` in its right argument — by
contraposition of `monotone_of_distrib_sup` against the non-monotonicity
witness `andSq_not_monotone_right`. Hence, by `lem:lin-monotone`'s
contrapositive, the square rows carry no `LinBLat2Mon` structure: they are
"BLat2Mon-with-DM territory, not Lin". The dual failure of `parr`
(via its own cross term) is not separately formalized — optional per the
ticket's disclosure clause, and forced anyway by `swapSq_dm` exchanging
the two operations under an antitone involution. -/
theorem andSq_not_lin :
    ¬ ∀ p q r : ℝ≥0ᵒᵈ × ℝ≥0, andSq p (q ⊔ r) = andSq p q ⊔ andSq p r := fun hdist =>
  andSq_not_monotone_right (monotone_of_distrib_sup _ (hdist (toDual (1 : ℝ≥0), (0 : ℝ≥0))))

/-! ### Persistence in the bounded completion `[0,∞]²` -/

/-- Blueprint `thm:square-not-lin` (persistence witness): `andSq`'s raw
formula, restated verbatim at `ℝ≥0∞ᵒᵈ × ℝ≥0∞`, the bounded completion of
the order family. Not the deferred completion-*instances* work (no
`BLat2Mon`/`Lattice` machinery is built here) — just this theorem's final
clause, that the counterexample below persists unchanged. -/
-- blueprint: internal (C2-E4a/A2 completeness census: pre-existing
-- internal helper, not itself blueprint-cited)
noncomputable def andSqENN (a b : ℝ≥0∞ᵒᵈ × ℝ≥0∞) : ℝ≥0∞ᵒᵈ × ℝ≥0∞ :=
  (toDual (ofDual a.1 * ofDual b.1 + ofDual a.1 * b.2 + a.2 * ofDual b.1), a.2 * b.2)

/-- Blueprint `thm:square-not-lin` (persistence): the exact same witness
`p = (1,0)`, `r = (5,0)`, `q = (0,10)` refutes monotonicity of `andSqENN`
in `ℝ≥0∞ᵒᵈ × ℝ≥0∞` — "the counterexample persists unchanged in the bounded
completion `[0,∞]²`". -/
-- blueprint: internal (A1 bijection-law companion of
-- `andSq_not_lin`, content.tex thm:square-not-lin)
theorem andSqENN_not_monotone_right :
    ¬ Monotone (andSqENN (toDual (1 : ℝ≥0∞), (0 : ℝ≥0∞))) := by
  intro hmono
  have hle : ((toDual (5 : ℝ≥0∞), (0 : ℝ≥0∞)) : ℝ≥0∞ᵒᵈ × ℝ≥0∞) ≤
      (toDual (0 : ℝ≥0∞), (10 : ℝ≥0∞)) :=
    ⟨toDual_le_toDual.mpr (by norm_num), by norm_num⟩
  have hcontra := hmono hle
  have e1 : andSqENN (toDual (1 : ℝ≥0∞), (0 : ℝ≥0∞)) (toDual (5 : ℝ≥0∞), (0 : ℝ≥0∞))
      = (toDual (5 : ℝ≥0∞), (0 : ℝ≥0∞)) := by
    unfold andSqENN; simp
  have e2 : andSqENN (toDual (1 : ℝ≥0∞), (0 : ℝ≥0∞)) (toDual (0 : ℝ≥0∞), (10 : ℝ≥0∞))
      = (toDual (10 : ℝ≥0∞), (0 : ℝ≥0∞)) := by
    unfold andSqENN; simp
  rw [e1, e2] at hcontra
  have h1 := hcontra.1
  rw [toDual_le_toDual] at h1
  norm_num at h1

end NeSyCat
