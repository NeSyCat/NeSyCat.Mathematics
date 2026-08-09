/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import NeSyCat.LogicalLayer.TruthStructures.BLat2Mon

/-!
# Notation history and the `macros.sty` twin registry

No theory lives here (that's
`NeSyCat/LogicalLayer/TruthStructures/BLat2Mon.lean` and friends), and — as
of C2-E4b — no live notation either: the scoped `⅋`/`&` infix notation this
file used to declare is retired (user adjudication, below); the truth-value
connectives are named directly (`BLat2Mon.oplus`/`BLat2Mon.otimes`, or the
bare `oplus`/`otimes` field names once the structure is opened). This file's
job now is purely historical record (the reverted notation experiments) and
the `macros.sty` twin registry that `scripts/blueprint.sh` checks
mechanically.

## The `¬` overload was tried and reverted (empirical fallback)

The pin asked for `scoped prefix:max "¬" => DMStructure.dneg`, attempted
and empirically tested against ordinary `Prop` negation in the same
scope. It poisons elaboration: e.g. (isolated single-level use, no
nesting, no interaction with `&`/`⅋`)

```
scoped prefix:max "¬" => DMStructure.dneg
example (p q : α) (h : p ≤ q) : ¬q ≤ ¬p := DMStructure.dneg_antitone p q h
-- error: Type mismatch
--   DMStructure.dneg_antitone p q h
-- has type
--   ¬q ≤ ¬p
-- but is expected to have type
--   ¬q ≤ ¬p
```

(the two displayed types are the *same pretty-print* of two different
elaborations of the ascribed-vs-inferred `¬`, so the check fails despite
looking identical). The identical statement typechecks immediately with
`¬` replaced by the qualified name `DMStructure.dneg`, isolating the
overload as the cause. Per the pin's own fallback protocol: **no `¬`
overload is shipped**; `DMStructure.dneg` remains the working name
everywhere (as already used throughout `NeSyCat/LogicalLayer/TruthStructures/BLat2Mon.lean` and
`NeSyCat/LogicalLayer/TruthStructures/BoolInstance.lean`). Flagged for LEAD/user adjudication,
not an invented alternative glyph.

## The `⊕`/`⊗` swap was tried and reverted (C2-E4a, empirical fallback)

The C2-E4a decree asked for scoped `" ⊕ " => BLat2Mon.parr` / `" ⊗ " =>
BLat2Mon.andC` (⊗ tighter, precedences 70/65 mirroring the pin), matching
the semiring-scalar `⊕`/`⊗` already live via `NeSyCat.LatSRng`. (Names as
they stood at the time of this experiment; C2-E4c later renamed the
fields themselves `oplus`/`otimes` — the transcript below is reproduced
verbatim as run, not touched, since it records a reverted experiment's
actual error trace.) Tested
against the same conflict candidates the pin named: Lean core's `Sum`
type notation (`α ⊕ β`, a GLOBAL, always-open infixr, unlike our
`scoped` one) and Mathlib's scoped `TensorProduct` `⊗`. `⊗` alone is
clean (Mathlib's own `⊗` is itself `scoped`, so it is never active
without its own `open scoped`, and no conflict surfaces even with the
same style of test below). `⊕` is **not** clean:

```
scoped infixl:65 " ⊕ " => BLat2Mon.parr
theorem foo {α : Type*} [Lattice α] [BoundedOrder α] [BLat2Mon α] (p q : α) :
    p ⊕ q = p ⊕ q := rfl
-- error: Application type mismatch: The argument
--   p
-- has type
--   α
-- of sort `Type u_1` but is expected to have type
--   Type ?u.12
-- of sort `Type (?u.12 + 1)` in the application
--   Sum p
```

With no expected type available to anchor elaboration (the ordinary
shape of a bare equation in a `theorem`/`lemma` statement -- exactly
how essentially every existing lemma in `NeSyCat/LogicalLayer/**/*.lean` is
written, e.g. `dneg (dneg p) = p` with no type ascription), Lean tries
Sum's global `⊕` notation for `p ⊕ q` before our scoped one, reads `p`
as a *type* argument to `Sum`, and the whole elaboration poisons --
reproducible with `⊕` alone, independent of whether `⊗` is even in
scope. An explicit type ascription (`(p ⊕ q : α) = ...`) works around
it, but requiring that on every ordinary lemma statement is not a
notation this library can ship. Per the pin's own fallback protocol
(same shape as the `¬`-episode below): **no `⊕`/`⊗` swap is shipped**;
the existing `⅋`/`&` scoped notation (below) remains live and
unchanged. Flagged for LEAD/user adjudication, not an invented
alternative glyph; E4b's macros.sty-side work (`\llparr`, the box
tensor, deleting the LaTeX-only `\parr`/`\AndC` macros) is independent
of this Lean-side finding and unaffected by it.

## `&` conflict test (empirical, no conflict found)

Tested `&` (our `otimes`) against `∧` (`Prop` and), `&&` (`Bool` and),
structure literals (`{ x := _ }`, `{ s with x := _ }`), and precedence
against our own `⅋`, all in the same scope — no conflict; see the
(deleted) scratch file used for this test, reproduced here as the shape
of what was checked:

```
example (p q : α) : α := p & q
example (a b : Prop) (h : a ∧ b) : a ∧ b := h
example (a b : Bool) : Bool := a && b
example : Foo := { x := 3 }
example (f : Foo) : Foo := { f with x := 5 }
example (p q r : α) : p & q ⅋ r = (p & q) ⅋ r := rfl  -- `&` binds tighter
```

## The `⅋`/`&` scoped notation itself is RETIRED (C2-E4b, user adjudication)

Despite the clean empirical result directly above, the notation is not
shipped: E4a's own probe (the `⊕`/`⊗` swap episode) showed Lean core's
global notation beats a scoped alternative in exactly the ordinary
no-expected-type shape this library writes constantly, and the user
adjudicated that the fix is not to keep hunting for a glyph pair immune to
every such conflict, but to drop glyph notation for the truth-value
connectives ENTIRELY: plain field names (`BLat2Mon.oplus`,
`BLat2Mon.otimes`, opened as bare `oplus`/`otimes` via `open NeSyCat` or
qualified) are the working Lean surface, per the `dneg` precedent (the `¬`
overload above was tried and reverted for the same reason). The `⊕`/`⊗`
story lives in LaTeX (`macros.sty`, `blueprint/src/content.tex`); Lean
speaks plain names. The two `scoped infixl` declarations that used to live
below (`" ⅋ " => BLat2Mon.oplus`, `" & " => BLat2Mon.otimes`) are deleted;
grepped clean across `NeSyCat/` first (zero uses in any statement or
proof, only in doc-comment prose naming the LaTeX symbols, which is
expected and left as prose). Field names `oplus`/`otimes` themselves are
unaffected and unchanged.

## The `(priority := high)` retry was tried and reverted again (C2-H2 item 4, empirical fallback)

User-approved retry: the C2-E4a episode above never set a notation
`priority`, and priority governs which of several candidate parsers wins
when more than one matches the same token — plausibly the missing
ingredient, since `priority := high` is a documented, real mechanism
(confirmed working via `scoped[Convex] notation (priority := high) "["
x " -[" 𝕜 "] " y "]" => segment 𝕜 x y` in Mathlib's own
`Mathlib/Analysis/Convex/Segment.lean`). Retried directly against
`BLat2Mon.oplus`/`BLat2Mon.otimes` (the post-C2-E4c field names):

```
namespace NeSyCat
scoped notation:65 (priority := high) a:65 " ⊕ " b:66 => BLat2Mon.oplus a b
scoped notation:70 (priority := high) a:70 " ⊗ " b:71 => BLat2Mon.otimes a b
end NeSyCat

open NeSyCat
example {α : Type*} [Lattice α] [BoundedOrder α] [BLat2Mon α] (p q : α) :
    p ⊕ q = p ⊕ q := rfl
-- error: Application type mismatch: The argument
--   p
-- has type
--   α
-- of sort `Type u_1` but is expected to have type
--   Type ?u.12
-- of sort `Type (?u.12 + 1)` in the application
--   Sum p
```

**Identical failure, byte-for-byte the same error shape as C2-E4a's**:
`priority := high` (the named level, `10000`, per
`Init/Notation.lean`'s `macro "high" : prio => `(prio| 10000)`) does not
move the needle. Pushed further to rule out "high just isn't high
enough": re-tried with the maximum `Nat` priority literal
(`priority := 4294967295`) — same error, unchanged. A sanity probe
confirms the notation *mechanism* itself is sound and `priority := high`
parses and registers correctly: swapping the token for one with no core
conflict (`" <+++> "`) elaborates cleanly on the first try, same
declaration shape, same `open NeSyCat`, same no-expected-type context.
So the failure is specific to contesting the *token* `⊕` against Lean
core's global, unscoped `infixr:30 " ⊕ " => Sum`
(`Init/Core.lean`) — not a priority-value tuning problem. The most
plausible mechanism (unconfirmed from Lean's own source, but consistent
with every probe run across both episodes): a `scoped` notation's
candidacy for a token is gated *before* priority comparison even runs
against a competing *global* (unscoped) notation for the same token —
priority only breaks ties among notations already in the same
open/global candidate pool, and `⊕` is precisely the case where the
competitor is global while ours is scoped. `⊗`, by contrast, **stays
clean at `priority := high`** too (re-confirmed; Mathlib's own `⊗` for
`TensorProduct` is itself `scoped`, so it was never in the global pool to
begin with — the asymmetry between the two glyphs is exactly this
scoped-vs-global distinction, not a fluke of one probe run).

Per the pin's own fallback protocol (repeated a second time now): **no
`⊕`/`⊗` swap is shipped**, reverted together for the same reason C2-E4b
reverted the clean-testing `⅋`/`&` pair alongside the broken one — this
library does not maintain an asymmetric truth-connective notation surface
where one glyph works and its dual doesn't. `BLat2Mon.oplus`/
`BLat2Mon.otimes` remain the working Lean names, unchanged. Since the two
glyphs did **not** both land cleanly, the item 4 precondition for
touching `dneg` is unmet: `DMStructure.dneg` **stays a plain name**,
settled, not reopened by this retry. This closes the `⊕`/`⊗` notation
question permanently — a second independent mechanism (priority,
including the maximum possible `Nat` value) has now been tried and has
failed identically; no further glyph-notation experiments for these two
connectives are warranted.

## Twin registry (`macros.sty` ↔ `NeSyCat/Notation.lean`)

Every `% Lean:`-tagged macro in the sibling `NeSyCat.Logics/macros.sty`
must appear, literally, on one line below (checked mechanically by
`scripts/blueprint.sh`'s registry-sync gate): either a live Lean
counterpart, or an honest `PLANNED` status naming where it lands.

-- \AndC  ↔ RETIRED (C2-E4b: macros.sty deleted \AndC's "Lean:" tag along
--          with the macro itself, in the same step this line was removed
--          from the registry -- both sides of the twin retire together)
-- \dzero ↔ NeSyCat.BLat2Mon.dzero (live field; the bold render is a LaTeX-
--          only markup choice, no Lean notation glyph shipped)
-- \done  ↔ NeSyCat.BLat2Mon.done (live field; the bold render is a LaTeX-
--          only markup choice, no Lean notation glyph shipped)
-- \impc  ↔ PLANNED (connective-indexed implication, S/R-implication /
--          residuation chapter, per the linear-logic dictionary table in
--          blueprint/src/content.tex, §"Truth-value structures")
-- \negc  ↔ PLANNED (connective-indexed negation, same later chapter;
--          note the *primitive* involution `DMStructure.dneg` is live
--          now, but the indexed family `negc[c]` is not)
-- \sem   ↔ PLANNED (chapter "Truth spaces and lifted connectives",
--          abbr:truth-space)
-- \bind  ↔ NeSyCat.bind (NeSyCat/CategoricalLayer/SemiringMonads/SemiringMonad.lean) -- the
--          function is live; the "≫=" scoped infix notation is not
--          shipped yet
-- \seq   ↔ PLANNED (diagrammatic composition, category-theoretic
--          chapter)
-- \seqop ↔ PLANNED (def:feed-forward, later chapter)
-- \actop ↔ PLANNED (def:categorical-interpretation, actegory chapter)
-/

-- No live scoped notation remains (C2-E4b retirement, above): the
-- `⅋`/`&` declarations that used to live in a `namespace NeSyCat` block
-- here are deleted. This file (imported by the root `NeSyCat.lean`) now
-- declares nothing at all; it remains the registry home per the block
-- above, and imports only `BLat2Mon` for the registry's own
-- cross-references.
