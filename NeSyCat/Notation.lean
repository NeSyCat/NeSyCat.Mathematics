/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import NeSyCat.Truth.BLat2Mon

/-!
# Scoped notation for the truth-value connectives

Scoped notation only — no theory lives here (that's
`NeSyCat/Truth/BLat2Mon.lean` and friends). Notation is `scoped` inside
`namespace NeSyCat`: automatically active for any `NeSyCat/*.lean` file
that reopens `namespace NeSyCat` (once this file is imported), opt-in
elsewhere via `open scoped NeSyCat`.

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
everywhere (as already used throughout `NeSyCat/Truth/BLat2Mon.lean` and
`NeSyCat/Truth/BoolInstance.lean`). Flagged for LEAD/user adjudication,
not an invented alternative glyph.

## The `⊕`/`⊗` swap was tried and reverted (C2-E4a, empirical fallback)

The C2-E4a decree asked for scoped `" ⊕ " => BLat2Mon.parr` / `" ⊗ " =>
BLat2Mon.andC` (⊗ tighter, precedences 70/65 mirroring the pin), matching
the semiring-scalar `⊕`/`⊗` already live via `NeSyCat.LatSRng`. Tested
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
how essentially every existing lemma in `NeSyCat/Truth/*.lean` is
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

Tested `&` (our `andC`) against `∧` (`Prop` and), `&&` (`Bool` and),
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

## Twin registry (`macros.sty` ↔ `NeSyCat/Notation.lean`)

Every `% Lean:`-tagged macro in the sibling `NeSyCat.Logics/macros.sty`
must appear, literally, on one line below (checked mechanically by
`scripts/blueprint.sh`'s registry-sync gate): either a live Lean
counterpart, or an honest `PLANNED` status naming where it lands.

-- \AndC  ↔ NeSyCat.BLat2Mon.andC (scoped notation " & ", this file)
-- \dzero ↔ NeSyCat.BLat2Mon.dzero (live field; the "0̇" glyph itself is
--          not notation-shipped by this ticket, only the bare name)
-- \done  ↔ NeSyCat.BLat2Mon.done (live field; the "1̇" glyph itself is
--          not notation-shipped by this ticket, only the bare name)
-- \impc  ↔ PLANNED (connective-indexed implication, S/R-implication /
--          residuation chapter, per the linear-logic dictionary table in
--          blueprint/src/content.tex, §"Truth-value structures")
-- \negc  ↔ PLANNED (connective-indexed negation, same later chapter;
--          note the *primitive* involution `DMStructure.dneg` is live
--          now, but the indexed family `negc[c]` is not)
-- \sem   ↔ PLANNED (chapter "Truth spaces and lifted connectives",
--          def:truth-space)
-- \bind  ↔ NeSyCat.bind (NeSyCat/Monad/SemiringMonad.lean) -- the
--          function is live; the "≫=" scoped infix notation is not
--          shipped yet
-- \seq   ↔ PLANNED (diagrammatic composition, category-theoretic
--          chapter)
-- \seqop ↔ PLANNED (def:feed-forward, later chapter)
-- \actop ↔ PLANNED (def:categorical-interpretation, actegory chapter)
-/

namespace NeSyCat

/-- The `⅋`-monoid multiplication of a `BLat2Mon` (linear logic's `⅋`,
"or-like"). `&` (below) binds tighter than `⅋`, matching linear logic's
own conventions and the blueprint's precedence. -/
scoped infixl:65 " ⅋ " => BLat2Mon.parr

/-- The `&`-monoid multiplication of a `BLat2Mon` (linear logic's
*multiplicative* conjunction `⊗`, kept as `&`/`andC` per `[NeSy26]`'s own
notation). -/
scoped infixl:70 " & " => BLat2Mon.andC

end NeSyCat
