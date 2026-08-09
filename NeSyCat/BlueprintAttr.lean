/-
Copyright (c) 2026 The NeSyCat Project (Daniel Romero Schellhorn). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Romero Schellhorn
-/
import Lean

/-!
# The `@[blueprint_internal]` attribute (C2-H2 item 2)

A root module (structure-mirror is folder-scoped, per
`scripts/blueprint.sh`'s STRUCTURE-MIRROR section — a root `.lean` file
like this one or `NeSyCat/Notation.lean`/`NeSyCat/Basic.lean` needs no
`NeSyCat/<Folder>/` counterpart), imported by every file that tags a
declaration with `@[blueprint_internal]`.

Replaces the former `-- blueprint: internal (<reason>)` comment-tag
convention (FORMALIZE.md's "internal-tag convention", C2-E4a/A2) with a
real Lean attribute, backed by `Lean.registerTagAttribute` (the same
`TagAttribute` machinery Mathlib itself uses for e.g.
`@[variable_alias]`). A comment can drift silently — nothing checks that
its text is even attached to the declaration a reader assumes; an
attribute is elaborated, kernel-checked plumbing: `scripts/blueprint.sh`'s
CENSUS section reads it back via `blueprintInternalAttr.hasTag`, not a
text regex.

The human-readable `(<reason>)` text that used to live inside the comment
tag itself stays behind as an ordinary comment on the declaration (same
line or the line above) wherever the migration (C2-H2) touched it —
reasons are for humans reading the source; the attribute alone is what
the machine checks.
-/

open Lean

/-- Marks a declaration as blueprint-internal: deliberately left uncited
by any `\lean{}` mark in `blueprint/src/content.tex` (a demoted A1
bijection-law companion — a `simp`/`_apply` unfolding lemma, a
round-trip half, a unit-law or monotonicity twin, a raw/corollary
doubling — or other pre-existing library-internal plumbing). See
FORMALIZE.md's "internal-tag convention" and `scripts/blueprint.sh`'s
CENSUS section, which reads this attribute (not source comments) to
classify every top-level declaration as either cited-once or tagged
internal. -/
initialize blueprintInternalAttr : TagAttribute ←
  registerTagAttribute `blueprint_internal
    "Marks a declaration as blueprint-internal: deliberately uncited by \
     any \\lean{} mark in blueprint/src/content.tex (see FORMALIZE.md's \
     internal-tag convention). Read by scripts/blueprint.sh's kernel-truth \
     CENSUS section."
