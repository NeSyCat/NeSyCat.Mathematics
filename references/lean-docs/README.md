# Vendored Lean documentation

Full local copies of the four canonical Lean 4 references, vendored
for offline use by this repository's formalization work and agents.

| directory | upstream | pinned commit | license |
|---|---|---|---|
| fp-lean | https://github.com/leanprover/fp-lean | 02dbbeb | CC BY 4.0 (see README.md + LICENSE-ASSETS inside) |
| theorem_proving_in_lean4 | https://github.com/leanprover/theorem_proving_in_lean4 | 63fad08 | Apache 2.0 |
| mathematics_in_lean | https://github.com/leanprover-community/mathematics_in_lean | dd6d752 | Apache 2.0 |
| reference-manual | https://github.com/leanprover/reference-manual | a2fd71c | Apache 2.0 |

Retrieved 2026-08-09 via shallow clone. Excluded from each copy:
`.git/` history and web-font bundles (`static/fonts`, `book/static` —
identical ~39MB render-asset payloads, not book content). Everything
else, including full book sources (Verso/Markdown/Lean), examples,
mathematics_in_lean's rendered `html/` and PDF, is complete.

These are third-party reference materials, not part of the NeSyCat
library; nothing in `NeSyCat/` or `blueprint/` may cite them as a
mathematical source (provenance discipline unchanged).
