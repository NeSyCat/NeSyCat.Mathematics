/-!
# NeSyCat

This is the NeSyCat library root module. The library is laid out flat,
with no wrapper folder: declarations live in the plain `NeSyCat`
namespace (e.g. `NeSyCat.tiltLemma`). As formalization work produces
content, topic folders (e.g. `Monad/`, `Truth/`, `Bridge/`) will
appear directly under `NeSyCat/`.

`blueprint/src/content.tex` is the canonical reference document for
what gets formalized here.

This file is currently a stub: it establishes the module and its
namespace so the `leanblueprint` scaffold (see `blueprint/`) has a Lean
target to link `\lean{...}` declarations against via
`scripts/blueprint.sh`'s declaration check. The itemized formalization
target — the actual definitions and theorems — is authored in a later
ticket (T-P3).
-/

namespace NeSyCat

end NeSyCat
