"""
nesycatshapes -- local plastex package (C2-E9 shapes, C2-E11 proved-
status, C2-E14 instance collapse): dependency-graph node-shape and
proved-status fixes for definition-like environment kinds.

## C2-E9: shapes

plastexdepgraph's own default (`Packages/depgraph.py`, `to_dot`, read
at render time from `document.userdata['dep_graph'].get('shapes',
{'definition': 'box'})`) boxes only the `definition` environment kind
and renders every other kind -- including NeSyCat's `class`,
`abbreviation` and `instance` environments -- as an ellipse, the shape
depgraph's own hardcoded legend (set at its own package-load time, in
the same file) labels "theorems and lemmas". That is wrong for
`class`/`abbreviation`/`instance`: all three are definition-like, so
they belong with `definition` as boxes.

## C2-E14: `instance` is definition-like too (LEAD reversal)

C2-E9/C2-E11 kept `instance` an ellipse and two-event, reasoning that
an instance env asserts "this carrier satisfies the class's laws" and
so has a statement and a proof. That reasoning is withdrawn. In Lean an
`instance` IS a `def`: a term of a structure type whose law fields are
discharged during elaboration, with no separate proof declaration to
point at. There is no second event in the Lean, so there is none in the
graph either -- and the kind-inventory law ("the blueprint's
environments are EXACTLY Lean's own declaration kinds") already implied
it. `instance` therefore joins `definition`/`class`/`abbreviation` in
BOTH overrides below: box shape, and `\\leanok` on the statement ⇒
`proved` ⇒ fill ⇒ `fully_proved` propagation to dependents.

Instance envs that carry a paired `proof` env (this document has two,
whose proofs discharge law fields the construction does not display)
are handled identically to proofless ones: their statement's `\\leanok`
is the discharge, and the paired proof's own `\\leanok` -- which
leanblueprint had already turned into `proved` -- is redundant rather
than contradictory. The patch below never downgrades a `proved` flag
leanblueprint set, so the two shapes of instance env land on the same
colour by construction.

## C2-E11: proved status

leanblueprint's `Packages/blueprint.py:make_lean_data` (a postParse
callback at priority 150) computes each node's `proved` flag from
`proof = node.userdata.get('proved_by')` -- set only by the `\\proves`
command inside a `proof` environment -- via `proved =
proof.userdata.get('leanok', False)`; with no `proof`, `proved` is
hardwired to `False`. `class`/`abbreviation` environments never carry
a `\\proof` (nothing is asserted, so nothing is proved separately from
the declaration itself), and `instance` environments carry one only
rarely, so their `proved` stayed permanently `False` even when
`\\leanok`'d, and `fully_proved`'s ancestor scan (`all(n
.userdata.get('proved', False) or item_kind(n) == 'definition' for n
in ...)`) only auto-passes ancestors of kind `definition`, never
`class`/`abbreviation`/`instance` -- so every theorem/lemma depending
on a `\\leanok`'d class or instance was denied both the `proved`
background fill on that node itself and the `fully_proved` dark-green
fill on its dependents, even once fully formalized.

Doctrine (LEAD-ruled, C2-E11; extended to `instance` at C2-E14): for
definition-like kinds the statement/proof distinction collapses -- a
definition's sole obligation is to exist and elaborate; kernel
acceptance IS the discharge. `class`, `abbreviation` and `instance`
are all definition-like (a class is a structure declaration, an
instance is a `def` producing a term of one; nothing is asserted
separately from the declaration) and get `\\leanok ⇒ proved`, exactly
mirroring how `definition`-kind nodes are treated by `fully_proved`'s
own ancestor scan.

This is done by *patching the computed `proved` flag*, not by forking
`fillcolorizer`/`colorizer`/`fully_proved`'s formula: once
`node.userdata['proved']` is corrected for
`class`/`abbreviation`/`instance` nodes, leanblueprint's own default
`fillcolorizer` (`Packages/blueprint.py:267-287`) already does the
right thing unmodified -- its first `if proved: fillcolor =
colors['proved'][0]` branch fires for the class or instance node
itself (the "proof of this result is formalized" green fill, same
legend row a proved theorem gets), and `fully_proved`'s
`all(n.userdata.get('proved', ...) or ...)` scan (re-run here with the
corrected `proved` values, using the identical formula from
`make_lean_data`) now also counts leanok'd
class/abbreviation/instance ancestors, so dependent theorems/lemmas
reach `fully_proved` and get the dark-green fill from the SAME
unmodified `fillcolorizer`. `colorizer` (border color) is untouched:
`\\leanok` already gave class/abbreviation/instance nodes a green
border before this fix (the symptom was fill-only), because
`colorizer` only reads `data.get('leanok')` directly, with no
kind-based gate.

## Load order

This package is loaded via `\\usepackage{nesycatshapes}` in web.tex,
placed AFTER `\\usepackage[...]{blueprint}` so that
`document.userdata['dep_graph']` (initialized by plastexdepgraph's own
`ProcessOptions`, which `blueprint`'s `ProcessOptions` loads
transitively) already exists when this package's `ProcessOptions`
runs, and so that its `legend` key already holds plastexdepgraph's two
hardcoded shape rows (`[('Boxes', 'definitions'), ('Ellipses',
'theorems and lemmas')]`) before we overwrite them in-place.

The legend rewrite runs as a post-parse callback at priority 200 (>
leanblueprint's own `Packages/blueprint.py:make_legend`, registered at
priority 150), so it runs after leanblueprint has already `extend()`-ed
the legend list with its own color rows -- rewriting `legend[0]` and
`legend[1]` in place leaves those color rows (appended after index 1)
untouched. The `proved`/`fully_proved` patch runs as a post-parse
callback at priority 160 (> leanblueprint's `make_lean_data`, also
registered at priority 150, and plasTeX's `TeX.py` runs postParse
callbacks in ascending priority order -- confirmed at
`plasTeX/TeX.py:426`, `for order, callbacks in
sorted(self.ownerDocument.postParseCallbacks.items())`), so it always
sees `make_lean_data`'s first-pass `proved`/`can_prove`/`fully_proved`
values before correcting them.
"""

from plastexdepgraph.Packages.depgraph import item_kind

# Kinds that are definition-like for proved-status purposes: the
# declaration IS the discharge, so kernel acceptance of the declaration
# itself (\leanok) is what `proved` should read. `instance` belongs
# here since C2-E14 (in Lean an instance is a def). Kept distinct from
# `dep_graph['shapes']` on purpose -- `definition` belongs in both
# sets, and the two sets answer different questions.
_DEFINITION_LIKE_PROVED_KINDS = ('class', 'abbreviation', 'instance')


def ProcessOptions(options, document):
    dep_graph = document.userdata.setdefault('dep_graph', dict())

    # kind -> graphviz shape. `lemma` and `theorem` are absent on
    # purpose: they fall through to plastexdepgraph's own ellipse
    # default in `DepGraph.to_dot`'s `shapes.get(item_kind(node),
    # 'ellipse')`, where the two-stage border/fill colouring is
    # truthful.
    dep_graph['shapes'] = {
        'definition': 'box',
        'class': 'box',
        'abbreviation': 'box',
        'instance': 'box',
    }

    def rewrite_shape_legend() -> None:
        legend = document.userdata['dep_graph']['legend']
        legend[0] = ('Boxes', 'definitions, classes, abbreviations, instances')
        legend[1] = ('Ellipses', 'lemmas, theorems')

    document.addPostParseCallbacks(200, rewrite_shape_legend)

    def fix_definition_like_proved() -> None:
        """
        Patch `node.userdata['proved']` for definition-like kinds
        (class, abbreviation, instance) that leanblueprint's
        `make_lean_data` (priority 150) hardwired to `False` for lack
        of a `\\proof` environment, then re-run `fully_proved`'s own
        ancestor scan verbatim (same formula as
        `Packages/blueprint.py:232-233`) so the correction propagates
        to dependents. The patch only ever upgrades: an instance env
        that does carry a paired `\\leanok`'d proof keeps the `proved`
        leanblueprint already gave it, so proof-carrying and proofless
        instances end up coloured identically.
        """
        for graph in document.userdata['dep_graph'].get('graphs', {}).values():
            for node in graph.nodes:
                if item_kind(node) in _DEFINITION_LIKE_PROVED_KINDS:
                    node.userdata['proved'] = (
                        bool(node.userdata.get('leanok'))
                        or bool(node.userdata.get('proved', False)))
            for node in graph.nodes:
                node.userdata['fully_proved'] = all(
                    n.userdata.get('proved', False) or item_kind(n) == 'definition'
                    for n in graph.ancestors(node).union({node}))

    document.addPostParseCallbacks(160, fix_definition_like_proved)
