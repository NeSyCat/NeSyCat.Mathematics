"""
nesycatshapes -- local plastex package (C2-E9): dependency-graph
node-shape fix.

plastexdepgraph's own default (`Packages/depgraph.py`, `to_dot`, read
at render time from `document.userdata['dep_graph'].get('shapes',
{'definition': 'box'})`) boxes only the `definition` environment kind
and renders every other kind -- including NeSyCat's `class` and
`abbreviation` environments -- as an ellipse, the shape depgraph's own
hardcoded legend (set at its own package-load time, in the same file)
labels "theorems and lemmas". That is wrong for `class`/`abbreviation`:
both are definition-like (no proof obligations; the anatomy law in
FORMALIZE.md gives only `instance`-kind environments a proof part), so
they belong with `definition` as boxes.

`instance` DELIBERATELY stays an ellipse: an instance environment
asserts "this carrier satisfies the class's laws", and its Lean side
discharges real proof obligations, so the theorem shape is truthful
there, not a defect to fix.

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
untouched.
"""


def ProcessOptions(options, document):
    dep_graph = document.userdata.setdefault('dep_graph', dict())

    # kind -> graphviz shape. `instance`, `lemma`, `theorem` are absent
    # on purpose: they fall through to plastexdepgraph's own ellipse
    # default in `DepGraph.to_dot`'s `shapes.get(item_kind(node),
    # 'ellipse')`.
    dep_graph['shapes'] = {
        'definition': 'box',
        'class': 'box',
        'abbreviation': 'box',
    }

    def rewrite_shape_legend() -> None:
        legend = document.userdata['dep_graph']['legend']
        legend[0] = ('Boxes', 'definitions, classes, abbreviations')
        legend[1] = ('Ellipses', 'lemmas, theorems, instances')

    document.addPostParseCallbacks(200, rewrite_shape_legend)
