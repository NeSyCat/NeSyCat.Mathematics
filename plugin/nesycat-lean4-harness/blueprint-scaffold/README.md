# blueprint-scaffold/

Portable companions to a host repo's `blueprint/src/` leanblueprint
scaffold. Unlike the rest of this plugin (hooks, skills, agents —
deliberately host-agnostic per the top-level README's "no
NeSyCat-specific paths" contract), the files here are small, optional
plastex packages a host repo copies directly into its own
`blueprint/src/`. They fix generic `plastexdepgraph`/`leanblueprint`
defaults, not anything NeSyCat-specific, so they travel with the
plugin rather than living only in this repo's own `blueprint/src/`.

This directory is new as of C2-E9; it did not exist before that ticket
(there was no prior "blueprint scaffold twin" location in this
plugin — the plugin's hooks/skills/agents are the only things
mirrored elsewhere in this repo). Created here as the natural home
for future scaffold-level companions.

## nesycatshapes.py

Byte-identical mirror of `blueprint/src/nesycatshapes.py` (this repo's
own copy is the one actually loaded by the web build). Fixes
`plastexdepgraph`'s dependency-graph node-shape default (only
`definition` is boxed; everything else — including `class` and
`abbreviation`, which are just as definition-like — renders as an
ellipse) by boxing `class`/`abbreviation` alongside `definition` and
rewriting the shape legend's two rows to match. `instance` is left as
an ellipse deliberately: an instance environment discharges real proof
obligations, so the theorem shape is truthful there.

### Install in a host repo

1. Copy `nesycatshapes.py` into the host's `blueprint/src/`.
2. Add `\usepackage{nesycatshapes}` to `web.tex`, AFTER
   `\usepackage[...]{blueprint}` (it reads and extends
   `document.userdata['dep_graph']`, which `blueprint` initializes).
3. plasTeX's local-package resolution (`plasTeX/Context.py`'s
   `loadPythonPackage`) only searches `config['general']['packages-dirs']`
   before falling back to installed plugins/builtins, and that option
   defaults to empty — so a bare `.py` dropped into `blueprint/src/`
   is NOT found without also adding, to the host's `plastex.cfg`
   `[general]` section:
   ```
   packages-dirs=.
   ```
   (verified empirically against this repo's own venv: the bare
   drop-in silently no-ops with `WARNING: No Python version of
   nesycatshapes.sty was found`; adding `packages-dirs=.` resolves it
   correctly).
