# FORMALIZE.md — Rules of Work

This file is the authoritative work-instruction document for any agent
session doing formalization work in this repository. It is the Lean 4
analog of the rules-of-work file described in Urban's "130k Lines of
Formal Topology in Two Weeks" (arXiv:2601.03298): a fast checker, a
sorry/admit tracker, a per-section progress ledger, and git as the
never-lose-work backup system. Follow it exactly. Work as long as
possible without stopping to ask questions.

## Scope rail (STRICT)

- You may create/edit files only under `NeSyCat/` (the library; topic
  folders as needed) and may edit
  `PROGRESS.md` and `blueprint/src/**`.
- `NeSyCat.lean` may ONLY be touched to add new
  `import NeSyCat.<NewFile>` lines when you create a new module.
- NEVER edit: `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`,
  `scripts/`, `references/`, `.github/`, `.foreman/`,
  `.gitignore`.
- NEVER run `lake update`.

## Never lose work

- Never run `git reset --hard`, `git revert`, `git checkout -- <file>`,
  or delete a compiling proof or definition.
- If you restructure a file, salvage every compiling theorem and
  definition — move it, don't drop it.
- Any commit that DECREASES the total line count of `NeSyCat/`
  must explicitly justify the decrease in its commit message. Cite
  Urban's rule 5: an agent once silently threw away 9k lines of working
  formalization. Do not repeat that mistake.

## Checker discipline

- After every meaningful edit, run `scripts/check.sh` (whole project)
  or `scripts/check.sh NeSyCat.Monad.<Module>` (one module, faster).
- Success = exit code 0 and no `error:` lines in the output (the script
  prints `CHECK: GREEN` on success, `CHECK: RED (exit <code>)` on
  failure).
- Commit small and often. Each commit message should have:
  1. a one-line summary,
  2. a short description of what changed,
  3. the sorry-count delta (before/after, from `scripts/sorry-report.sh`).
- Include the `Co-Authored-By:` footer per session convention if one is
  in use.
- When `blueprint/src/**` or any `\lean`/`\leanok` mark changes, run
  `scripts/blueprint.sh` and confirm it prints `CORRESPONDENCE: OK`
  followed by `BLUEPRINT: GREEN` before committing (`scripts/check.sh`
  remains the Lean commit gate). `CORRESPONDENCE: OK` is the
  blueprint<->Lean correspondence gate (structural editorial laws +
  Lean-kind assertions per `\lean{}` name) — a red CORRESPONDENCE
  section blocks exactly like a red decl-check.
- **Blueprint-sync commit law.** A commit that touches a `NeSyCat/**.lean`
  declaration cited by a blueprint `\lean{}` mark must either (1) stage
  the corresponding `blueprint/src/content.tex` tightening alongside it
  (the normal case — see the post-`\leanok` work-loop step below), or
  (2) carry a commit-message line starting `Blueprint-sync: <reason>`
  documenting a justified skip (e.g. a whitespace/comment-only edit or a
  golf pass with no statement change) — the same justified-skip
  convention as the never-lose-work line-count rule above. This is
  mechanically enforced: `scripts/git-hooks/commit-msg`, installed at
  `.git/hooks/commit-msg`, rejects a commit that satisfies neither.
- Every `.lean` file begins with the standard copyright header (copy it
  from `NeSyCat/Monad/LatticeSemiring.lean`; Apache 2.0, see `LICENSE`);
  keep the style/header linter silent.

## sorry policy

`sorry` is legitimate scaffolding. It is allowed in unfinished
branches, ALWAYS with an adjacent `-- TODO:` comment describing what
remains to be proved. Burn sorries down continuously — run
`scripts/sorry-report.sh` before and after each work unit and watch the
total trend downward over time.

HARD BANS (no exceptions):

- `axiom` declarations of any kind.
- Changing a target statement to make it weaker or trivial so it is
  easier to prove.
- `native_decide`.
- Using `set_option` to suppress ERRORS. (Suppressing purely stylistic
  linter warnings via `set_option linter.style... false` is fine;
  suppressing real errors is not.)
- Deleting a hard item instead of finishing it. Leave it as a `sorry`
  with notes instead.

## Faithfulness

**Absolutely lean.** Once an item's Lean form is settled (post-`\leanok`),
the blueprint's own prose for that item is tightened to match it: Lean's
economy and its natural proof language are the standard the informal
text is pulled toward, not the other way around. A blueprint item is
never left more verbose, more hedged, or less precise than the Lean
declaration and proof it now cites — see the post-`\leanok` work-loop
step below.

- Every formal item gets a doc comment of the form:
  `/-- Blueprint <tex-label> (<name>): <informal statement>. -/`, where
  `<tex-label>` is the blueprint `\label` key for that item in
  `blueprint/src/content.tex`.
- Faithfulness has two legs: (1) Lean statement ↔ blueprint statement —
  exact, library items are stated per the blueprint (the canonical
  informal document); (2) blueprint item ↔ its cited source — the
  blueprint is the canonical, authoritative document in its own right,
  not a restatement graded against some other standing target.
  Bibliographic citations (e.g. "[NeSy26, App. A]") are provenance
  credits, not a conformity requirement, so the check on a citation is
  ACCURACY: does the cited source really contain what is credited to it
  — not whether the blueprint's own statement matches the source's
  concrete case. Items are freely stated at their natural mathematical
  generality; a cited source's narrower case then appears as an
  instance/corollary, noted in-item in the library's own voice (no
  "divergence declared relative to the source" framing). When library
  work generalizes or corrects a claim that a live paper (e.g. NeSy26
  itself) still states more narrowly or differently, aligning that
  paper's text is part of closing the item, not optional follow-up —
  such paper edits are user-approved, never made unilaterally. Pinned
  texts used for an authoring or verification pass live at recorded git
  refs (ledger + blueprint preamble), not as standing copies.
- Before adding ANY definition or theorem:
  1. `grep` `NeSyCat/` for duplicates of the same item.
  2. Search Mathlib for existing versions (`exact?`, `apply?`, `rw?`,
     or https://leansearch.net).
- Mathlib may be used freely as BACKGROUND machinery (e.g. `Category`,
  `Functor`, `NatTrans` from `Mathlib.CategoryTheory`). But a library
  item from the canonical library document `blueprint/src/content.tex`
  (provenance: bibliographic citations, e.g. `[NeSy26, App. A]`, with
  pinned texts recorded at their git refs) must be STATED in the plain
  `NeSyCat` namespace and given a REAL proof. A
  bare one-line `exact <Mathlib lemma>` citation of the identical
  statement defeats the campaign's purpose — construct the proof, even
  if it uses Mathlib lemmas as steps.

## Blueprint structural laws

- **Final environment inventory (C2-E4a full Lean-kind sync, USER
  DECREE 2026-08-09, supersedes every earlier version of this list).**
  The blueprint's environments are EXACTLY Lean's own declaration
  kinds — `def`, `class`, `instance`, `abbrev`, `lemma`, `theorem` (+
  `Structure`/`Inductive` added lazily when first needed; `axiom`
  excluded forever by the library's axiom-freedom law) — rendered as
  the LaTeX env names `definition`/`class`/`instance`/`abbreviation`/
  `lemma`/`theorem`/`proof`, heads printed as the WRITTEN-OUT English
  words ("Definition 3", "Class 5", "Instance 2", "Abbreviation 1",
  "Lemma 7", "Theorem 4"), each on its OWN independent counter
  (restarting at 1, incrementing only within its own kind — not a
  shared counter, not per-section). `remark`/`proposition`/
  `corollary`/`example`/`conjecture` are ALL abolished — nothing else
  exists. Retriage: a former proposition/corollary → `lemma`
  (cited-as-infrastructure) or `theorem` (chapter-payoff); a former
  example → an `instance` env (if it witnesses a class) or dissolves
  into plain narrative prose (tables/diagrams allowed, no env, no
  label); a former conjecture → a `theorem` env whose proof body is
  the open marker (below). Re-kinding rule: every item's kind is fixed
  by its PRINCIPAL Lean declaration — a `class`-kind declaration lives
  in `class`; an `instance`-kind declaration lives in `instance`;
  everything else with new mathematical content lives in `definition`
  (internal env name `definition`, no TeX clash with `\def`, head
  "Definition"); a reducible-def name-introduction lives in
  `abbreviation`. `scripts/blueprint.sh`'s CORRESPONDENCE STRUCTURE
  check rejects any surviving dead-kind environment (hard, gate-red);
  the lint hooks advise on one the moment it is typed.
- **The open-theorem convention.** A theorem with no known proof is a
  `theorem` env like any other (never its own environment kind, per
  the conjecture abolition above), paired with a `proof` env whose
  ENTIRE body is the single sentence "Open." — no ad-hoc "-- OPEN"/
  "Status: open" phrasing anywhere, and it never carries `\leanok` on
  either the statement or the proof side (there is nothing formalized
  to mark). `scripts/blueprint.sh` enforces this structurally: an
  "Open."-body proof carrying `\leanok` is a hard violation, and so is
  its paired statement carrying `\leanok`. Current instance:
  `thm:chain-bound` ("How wrong can it get").
- **The bijection law (C2-E4a/A1, USER DECREE 2026-08-09).** The
  LaTeX↔Lean correspondence is one-to-one: every environment that
  carries a `\lean{}` mark at all carries EXACTLY ONE name, its
  principal declaration — never a multi-name list. The map is
  injective envs→decls, NOT surjective: a Lean declaration that is a
  technical companion of the cited principal (a `simp`/`_apply`
  unfolding lemma, a round-trip half of an equivalence, a unit-law or
  left/right-monotonicity twin, a raw/corollary doubling) simply
  becomes an UNMARKED internal — it still exists in Lean, still
  compiles under `scripts/check.sh`, it just is not blueprint-cited.
  Deciding split vs. companion for a formerly multi-name env: if the
  extra names are PEER CLAIMS the statement genuinely bundles (e.g.
  distinct numbered parts, each with its own proof), split the env
  into one per claim, distributing the statement's clauses
  accordingly (purity + anatomy laws make the split well-defined); if
  the extras are companions of one claim, keep the single principal
  name and drop the rest. Bias: fewer envs, more unmarked companions —
  split only genuine peer bundles. `scripts/blueprint.sh` enforces
  this as a hard structural check (a `\lean{}` list of ≥2 names is a
  gate violation, checked before the kind-check step, which then
  checks THAT one name's kind exactly, not "at least one of several").
- **The internal-tag convention (C2-E4a/A2).** Every public Lean
  declaration deliberately left uncited by the bijection law above (a
  demoted companion, or any other pre-existing library-internal
  helper) carries a line comment `-- blueprint: internal (<short
  reason>)` on, or immediately above, its declaration — `private`
  declarations need no tag, since they cannot be cited by anything
  outside their own file regardless. This is what lets a completeness
  census tell "deliberately uncited plumbing" apart from "real
  mathematics nobody wrote an env for": every top-level declaration in
  the NeSyCat namespace is either (a) cited by exactly one env, or (b)
  carries this tag — nothing may be neither.
  `scripts/blueprint.sh`'s CENSUS subsection enforces this over a
  fixed, disclosed file list (`CENSUS_FILES`, currently the
  Truth-value-structures and semiring-monad chapters; extending it to
  the rest of the library, file by file, is each new chapter's own
  ticket's job) via a pragmatic text-based name matcher (not yet a
  full `lake env lean` environment fold) — an unclassified declaration
  is a hard gate violation. Audit fruit — a genuinely uncited,
  genuinely real piece of mathematics the census turns up (not
  plumbing) — gets its own env of the right kind, statement mirroring
  the declaration, `\leanok` statement-side, proof env where
  theorem-kind (example: `def:psum`, the probabilistic sum, found this
  way and given a `definition` env).
- **The calibrated reuse/fold principle (C2-E4c, USER DECREE
  2026-08-09).** A result folds into its consumer as a PROOF STEP — in
  Lean AND LaTeX together, the same bijection-preserving move at both
  layers at once (the Lean declaration is deleted and its proof is
  absorbed inline into the consumer's `proof` env; the LaTeX `lemma`
  env is deleted and its own `proof` env's text is absorbed into the
  consumer's `proof` env) — only when BOTH hold: (a) it is TRIVIAL (a
  one-liner that just unfolds a definition against a couple of
  standard lemmas) AND (b) it is SINGLE-PURPOSE (exists only to feed
  one theorem, zero other call sites anywhere in the library). A
  result with independent mathematical interest ("a nice result")
  KEEPS its lemma-hood regardless of current use count — future reuse
  cannot be known in advance, and quotability is itself a reason for a
  result to exist as its own named declaration (USER calibration
  2026-08-09: "don't make it too strict" — this is deliberately NOT a
  blanket "fold every zero-use lemma" rule). Worked example
  (`NeSyCat.bind_ret`, C2-E4c): `ret_bind` and `bind_assoc` each have
  5+/4+ further call sites in `NeSyCat/Truth/*.lean`'s truth-space
  machinery, so both STAY independent lemmas; `bind_ret` has zero uses
  anywhere outside its own statement, and its proof is a one-line
  `Finsupp` unfold — it FOLDS into `semiring_monad_laws`, a single
  bundled theorem whose proof cites `ret_bind`/`bind_assoc` verbatim
  and proves the (former `bind_ret`) right-unit law inline as one
  conjunct; `content.tex`'s `lem:bind-right-unit` env and its `proof`
  env are deleted, their content absorbed into
  `thm:semiring-monad-laws`'s own (now `\lean`/`\leanok`-marked)
  statement and proof envs. Enforcement: the census report (below,
  `scripts/blueprint.sh`) gains an ADVISORY line listing cited
  theorem/lemma-kind declarations with zero further code uses anywhere
  in `NeSyCat/` (mechanical: a grep-based use count, excluding the
  declaration's own signature line) — a surfacing tool, NEVER an
  automatic mandate. Every fold is individually adjudicated by
  LEAD/user against the two criteria above; a name appearing on the
  advisory list is a folding CANDIDATE for disclosure and discussion,
  not a violation, and a fresh lemma with zero uses so far may simply
  be awaiting its first consumer. Verifier checklists inherit this: a
  blind verifier MUST NOT flag an un-folded zero-use lemma as a
  finding on its own; it may only flag a fold that was performed
  without satisfying both criteria, or a criteria-satisfying case the
  ticket disclosed but silently declined to fold.
- **The three-shape witness doctrine.** A worked instance dissolved
  out of the old `example` kind (per the retriage rule above) takes
  one of three shapes, all via NAMED Lean declarations (never Lean's
  anonymous `example` keyword, which cannot be cited or kind-checked):
  *inhabitation* (an `instance`/`def`-kind witness that a concrete
  carrier satisfies a class — cite the `instance`); *separation* (a
  negative theorem with an explicit witness, e.g. a counterexample —
  cite the `theorem`); *computation* (an equation lemma evaluating a
  construction at concrete data — cite the `theorem`). Whichever shape
  applies, the env is `instance` only for the inhabitation case;
  separation and computation stay plain narrative prose (with a
  `\lean{}`-marked `theorem`/`lemma` if the fact is itself citable
  infrastructure, or no env at all if it is purely illustrative).
- **Remarks are abolished.** The document reads as a STORY: formal
  environments (`definition`, `class`, `instance`, `abbreviation`,
  `lemma`/`theorem` + `proof`) floating in continuous narrative prose.
  Anything with no Lean counterpart — provenance credits, notational
  conventions, dictionary glosses, contrasts, forward pointers, worked
  narrative examples — is plain untagged text immediately before or
  after the formal environment it concerns, never its own
  `\begin{remark}`/`\begin{example}`. Condensation of this discourse
  prose is licensed (shorter is better) as long as no mathematical
  claim is dropped or altered and provenance is never silently deleted
  — it moves. Honesty records (errata, scope/faithfulness disclosures)
  MUST survive as prose, condensed but never deleted.
  `\uses`/`\lean`/`\label`/`\leanok` always stay inside the environment
  they mark (leanblueprint needs `\uses` inside the env for the
  dependency graph).
- **Total Lean-mirror purity.** Every environment with a Lean
  counterpart — `lemma`/`theorem` (statement), `definition`, `class`,
  `instance`, `abbreviation`, and `proof` — contains ONLY the
  mathematical content its cited Lean declaration/proof contains:
  structure fields, laws, hypotheses, conclusion, carrier, or (for
  `proof`) the informal mirror of the Lean proof's own steps.
  Provenance tags (bracketed source citations), dictionary glosses,
  contrast commentary ("unlike a ... no distributivity is assumed"),
  and forward/backward pointers are OUT — they move to plain prose
  immediately before or after the env, condensed and deduped across a
  run of items sharing the same citation where that reads better as a
  story, never dropped. An open theorem gets the same commentary
  treatment for uniformity, governed otherwise by statement-
  minimality. **Pinned exemption:** `def:domain-signature-notation`
  ("Writing convention for typed symbols", Domain layer) is the one
  `definition` environment with no Lean counterpart, by explicit user
  decision predating and surviving this law for this specific item —
  the sweep, the lint advisory, and the kind-check gate all exempt it
  by label, and it is never dissolved into prose. Enforced
  advisory-side by the lint hooks' commentary/provenance marker scan
  (bracketed `[NeSy26`/`[Girard`/... tags, or phrases like "Distilled
  from", "unlike a", "transported along", "see Remark", "the source");
  the hard structural gate lives in `scripts/blueprint.sh`'s
  CORRESPONDENCE section (env/kind agreement, the bijection law, and
  the dead-kind checks above).
- **Statement/proof anatomy.** A `lemma`/`theorem` statement env
  contains exactly what the Lean statement contains: for an
  existential or negative claim ("does not distribute", "is not
  idempotent"), that is the `∃`/`¬`-form itself, with NO witness
  values and no worked computation. Witness choices, numeric
  instantiations, and the arithmetic that verifies them belong in the
  `proof` env, matching the Lean proof's own `refine ⟨...⟩`/`norm_num`
  shape. "Concretely, at $p=q=r=\tfrac12$, ..." inside a statement is
  proof content in the wrong box — it always moves down into the
  `\begin{proof}`.
- **Definition atomicity.** Every `definition`/`class` environment
  introduces exactly one named structure. A family of variant
  refinements (commutative / bounded / bounded-commutative;
  C-variants of a class) each get their own env, `\uses`-linked to the
  atom(s) they refine — never bundled into one env with the base
  structure.
- **No worked instances in definitions.** A `definition`/`class`
  environment states the structure only: no worked instances,
  running-instance itemizations, or anti-examples. That content moves
  to an `instance` env (per the three-shape witness doctrine above) or
  plain prose placed after the definition(s)/class(es) it
  instantiates, `\uses`-linked back to them.
- **The book register law (C2-E5, USER DECREE 2026-08-09).** The
  rendered blueprint reads like a book: simple, direct language, no
  jargon, no meta-history, no provenance apparatus on the page, no
  dashes. Scholarly bookkeeping (bracketed source citations, the
  erratum account, the sources-and-provenance paragraph with its git
  refs and sha256 pins, ticket/decree references, and any other
  self-referential or process passage) lives in NON-RENDERED homes:
  LaTeX `%` comments at the original location, plus `PROGRESS.md` and
  `.foreman/ledger.md`. It is moved, never deleted — a moved block is
  preserved verbatim in its comment. The correspondence between
  environment kind and Lean declaration kind, and every other
  structural law in this document, is enforced by the gate regardless
  of whether the rendered page describes it; a page-facing summary may
  stay in plain book language, without tool names or script paths, when
  it genuinely helps a reader understand the boxes.
  Language sweep, rendered text only: no em/en dashes (LaTeX `---`/`--`
  or literal —/–) — restructure with commas, colons, periods, or
  parentheses (hyphens inside compound words stay; a minus sign inside
  math is not a dash); plain words over apparatus-speak (mathematical
  terminology of the subject itself, e.g. semiring, monad, lattice, is
  never jargon); no AI-flavored filler ("It is worth noting",
  "Crucially", "Note that" chains, "serves as", "plays a crucial role",
  "underscores", "highlights", "In essence"); no aphorism/chiasmus
  metaphors ("If X is the contract, Y is its fulfillment" — state what
  a thing IS); no grand unearned framing ("provides the right language
  to resolve this uniformly"); no overclaims (prose exactly as strong
  as what is proven — the Lean-mirror principle applied to language:
  state the `∃` you proved, not the `∀` you would like); no performative
  paragraphs (idea-dropping that teaches nothing — delete it if the
  story survives without it); one authorial voice throughout (no
  contradictory stances between sections). Mathematics inside an env is
  untouched except where a dash or a banned phrase sits in its own
  prose connective tissue; no mathematical clause may change meaning.
  Honesty records (errata, scope/faithfulness disclosures) still MUST
  survive as prose — the register law changes how apparatus is written,
  never whether a genuine mathematical caveat is disclosed.
  Enforced by `lint-blueprint.py` (both copies): advisories on
  rendered-text (comment-stripped) occurrences of bracket-citation
  patterns, em/en dashes outside math (a pragmatic heuristic — it does
  not track math-mode boundaries, since the final document contains
  zero such occurrences anywhere at all), history markers ("Erratum",
  "corrected upstream", "revisions up to", "git ref", "sha256",
  "authored and verified"), and the filler-phrase list above. A blind
  verifier reads a rendered page sample as a READER and flags apparatus
  leakage or register violations on its own initiative. Narrative
  mathematical claims must be env-backed or explicitly Open, never
  merely asserted in prose (C2-E4b, USER-CAUGHT violation): a sentence
  making a real mathematical claim that Definition/Lemma/Theorem/proof
  envs do not already cover gets promoted to its own env (with a real
  proof, or the open-theorem convention's "Open." marker), not left as
  an unmarked observation.
- **The plain-language density law (C2-E7, USER DECREE 2026-08-09).**
  One claim per sentence. A sentence that carries two facts, a
  hypothetical, or a proof-sketch riding along inside a parenthetical
  or a subordinate clause gets split: state each fact on its own line,
  in flat declaratives (has/is/contains/do), not stacked into one
  compound sentence. This is a companion to the book register law
  above: that law bans apparatus and filler; this law bans *density* —
  writing that is grammatical and on-topic but crams more than a
  reader can take in one sentence. Five register-smell classes, all
  user-caught against this document, define the bar (full catalogue:
  memory `nesycat-writing-style.md` items 9-13):
  1. **Compression-stacking** — several claims, a noun-pile subject, or
     a mid-sentence parenthetical proof-sketch, packed into one
     sentence.
  2. **Altitude / nominalization** — role-speak and abstract nouns
     standing in for a plain subject-verb-object claim ("the order
     obstruction vanishes" for "the order has no top, so the argument
     fails").
  3. **Significance pronouncement** — antithesis flourishes and
     profundity clinchers ("this is structural, not accidental") that
     announce importance instead of stating a fact.
  4. **Program-shaped prose** — inline guards, condition-stacking, and
     case-texture ("in the general (possibly noncommutative) case
     ... absent commutativity of ...") that reads like a code
     comment, not a sentence.
  5. **Essay voice** — narrated transitions and self-referential
     scaffolding ("taken up together with the completion instances")
     standing in for a plain forward pointer.
  The five classes are diagnostics for catching a bad sentence, not an
  exhaustive checklist: the actual bar is flat declarative prose, one
  fact per sentence, matching the voice of the library's own reference
  source (*NeSyCat Theory v2*, `new.tex` lines 1-396). Mathematics
  inside an env is untouched except where its own prose connective
  tissue carries one of these patterns; no mathematical clause may
  change meaning. Enforced by `lint-blueprint.py` (both copies):
  advisories on a rendered-prose (comment-stripped, math-mode
  excluded) sentence over 55 words, and on a rendered-prose sentence
  with more than two real parenthetical groups (citation/cross-
  reference parens such as `(Class~\ref{...})` and bare enumeration
  markers such as `(i)` excluded — both crude, honest proxies, tuned
  for zero false positives against the swept document, not exhaustive
  detectors). A blind verifier reads a short rendered-page sample as a
  READER and judges density on that sample directly, the same way it
  already judges register.
- **The structure-mirror law (C2-E6, USER DECREE 2026-08-09).** The
  blueprint's `\section`/`\subsection` tree and the `NeSyCat/` folder
  tree mirror each other exactly — computed and self-updating, never
  hand-maintained. Every `\section`/`\subsection` in `content.tex`
  carries a trailing `% lean-dir: <FolderName>` comment naming the
  `NeSyCat/<FolderName>/` folder it lives in; the Introduction alone
  may tag `% lean-dir: -` (no Lean home), the one permitted opt-out.
  Folders are named after blueprint structure, not blueprint numbers
  (Lean identifiers ban a leading digit, and a reserved future layer
  would renumber a later one) — the section number lives in the
  folder's own root module's module-doc header instead. Every folder
  under `NeSyCat/` — including one with no formalized content yet —
  carries exactly one root module file `<FolderName>.lean` (copyright
  header plus a module-doc citing its blueprint section number and
  title; an empty folder's says "No Lean content yet"), imported by
  `NeSyCat.lean` so `scripts/check.sh` compiles the whole mirror, empty
  folders included. Three violation shapes are possible: an untagged
  section, a tag naming a folder that does not exist, and a folder with
  no tag naming it (the allowlist: root `Notation.lean`/`Basic.lean`
  and the root module files themselves, none of which is a folder).
  Enforced twice, identically, both pure text-plus-filesystem checks
  with no Lean elaboration: `scripts/blueprint.sh`'s CORRESPONDENCE
  `structure-mirror` subsection (prints the derived tree), and
  `scripts/git-hooks/commit-msg` (+ its `.git/hooks/` install and the
  plugin's generic twin) as an unconditional commit-time gate, with no
  `Blueprint-sync:` escape hatch — a mismatched tree may never even be
  committed. `lint-blueprint.py` (both copies) additionally advises,
  non-blocking, the instant an edit leaves a section untagged.

- **Connective flow and visible attribution (C2-E8, USER DECREE
  2026-08-09).** Two register laws, calibrated against the
  ⊗-commutativity passage (the E7 flat-prose master specimen), that
  revise the book-register (C2-E5) and density (C2-E7) laws above
  rather than reopen them.
  1. **Connective flow.** Short precise sentences stay; the
     one-claim-per-sentence law and the >55-word advisory are
     unchanged. What is missing when consecutive sentences all open
     with "The"/"This"/"It" — a monotone drumbeat, not a story — is
     connective tissue: since, therefore, hence, because of that, for,
     but, yet, however, likewise, so. Joining two short sentences with
     such a connective is welcome, and often better than leaving them
     apart, PROVIDED the connective reflects a genuine inferential or
     contrastive relation the two clauses actually have — never a
     decorative stitch between two merely-adjacent facts (a plain
     enumeration, e.g. the library's five layers, stays five separate
     facts; break a repetitive run of openers by reopening with a
     different subject instead of inventing a relation that is not
     there). A joined sentence carries its two claims visibly, one per
     clause; a connective JOINS, it does not stack.
  2. **Visible attribution.** If a result comes from a source, the
     page says so. The book register law's ban on apparatus STAYS:
     bracketed tag walls, git refs, sha256 pins, and errata history
     remain `%` comments and never render. What returns is book-style
     prose attribution for genuinely external RESULTS — "a result of
     `\citet{...}`", "due to `\citet{...}`", "linear logic's four
     linear distributions `\citep{...}`" — paired with a rendered
     bibliography (`\citep`/`\citet`, natbib author-year style,
     matching the user's own papers' citation convention; a
     hand-written `thebibliography` with natbib-format
     `\bibitem[Author(Year)]{key}` optional arguments, camelCase
     authorTitleYear keys, no BibTeX/biber program run — see
     content.tex's own Bibliography section comment for the print/web
     toolchain split, including the plasTeX fallback). A blanket,
     whole-section "this material is due to [our own precursor
     paper]" credit is NOT the same thing as crediting a specific
     result to an external author: the former is document-history
     (source-priority bookkeeping, `%` comment, PROGRESS/ledger; see
     the source-priority rule elsewhere in this file), the latter is
     what this law makes visible. When in doubt which a `%` block is,
     classify conservatively as the former and disclose the
     uncertainty rather than invent an attribution; every rendered
     attribution must name a source its adjacent `%` comment (or a
     vendored paper under `references/`) actually substantiates — a
     concrete external-system correspondence (e.g. an evaluator
     implementing the same semirings this library defines) may earn
     its own short connection sentence the same way, but ONLY after
     checking it against the vendored source directly, never invented.
     Enforced by `lint-blueprint.py` (both copies): a new advisory on
     4+ consecutive rendered-prose sentences, in one paragraph,
     opening with "The"/"This"/"It" (the exact three words Law 1
     itself names — tuned narrower than a first "The/This/That/It/We"
     draft specifically so it does not false-positive against the
     ⊗-commutativity specimen this law calibrates against; disclosed
     at `FLOW_OPENER_RE`'s definition). A blind verifier reads a page
     sample as a READER for flow (does it march?), spot-checks a
     handful of `%` citation blocks for correct classification, and
     confirms every prose attribution names a real source its
     adjacent `%` comment substantiates.

## Work strategy

- Prioritize named definitions/theorems/constructions over exercises;
  exercises come second.
- A partial proof with `sorry` branches beats abandoning the item
  entirely.
- Don't endlessly hunt for easy wins, and don't get stuck more than 2
  hours on a single item — leave a `sorry` with notes explaining what
  you tried and move on to the next item.

## Progress ledger

Keep `PROGRESS.md` current. One status line per section, using exactly
these six statuses:

`not-started -> stubs -> stated -> partial -> proved -> complete(+exercises)`

## Resume protocol (start of EVERY session)

Before editing anything:

1. Read `FORMALIZE.md` (this file) in full.
2. Read `PROGRESS.md` to see current status per section.
3. Read `blueprint/src/content.tex` for per-item status (`\lean`/
   `\leanok` marks).
4. Run `scripts/sorry-report.sh` to see the current sorry/violation
   count.
5. Run `git log --oneline -20` to see recent history.

Only after all five steps should you start editing.

## Work loop

1. Pick the highest-priority unfinished item per `PROGRESS.md`.
2. Implement it in the relevant `NeSyCat/` module (topic folders as
   needed; the blueprint item's `\label` names the target).
3. Run `scripts/check.sh` (module-scoped, then full project before
   committing).
4. Once the item is `\leanok` (fully proved, no `sorry`): tighten the
   blueprint text against the formalized form — the "absolutely lean"
   motto above — trimming hedges, matching the Lean statement's exact
   hypotheses/conclusion shape, and preferring the proof's own natural
   argument over a looser gloss written before the proof existed. Run
   `scripts/blueprint.sh` and confirm `CORRESPONDENCE: OK`.
5. Commit (small, with the message format above; stage the tightened
   `blueprint/src/content.tex` alongside the Lean change, or add a
   `Blueprint-sync:` line if step 4 found nothing to tighten — see the
   Blueprint-sync commit law above).
6. Update `PROGRESS.md`.
7. Repeat. Work as long as possible without stopping to ask questions.

## Tooling

Two tool layers are available. Neither replaces this file; both serve
it.

- **lean-lsp-mcp** (project-scoped MCP, tools prefixed `lean_*`).
  During proof work, prefer `lean_goal` (goal state at a position) and
  `lean_diagnostic_messages` over full rebuilds — they're cheap,
  incremental, and don't wait on `lake build`. Use `lean_local_search` /
  LeanSearch / Loogle for lemma discovery before writing a proof from
  scratch (faithfulness rule still applies). `scripts/check.sh` remains
  the ONLY commit gate — MCP diagnostics are a fast inner-loop signal,
  never a substitute for a green full check before committing.

- **lean4 plugin** (user-scope, `cameronfreer/lean4-skills`). Per-item
  inner loop may use `/lean4:prove`-style cycles for the goal-state
  grind on a single item. HARD RULE — the disprove guard: if an item
  resists two serious proof attempts, run a `/lean4:disprove`-style
  counterexample search on the STATEMENT before grinding further. If a
  counterexample surfaces, the formalization is unfaithful — re-derive
  from the blueprint item and its cited source, fix it, and note the
  correction in the commit message. Axiom audit
  before marking any section `proved`/`complete`: only `propext`,
  `Classical.choice`,
  `Quot.sound` are acceptable (matches the no-`axiom` hard ban above).
  Optional `/lean4:golf` AFTER a proof is green and committed — never
  before committing (never-lose-work).

- **Precedence.** On any conflict between this file and a skill/tool
  suggestion, FORMALIZE.md wins: the scope rail, the sorry policy, and
  the commit law above are not negotiable inputs to a tool's workflow.

- **Local reference texts.** The four canonical Lean books are
  vendored at `references/lean-docs/` (`fp-lean`,
  `theorem_proving_in_lean4`, `mathematics_in_lean`,
  `reference-manual`). Consult them locally before reaching for web
  docs for Lean/Mathlib tooling questions. They are TOOLING
  references only, never citable as mathematical sources — the
  source-priority rule (blueprint mathematical content comes from the
  library's own cited sources, e.g. NeSyCat Theory v2, never from
  these Lean docs) is unchanged.
