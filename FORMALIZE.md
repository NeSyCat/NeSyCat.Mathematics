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
  `.gitignore`, `CLAUDE.md`, `.github/`. These are the build pin, the
  dependency lock, and the session's own configuration: nothing a
  formalization ticket does legitimately touches them, and
  `.claude/hooks/guard-scope.py` enforces exactly this list (deny in
  grind mode, ask otherwise).
- NEVER edit `.foreman/**` EXCEPT `.foreman/scratch/`, where a worker
  writes its own report and bulk artifacts. The rest is the
  orchestrator's ledger, and this rule is the only thing guarding it:
  the hook deliberately does not, since prompting on routine ledger
  bookkeeping was pure noise (2026-08-07).
- TICKET-SCOPED, not forbidden: `FORMALIZE.md`, `scripts/`,
  `references/`, and `.claude/`. These were removed from hard protection
  on 2026-08-09 (user decision after the E8 law-patch prompt; recorded
  in `.claude/hooks/guard-scope.py`, whose `protected_prefixes` no
  longer lists them). The harness itself needs them editable: gate work
  edits `scripts/blueprint.sh`, law patches edit this file, and a paper
  pin lands under `references/`. Edit them only when your ticket's write
  set names them, and never to weaken a gate you are failing.
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

**REFUTABILITY OF LAW FIELDS.** A law field of a structure or class must
be *falsifiable*: some instance must be able to fail it. A field whose two
sides are definitionally equal states nothing, and no gate here would
notice, because every other check in this repo asks whether a PROOF is
honest and none asks whether a STATEMENT says anything. A non-trivial
proof of a vacuous statement passes all of them. This is not hypothetical:
`def:cd-category`'s two tensor compatibilities elaborated to reflexivity
from the day they were written, passed every gate, and passed a blind
verification that explicitly confirmed their consumer "genuinely
discharges" them, checking that the proof did work and never asking
whether the goal said anything. `scripts/blueprint.sh`'s vacuity gate now
telescopes every `Eq`-shaped law field under the `NeSyCat` prefix and goes
RED if its two sides are defeq. When writing a law field, check it by hand
too: if `rfl` closes it, it is not a law.

**DO-SUGAR BAN.** `MS S` is registered against Lean's `Monad` and
`LawfulMonad` classes (`instMonadMS`/`instLawfulMonadMS`, over the
library's own `Ret`/`bind`), so do-notation is writable — but only its
faithful fragment corresponds to the hand-proved semantics: `←`,
`let :=`, nested actions, and a final `pure`. Lean's EXTENDED sugar does
not, and must not appear in a formal statement or proof about `MS S`:
`let mut` and `for … in` desugar through `ForIn`/state-passing
machinery, and an early `return` through an `ExceptT`-shaped short
circuit, none of which `MS S` provides. Writing them would silently
change what is being proved. `.claude/hooks/lint-lean.py` flags all
three, advisory rather than blocking — the same patterns are legitimate
Lean outside `MS S` code, and the hook cannot see do-block context, so
the judgement stays with the author.

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
  its paired statement carrying `\leanok`. The convention currently has
  no live instance: its founding case, `thm:chain-bound` ("How wrong
  can it get"), was proved at C3-CB (2026-08-10), equality clause
  included.
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
  minimality. The former pinned exemption
  (`def:domain-signature-notation`) was retired at C3-B2: its writing
  convention is formalized as a display function
  (`DomSignature.TypedSymbol.display`), and no definition environment
  lacks a Lean counterpart. Enforced
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

- **The proof-substance law (C3-E12, USER DECREE 2026-08-10).** A
  rendered proof mirrors the FORMAL proof's skeleton, not a narration
  of it. The user's own words, calibrating this law: "this proof and
  other proofs use way too much natural language just vaguely
  describing the proof. why not use calculations and equations and
  logical structuring? that should be more enforced especially for
  the important theorems; for small lemmas it is not so important."
  1. **Theorem envs** (and `lemma` envs whose Lean proof exceeds ~40
     lines): the proof shows the actual mathematics — displayed
     equation/inequality chains (`align*`/`gather*`/`\[...\]`) for
     calculations, explicit enumerated case analyses where the Lean
     proof case-splits, the induction structure named with its base
     case and step shown as displays, each display traceable to a
     named Lean lemma (a `%` comment where the correspondence is not
     obvious from the surrounding prose). Connective prose glues the
     steps together; it never replaces them.
  2. **Small lemmas** (short Lean proofs): a sentence citing the
     computation stays fine. No bureaucracy where a line suffices —
     this law does not ask every one-line `rfl`/`ring` proof to grow
     a display.
  3. **Formability clause (C2-E14+FIX, 2026-08-10; a defect class with
     four recorded offences).** Before a statement or a display NAMES an
     object — `⊥`, `⊤`, an inverse, a quotient, any other
     instance-dependent element — the author checks that the object is
     CONSTRUCTIBLE under the hypotheses actually in force on that
     carrier. Lean's typeclass requirements are the test, and they are
     the whole test: if the Lean side would need `[BoundedOrder S]`,
     `[Inv S]`, a `Setoid`, or any instance the carrier does not carry,
     the object does not exist there and the display must not write it.
     The Lean counterpart is also the EVIDENCE, readable without
     re-deriving anything: a statement whose Lean form avoids the object
     (`¬ IsBot x` where the page wrote `x \ne \bot`; an `orderBot`
     available only under `[BoundedOrder S]`) is saying plainly that the
     object is unavailable on that carrier, and a display that writes it
     anyway is a defect, not a convenience. The repair is never to
     delete the mathematics: the unbounded carrier keeps what is true of
     it, and the bounded statement moves to the carrier where the
     hypotheses do hold (typically the completion), reached by a forward
     pointer in plain prose after the environment. The four offences to
     date, kept here as calibration: `\bot` written on an unbounded
     carrier; `(\top_{\MassS}, \bot_{\MassS})` written where
     `BoundedOrder ℝ≥0` does not exist; the mass twin of the lifted
     bounds line; and `lem:lifted-log`'s bounds line, which wrote
     $\infty$ on `LogS = WithBot ℝ`, a carrier with a bottom and no top.
     Procedure, TRANSCRIBE-FIRST — this is the order that caught the
     fourth one, and reversing it is how all four were authored: locate
     the Lean step, write the `%` comment naming the lemma it cites,
     DERIVE the display from that lemma's statement, then run the
     formability check over every object the display names. Writing the
     display from memory and hunting for a Lean step afterwards is the
     defect's cause, not merely its occasion. A blind verifier reads
     each display in a swept environment against the carrier's actual
     instances and reports every named object the carrier cannot
     construct.
  The flat-register and connective-flow laws above apply to this
  law's own glue prose unchanged; this law is about mathematical
  CONTENT (does the proof show its work?), not about sentence style.
  Two books are the standing proof-style models a worker reads before
  sweeping a proof (style references, like `new.tex`, never
  mathematical sources — the source-priority rule is untouched):
  Awodey, *Category Theory* (2010) for the TECHNICAL/FORMAL register
  (important theorems: displayed chains, precise case structure,
  formal economy — e.g. the free-monoid universal-mapping-property
  proof's equational chain), and Spivak, *Category Theory for the
  Sciences* (2014) for the NATURAL/INTUITIVE register (expository
  passages, examples, and proofs where an intuition-first reading
  serves the reader — e.g. the bijective-iff-isomorphism proof's
  witness-construction-then-discursive-verification shape). Usage
  rule: Awodey's register for proving a property OF a known structure
  (a theorem sweep's default), Spivak's register for INTRODUCING a
  structure or justifying a non-obvious step (definitions, examples,
  first-contact passages); one document may use both, the choice
  following the passage's job. Enforced by `lint-blueprint.py` (both
  copies): an advisory when a `proof` env paired with a `theorem`
  statement contains zero displayed-math blocks
  (`\[...\]`/`align*`/`gather*`/`multline*`) while its rendered prose
  exceeds ~60 words — "prose-only theorem proof; show the
  calculation" — tuned to zero false positives against the swept
  document. A blind verifier reads each swept proof against its Lean
  counterpart: every display must correspond to a real step (a named
  lemma or a case split); a narrative sentence carrying mathematical
  content with no display backing it is a finding.

- **The step-tag convention and the `have`-naming house rule (C3-ISAR,
  USER DECREE 2026-08-10).** Five display-fidelity defects across four
  tickets were caught by blind verifiers and none by policy. The
  proof-substance law, the formability clause, and the transcribe-first
  procedure were all already in this file and the class kept recurring.
  This law replaces policy with a machine for the half of that class a
  machine can decide.
  1. **The convention.** Inside the `proof` env of a covered
     theorem-family item, every displayed-math block carries an adjacent
     `% lean-step: <name>[, <name>...]` comment naming the Lean step it
     transcribes: a lemma the cited proof uses, or a labelled
     `have`/`set`/case step in its source. Adjacent means the comment
     sits in the contiguous run of `%` comment lines immediately above
     the display's opening line. Several names are allowed where a
     display legitimately fuses steps, and a fusion must be HONEST:
     every name listed has to occur.
  2. **The gate.** `scripts/blueprint.sh`'s STEP CORRESPONDENCE section
     resolves each named step against the cited declaration's own proof
     and goes RED on a name that does not occur, on a display with no
     tag, and on a covered proof with displays and no tag at all. It is
     PHASE-GATED by `content.tex`'s `% LEAN-STEP-PHASE:` line, so the
     convention lands item by item; `% LEAN-STEP-SENTINEL:` records the
     counts and is asserted every run, in the document rather than in the
     script, exactly like `% CLASSIFY-SENTINEL:`. The resolution rule and
     its transitive closure through `@[blueprint_internal]` companions
     are documented in full at the script's `cmd_lean_step_scan`. When a
     cited principal's own proof is a one-line delegation to such a
     companion (the calibrated reuse principle's normal shape for an item
     like `lem:tilt`, whose real mathematics lives in `tilt_bind'`), a
     display legitimately transcribes the COMPANION's proof body reached
     through that closure, not the principal's own one-liner: this is the
     intended reading of "the cited declaration's own proof" above, not a
     defect, and it recurs every time an item's mathematics lives in its
     internal helper rather than in its cited wrapper.
  3. **What it catches, stated without overselling it.** CATCHES: a
     display attributing a step to a lemma that does not occur in the
     cited proof; a display naming a step that does not exist; a covered
     proof with displays and no tags. DOES NOT CATCH: a display that
     names a real step and states it WRONGLY, the unformable-object class
     included. The formability clause and the human verifier stay
     load-bearing for content. One further honest limit: the constant
     side of the resolution set is the proof TERM's used constants, which
     also contain the statement's own constants, so a tag naming a
     definition the statement mentions passes while saying nothing.
  4. **The `have`-naming house rule.** A `have` that a display can cite
     is named after the MATHEMATICS it carries, never after the tactic
     that discharges it: `tmon_reading`, `log_gap_upper`,
     `fiber_sum_carries`, not `h1`/`hTm`/`hpt`. Mathlib has NO rule here
     (its style guide governs layout, its naming guide governs
     declarations), so this is ours, and its reason is specific: the
     blueprint cites these names, so they are part of the document's
     public surface, not private scratch. The side benefit is real too:
     named intermediate steps localize breakage under Mathlib churn.
  5. **`have` is the structuring primitive, not `calc`.** Mathlib's own
     ratio in the vendored checkout is 37,378 `have` lines to 2,754
     `calc` lines, with `calc` in roughly 15% of files; `calc` is a
     SPECIALIST tool for genuine chained relations, and it carries
     documented costs (uniform indentation mandatory since Lean 4.0.0;
     Lean core deliberately does not use the expected type to elaborate a
     step's LHS/RHS, an optimisation two contributors implemented and
     REVERTED, so every intermediate expression is spelled out in full
     and breaks under definitional refactors). Structure our proofs the
     same way: named `have` steps as the backbone, `calc` only for a real
     relation chain. Atomic closers (`rfl`, a single `simp`, `ring`,
     `omega`, `norm_num`, `decide`) have no internal steps to name and
     are NEVER decomposed for the sake of it. Leaf justifications stay
     one-liners (`gcongr`/`positivity`/`rel` where they apply).
  6. **Isar's shape, not Isar's scoping.** Isabelle's Isar is the model:
     there the readable proof IS the checked proof, so an attribution
     error is unrepresentable. We cannot merge the two artifacts, so we
     mechanize the link. Lean has no fact scoping: a `have` enters the
     local context and stays visible, and Isar's discipline (facts must
     be explicitly chained in) is not available. We adopt the SHAPE, not
     the scoping, and say so rather than implying otherwise.
  7. **Prior art, since the gate is a narrow novel claim.**
     leanblueprint's entire formal check is `env.contains name`, and
     `\leanok` is a hand-set human boolean; Verso Blueprint already
     INFERS dependency edges from compiled declarations and derives
     `\leanok` from sorry-freeness, but its documented resolution rule
     MERGES inferred and manual edges rather than diffing them, so it is
     about one comparison away from this gate and worth evaluating for
     adoption or upstreaming rather than duplicating. LeanArchitect
     dissolves the problem instead, by putting prose in docstrings inside
     the tactic branches; that does not fit a blueprint that is an
     authored book rather than a projection of the source. Isabelle's
     document antiquotations check terms, types, and theorem names in
     prose, not proof structure. The novel claim is narrow and sharp:
     STEP-LEVEL prose-to-proof correspondence is unclaimed.

- **Sequential composition decree (C2-E10, USER DECREE 2026-08-09).**
  Composition is always written sequentially, with the fat semicolon:
  "first $f$, then $g$" is $f \seq g$. `\circ` is banned — never write
  it for map composition, in either LaTeX source. `\seq`/`\fatsemi`
  are single-sourced in `NeSyCat.Logics/macros.sty` (the shared-macro
  import all three papers use); `blueprint/src/macros/common.tex`
  pulls them in via its existing wholesale `\input` of that file, not
  a local re-`\newcommand` copy — the single-sourcing law is satisfied
  by that live import, not a textual duplicate. Function APPLICATION
  is untouched by this decree: $f(x)$, $f(g(x))$, $\Ret(m(b))$ stay
  exactly as written regardless of how many arguments are nested —
  only the composition OPERATOR $\circ$ converts, and only where the
  source already writes it that way; never rewrite a nested
  application into a composition chain (that changes expression
  style, not notation). A genuinely foreign, non-composition `\circ`
  (quoting another author's own notation verbatim, e.g. a citation
  describing a cited paper's own operator) is exempted precisely, by
  its own fixed surrounding phrase, and disclosed at the exemption
  site — never a silent allowance. Enforced by `lint-blueprint.py`
  (both copies): a `CIRC_RE`/`circ_scan` advisory on every `\circ` in
  `content.tex` (math or prose) except the document's own sentence
  naming the banned symbol, matched by its fixed preceding phrase
  ("never write"), RED/GREEN-tested through the hook entry point.

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
