# PROGRESS.md — Campaign Progress Ledger

Tracks the formalization status of each cluster of the
NeSyCat library (canonical document `blueprint/src/content.tex`,
sources cited bibliographically therein — see `CLAUDE.md`). Updated at
the end of every work unit per `FORMALIZE.md`.

## Status legend

| Status                | Meaning                                                            |
|------------------------|---------------------------------------------------------------------|
| `not-started`          | No file/content exists for this section yet.                       |
| `stubs`                | File exists; item names/statements sketched, mostly `sorry`.       |
| `stated`               | All in-scope items from the canonical library document are stated (typechecking statements), proofs not yet attempted. |
| `partial`              | Some items proved, some still `sorry`.                             |
| `proved`               | All in-scope Definitions/Lemmas/Theorems for the section are proved (exercises may remain). |
| `complete(+exercises)` | Section fully proved including its exercises.                      |

## NeSyCat library

Active library work, canonical document `blueprint/src/content.tex`
(provenance: bibliographic citations, e.g. `[NeSy26, App. A]`, with
pinned texts recorded at their git refs), Lean home `NeSyCat/` (topic
folders as content emerges).

| Cluster                                                                    | Status      |
|-----------------------------------------------------------------------------|-------------|
| Semiring-monad infrastructure (`M_S`, `D` as mass-one submonad)              | partial (def:lattice-semiring stated, Boolean+mass instances done, log instance pending C1-T3; lem:prob-not-semiring proved; def:semiring-monad + thm:semiring-monad-laws proved in `NeSyCat/Monad/SemiringMonad.lean` (`MS`, `ret`, `bind`, `ret_bind`/`bind_ret`/`bind_assoc`, `Tens`); rem:semiring-monad-algebras split out as a stretch target, not proved; def:dist-monad and lem:log-iso not yet started) |
| Truth spaces `M(Bool)`                                                      | not-started |
| Lifted connectives (mass+log, derived `p+q−pq`)                             | not-started |
| Pointwise/linear-laws/copying-laws lemmas + three-layers theorem            | not-started |
| Batch monad + transformer + pointwise evaluation                           | not-started |
| dec/enc/Z suite + tilt lemma + mass preservation + pull-out theorem + normalizer corollaries | not-started |
| Examples (failure numbers, MNIST commute)                                  | not-started |

OPEN: chain version of the tilt bound.

Fine-grained per-item status (labels, `\lean`/`\leanok` marks) lives in
`blueprint/src/content.tex`, not in this table.

## Notes

- See `FORMALIZE.md` for the resume protocol and work loop.
