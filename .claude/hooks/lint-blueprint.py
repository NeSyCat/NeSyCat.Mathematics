#!/usr/bin/env python3
"""Implementation for lint-blueprint.sh. Reads the PostToolUse hook JSON
from stdin, and if the touched file is a *.tex file under blueprint/src/,
scans it on disk for editorial-law smells and prints non-blocking
additionalContext reminders. Never raises past main().

This is guidance, not enforcement: the gate lives in
scripts/blueprint.sh's CORRESPONDENCE section. These are instant,
in-the-loop nudges so an agent can fix a smell before it ever reaches the
gate.
"""
import json
import os
import re
import sys

THEOREM_FAMILY_BEGIN_RE = re.compile(r'\\begin\{(theorem|lemma)\}')
ABBREV_BEGIN_RE = re.compile(r'\\begin\{abbreviation\}')
ABBREV_END_RE = re.compile(r'\\end\{abbreviation\}')
REMARK_BEGIN_RE = re.compile(r'\\begin\{remark\}')
REMARK_END_RE = re.compile(r'\\end\{remark\}')
# C2-E4a full Lean-kind sync: the dead-kind list grows to match
# scripts/blueprint.sh's DEAD_KINDS (remark handled separately above,
# by its own paired begin/end scan; the rest share one generic advisory).
DEAD_KIND_BEGIN_RE = re.compile(
    r'\\begin\{(proposition|corollary|example|conjecture)\}')
RETRIAGE = {
    "proposition": "use lemma or theorem",
    "corollary": "use lemma or theorem",
    "example": "use an `instance` env (if it witnesses a class) or plain prose",
    "conjecture": "use a `theorem` env with a proof body of exactly \"Open.\"",
}
END_ANY_RE = re.compile(r'\\end\{[a-zA-Z]+\}')
BEGIN_PROOF_RE = re.compile(r'\\begin\{proof\}')
LEAN_RE = re.compile(r'\\lean\{')
LEAN_NAMES_RE = re.compile(r'\\lean\{([^}]*)\}')
LABEL_RE = re.compile(r'\\label\{([^}]*)\}')
USES_REM_RE = re.compile(r'\\uses\{[^}]*\brem:')

# Total Lean-mirror purity (C2-E3 decree): the kinds below carry a Lean
# counterpart and must contain ONLY what that counterpart contains --
# provenance, glosses, contrasts, and forward pointers move to plain
# prose outside the env. This regex is the empirically-tuned marker list
# from the ticket: bracketed provenance tags, plus phrases that are
# reliably commentary/provenance rather than mathematical content in
# this document's own voice.
PURITY_BEGIN_RE = re.compile(
    r'\\begin\{(theorem|lemma|definition|class|instance|abbreviation|proof)\}')
PURITY_MARKER_RE = re.compile(
    r'\[NeSy26|\[Girard|\[Coumans|\[NeSyCat Theory|'
    r'Distilled from|vocabulary from|axiomatized|compared in|'
    r'\bunlike a\b|transported along|see Remark|see Definition|'
    r'\bthe source\b|\bthe paper\b')
# Statement/proof anatomy (C2-E3/A6 decree): a lemma/theorem STATEMENT
# env contains exactly what the Lean statement contains -- for an
# existential/negative claim that is the \exists/\lnot-form itself, with
# no witness values or worked arithmetic (those belong in the proof
# env, matching the Lean proof's own witness-then-computation shape).
# Scoped to theorem/lemma only (never proof/definition/abbreviation/
# example -- a proof is EXACTLY where a witness and its arithmetic
# belong, and an example's whole point is showing a concrete instance).
ANATOMY_BEGIN_RE = re.compile(r'\\begin\{(theorem|lemma)\}')
ANATOMY_MARKER_RE = re.compile(
    r'\bConcretely\b|\bWitness\b|\btake\s*\$|\\tfrac', re.IGNORECASE)

# The one blessed no-Lean definition (LEAD decree, post-E2): exempt by
# label match from the purity sweep -- see FORMALIZE.md's structural
# laws for the standing exemption text.
PURITY_EXEMPT_LABELS = {"def:domain-signature-notation"}

# Book register law (C2-E5, USER DECREE 2026-08-09): the rendered page
# (comment-stripped, whole document -- not scoped to any one env) must
# carry no citation apparatus, no history/provenance markers, no dashes,
# and none of the filler phrases below. Four independent marker classes,
# each scanned line-by-line against the comment-stripped text.
REGISTER_CITATION_RE = re.compile(
    r'\[NeSy26|\[Girard|\[Coumans|\[NeSyCat Theory|'
    r'\[[A-Z][A-Za-z]*[- ]?[A-Za-z]*\s?\d{2,4}[,\]]')
# Pragmatic heuristic (disclosed in FORMALIZE.md's register law): dashes
# are flagged wherever two or more hyphens (or a literal em/en dash
# character) occur, with NO math-mode tracking. This is deliberately
# blunt -- the final swept document contains zero such occurrences
# anywhere, in or out of math, so the heuristic has zero false positives
# on it; a future legitimate math-mode "--" would call for refining this
# regex, not for leaving prose dashes unswept.
REGISTER_DASH_RE = re.compile(r'-{2,}|—|–')
REGISTER_HISTORY_RE = re.compile(
    r'Erratum|corrected upstream|revisions up to|git ref|sha256|'
    r'authored and verified', re.IGNORECASE)
REGISTER_FILLER_RE = re.compile(
    r'It is worth noting|Crucially|Note that|serves as|'
    r'plays a crucial role|underscores|highlights|In essence',
    re.IGNORECASE)

# PLAIN-LANGUAGE DENSITY (C2-E7, USER DECREE 2026-08-09): two crude,
# honest proxies for the compression-stacking/program-shaped-prose
# register smells (memory items 9 and 12) -- a rendered-prose sentence
# over WORD_LIMIT words, or with more than two real parenthetical
# groups. Both are math-mode excluded: display/inline math, and
# citation-apparatus parens such as "(Class~\ref{...})" or a bare
# enumeration marker "(i)"/"(ii)", are not prose stacking and are
# stripped/ignored before either check runs. Tuned (2026-08-09) against
# the swept content.tex to zero false positives at WORD_LIMIT=55; a
# future legitimate long math sentence may force a higher bar or a
# smarter split-on-$...$ heuristic -- raise the constant, don't disable
# the check.
DENSITY_WORD_LIMIT = 55
DENSITY_DISPLAY_MATH_RE = re.compile(r'\\\[.*?\\\]', re.DOTALL)
DENSITY_INLINE_MATH_RE = re.compile(r'\$[^$]*\$', re.DOTALL)
DENSITY_BLOCK_ENV_RE = re.compile(
    r'\\begin\{(tabular|center|align\*?|gather\*?|multline\*?|equation\*?)\}'
    r'.*?\\end\{\1\}', re.DOTALL)
DENSITY_DROP_CMD_RE = re.compile(
    r'\\(label|uses|lean|leanok|ref|eqref|cite)\{[^}]*\}')
DENSITY_UNWRAP_CMD_RE = re.compile(
    r'\\(textbf|emph|texttt|textit|mathrm)\{([^{}]*)\}')
DENSITY_ENV_MARKER_RE = re.compile(
    r'\\(begin|end)\{[a-zA-Z*]+\}(\[[^\]]*\])?(\{[^}]*\})?')
DENSITY_SENT_SPLIT_RE = re.compile(r'(?<=[.!?])\s+(?=[A-Z(])')
DENSITY_ABBR_RE = re.compile(
    r'\b(e\.g|i\.e|cf|resp|vs|etc|c\.f)\.', re.IGNORECASE)
DENSITY_PAREN_GROUP_RE = re.compile(r'\(([^()]*)\)')
DENSITY_PAREN_EXCLUDE_RE = re.compile(
    r'^\s*(MATH\s*)?'
    r'((Class|Definition|Lemma|Theorem|Corollary|Abbreviation|Section|'
    r'Example)~?\s*)?'
    r'([ivxIVX]{1,4}|[a-hA-H])?\s*(MATH\s*)?\s*$')
# Non-prose block boundaries for grouping code_lines into paragraphs:
# same granularity as this file's other multi-line scanners.
DENSITY_BOUNDARY_RE = re.compile(
    r'^\s*(\\begin\{|\\end\{|\\section\{|\\subsection\{|\\item)')

# Definition-atomicity / no-examples-in-definitions (editorial decree,
# 2026-08-09). DEFINITION_BEGIN_RE/END_RE bracket a `definition` env; the
# two structure-introduction patterns below are the two grammatical shapes
# this document uses to name a brand-new structure ("A \textbf{Foo} ... is
# a ..." and "\textbf{Foo} demands/requires ..."); counting more than one
# such introduction in a single env is the atomicity smell. Deliberately
# NOT triggered by bare \textbf{} occurrences (component names inside a
# single structure's own data, e.g. \textbf{domain symbols} inside
# def:domain-signature, are not separate structures) nor by bare
# \begin{itemize}/\begin{enumerate} (a definition's own law/component list,
# e.g. def:lin-blat2mon's binary/nullary laws, is not example content).
DEFINITION_BEGIN_RE = re.compile(r'\\begin\{definition\}')
DEFINITION_END_RE = re.compile(r'\\end\{definition\}')
STRUCT_INTRO_RE = re.compile(
    r'\b[Aa]n?\s+\\textbf\{[^}]+\}(?:[^.]{0,120})?\bis\s+(?:an?|the)\b', re.S)
MIXIN_INTRO_RE = re.compile(r'\\textbf\{[^}]+\}\s*(?:demands|requires)\b', re.S)
ITEM_INSTANCE_ROW_RE = re.compile(r'\\item\s*\\emph\{[^}]+\}\s*\([^)]*\)\s*:')
INSTANCE_MARKER_RE = re.compile(
    r'running instance|instances are|e\.g\.|for example|not an instance',
    re.IGNORECASE)


# STRUCTURE-MIRROR law (C2-E6, USER DECREE 2026-08-09): every
# \section/\subsection line, matched against the RAW (not
# comment-stripped) line, since the tag itself lives in the comment.
STRUCTURE_MIRROR_SECTION_RE = re.compile(
    r'^\\(section|subsection)\{([^}]*)\}'
    r'(?:\s*%\s*lean-dir:\s*(\S+))?\s*$')


def strip_comment(line):
    i, n = 0, len(line)
    while i < n:
        if line[i] == '%' and (i == 0 or line[i - 1] != '\\'):
            return line[:i]
        i += 1
    return line


def density_paragraphs(raw_lines):
    """Yield (start_line_1based, text) for maximal runs of non-blank,
    non-env-boundary lines, with whole non-prose block environments
    (tables, display-math wrappers) deleted first -- same granularity
    as this file's other multi-line scanners."""
    code_lines = [strip_comment(l) for l in raw_lines]
    joined = "\n".join(code_lines)

    def _blank(m):
        return "\n" * m.group(0).count("\n")
    joined = DENSITY_BLOCK_ENV_RE.sub(_blank, joined)
    code_lines = joined.split("\n")
    n = len(code_lines)
    i = 0
    while i < n:
        if DENSITY_BOUNDARY_RE.match(code_lines[i]) or code_lines[i].strip() == "":
            i += 1
            continue
        start = i
        buf = []
        while i < n:
            s = code_lines[i]
            if DENSITY_BOUNDARY_RE.match(s) or s.strip() == "":
                break
            buf.append(s)
            i += 1
        yield start + 1, "\n".join(buf)


def density_clean(text):
    text = DENSITY_DISPLAY_MATH_RE.sub(' MATH ', text)
    text = DENSITY_INLINE_MATH_RE.sub(' MATH ', text)
    text = DENSITY_DROP_CMD_RE.sub(' ', text)
    for _ in range(2):
        text = DENSITY_UNWRAP_CMD_RE.sub(r'\2', text)
    text = DENSITY_ENV_MARKER_RE.sub(' ', text)
    return text


DENSITY_DOT_MASK = "@@DENSITYDOT@@"


def density_sentences(text):
    masked = DENSITY_ABBR_RE.sub(
        lambda m: m.group(0).replace('.', DENSITY_DOT_MASK), text)
    for p in DENSITY_SENT_SPLIT_RE.split(masked):
        s = p.replace(DENSITY_DOT_MASK, '.').strip()
        if s:
            yield s


def density_scan(raw_lines, rel_posix):
    """PLAIN-LANGUAGE DENSITY (C2-E7): two crude advisories on rendered
    prose -- a sentence over DENSITY_WORD_LIMIT words, or one with more
    than two real (non-citation, non-math) parenthetical groups."""
    out = []
    for start, text in density_paragraphs(raw_lines):
        cleaned = density_clean(text)
        for sent in density_sentences(cleaned):
            words = [w for w in re.split(r'\s+', sent) if w and w != 'MATH']
            wc = len(words)
            if wc > DENSITY_WORD_LIMIT:
                out.append(
                    f"{rel_posix}:{start}: DENSITY -- rendered-prose "
                    f"sentence has {wc} words (over {DENSITY_WORD_LIMIT}, "
                    "math-mode excluded) -- one claim per sentence "
                    f"(compression-stacking, memory item 9): {sent[:100]!r}")
            groups = DENSITY_PAREN_GROUP_RE.findall(sent)
            real = [g for g in groups if not DENSITY_PAREN_EXCLUDE_RE.match(g)]
            if len(real) > 2:
                out.append(
                    f"{rel_posix}:{start}: DENSITY -- rendered-prose "
                    f"sentence has {len(real)} parenthetical groups (over "
                    "2, math/citation parens excluded) -- unpack the "
                    f"guards (program-shaped prose, memory item 12): "
                    f"{sent[:100]!r}")
    return out


def main():
    if len(sys.argv) < 2:
        return
    project_dir = sys.argv[1]

    try:
        data = json.load(sys.stdin)
    except Exception:
        return

    file_path = (data.get("tool_input") or {}).get("file_path")
    if not file_path:
        return

    if not os.path.isabs(file_path):
        abs_path = os.path.normpath(os.path.join(project_dir, file_path))
    else:
        abs_path = os.path.normpath(file_path)

    project_dir_norm = os.path.normpath(project_dir)
    try:
        rel_path = os.path.relpath(abs_path, project_dir_norm)
    except ValueError:
        return
    rel_posix = rel_path.replace(os.sep, "/")

    if not rel_posix.startswith("blueprint/src/") or not rel_posix.endswith(".tex"):
        return

    if not os.path.isfile(abs_path):
        return

    try:
        with open(abs_path, "r", encoding="utf-8", errors="replace") as fh:
            raw_lines = fh.read().splitlines()
    except Exception:
        return

    code_lines = [strip_comment(l) for l in raw_lines]
    n = len(code_lines)
    warnings = []

    # BIJECTION LAW (C2-E4a/A1): a \lean{} list with >=2 names -- strong
    # warning, this is a hard structural violation (scripts/blueprint.sh
    # rejects it). Multi-line \lean{...} calls are handled by joining
    # continuation lines until the closing brace.
    idx = 0
    while idx < n:
        if '\\lean{' in code_lines[idx] and '}' not in code_lines[idx].split('\\lean{', 1)[1]:
            # multi-line \lean{...}; join forward until the closing brace.
            joined = code_lines[idx]
            j = idx + 1
            while j < n and '}' not in code_lines[j]:
                joined += " " + code_lines[j]
                j += 1
            if j < n:
                joined += " " + code_lines[j]
            m = LEAN_NAMES_RE.search(joined)
        else:
            m = LEAN_NAMES_RE.search(code_lines[idx])
        if m:
            names = [x.strip() for x in m.group(1).split(',') if x.strip()]
            if len(names) > 1:
                warnings.append(
                    f"{rel_posix}:{idx + 1}: STRONG WARNING -- \\lean{{}} "
                    f"names {names} violate the bijection law (exactly one "
                    "principal name per env; demote the rest to unmarked "
                    "internals, tagged in the .lean source)")
        idx += 1

    # \uses{rem:...} -- strong warning, this is a hard structural violation.
    for idx, line in enumerate(code_lines):
        if USES_REM_RE.search(line):
            warnings.append(
                f"{rel_posix}:{idx + 1}: STRONG WARNING -- \\uses{{rem:...}} "
                "cites a remark; remarks may not be depended on "
                "(scripts/blueprint.sh CORRESPONDENCE will reject this)")

    # abbreviation env without \lean{}; remark containing \lean or display
    # math (promotion candidate).
    idx = 0
    while idx < n:
        if ABBREV_BEGIN_RE.search(code_lines[idx]):
            start = idx
            end = idx
            for j in range(idx, n):
                if ABBREV_END_RE.search(code_lines[j]):
                    end = j
                    break
            body = "\n".join(code_lines[start:end + 1])
            if not LEAN_RE.search(body):
                warnings.append(
                    f"{rel_posix}:{start + 1}: abbreviation environment has "
                    "no \\lean{} name")
            idx = end + 1
            continue
        if REMARK_BEGIN_RE.search(code_lines[idx]):
            start = idx
            end = idx
            for j in range(idx, n):
                if REMARK_END_RE.search(code_lines[j]):
                    end = j
                    break
            # Remark-abolition decree (C2-E3): remarks are abolished
            # outright -- the former promotion-candidate advisories
            # (carries \lean{}; contains display math) are replaced by
            # this one simple advisory, since a remark's CONTENT no
            # longer matters -- its mere EXISTENCE is the smell.
            warnings.append(
                f"{rel_posix}:{start + 1}: remark environment present -- "
                "remarks are abolished, write plain prose")
            idx = end + 1
            continue
        if DEAD_KIND_BEGIN_RE.search(code_lines[idx]):
            kind = DEAD_KIND_BEGIN_RE.search(code_lines[idx]).group(1)
            warnings.append(
                f"{rel_posix}:{idx + 1}: {kind} environment present -- "
                f"{kind} is abolished -- {RETRIAGE[kind]}")
            idx += 1
            continue
        if DEFINITION_BEGIN_RE.search(code_lines[idx]):
            start = idx
            end = idx
            for j in range(idx, n):
                if DEFINITION_END_RE.search(code_lines[j]):
                    end = j
                    break
            body = "\n".join(code_lines[start:end + 1])
            struct_count = (len(STRUCT_INTRO_RE.findall(body))
                             + len(MIXIN_INTRO_RE.findall(body)))
            if struct_count > 1:
                warnings.append(
                    f"{rel_posix}:{start + 1}: definition not atomic -- "
                    "split (one structure per definition)")
            if (INSTANCE_MARKER_RE.search(body)
                    or ITEM_INSTANCE_ROW_RE.search(body)):
                warnings.append(
                    f"{rel_posix}:{start + 1}: example content inside "
                    "definition -- move to an example env")
            idx = end + 1
            continue
        idx += 1

    # theorem-family \begin{...} without a following \begin{proof} anywhere
    # later in the file (best-effort, whole-file scan; the gate does the
    # precise adjacency check).
    for idx, line in enumerate(code_lines):
        if THEOREM_FAMILY_BEGIN_RE.search(line):
            # Find this env's \end{...}.
            kind = THEOREM_FAMILY_BEGIN_RE.search(line).group(1)
            end_re = re.compile(r'\\end\{' + kind + r'\}')
            end_idx = None
            for j in range(idx, n):
                if end_re.search(code_lines[j]):
                    end_idx = j
                    break
            if end_idx is None:
                continue
            # Skip blank/comment lines after end_idx; check next real line.
            j = end_idx + 1
            while j < n and code_lines[j].strip() == "":
                j += 1
            if j >= n or not BEGIN_PROOF_RE.search(code_lines[j]):
                warnings.append(
                    f"{rel_posix}:{idx + 1}: {kind} environment has no "
                    "\\begin{proof} immediately following")

    # Total Lean-mirror purity (C2-E3): every theorem-family/definition/
    # abbreviation/example/proof env body must contain ONLY what its
    # Lean counterpart contains -- provenance, glosses, contrasts, and
    # forward pointers belong in plain prose outside the env. Scan each
    # such env independently (kinds overlap with the scans above, but
    # this pass is self-contained and does not consume idx from them).
    idx = 0
    while idx < n:
        m = PURITY_BEGIN_RE.search(code_lines[idx])
        if not m:
            idx += 1
            continue
        kind = m.group(1)
        start = idx
        end = idx
        end_re = re.compile(r'\\end\{' + kind + r'\}')
        for j in range(idx, n):
            if end_re.search(code_lines[j]):
                end = j
                break
        body = "\n".join(code_lines[start:end + 1])
        label_m = LABEL_RE.search(body)
        label = label_m.group(1) if label_m else None
        if label not in PURITY_EXEMPT_LABELS:
            pm = PURITY_MARKER_RE.search(body)
            if pm:
                warnings.append(
                    f"{rel_posix}:{start + 1}: {kind} contains "
                    "commentary/provenance -- move to plain text outside "
                    f"the env (absolutely-lean) [matched: {pm.group(0)!r}]")
        idx = end + 1

    # Statement/proof anatomy (C2-E3/A6): a lemma/theorem STATEMENT
    # carries no witness values or worked arithmetic -- those belong in
    # its proof. Independent pass, scoped to theorem/lemma only.
    idx = 0
    while idx < n:
        m = ANATOMY_BEGIN_RE.search(code_lines[idx])
        if not m:
            idx += 1
            continue
        kind = m.group(1)
        start = idx
        end = idx
        end_re = re.compile(r'\\end\{' + kind + r'\}')
        for j in range(idx, n):
            if end_re.search(code_lines[j]):
                end = j
                break
        body = "\n".join(code_lines[start:end + 1])
        am = ANATOMY_MARKER_RE.search(body)
        if am:
            label_m = LABEL_RE.search(body)
            label = label_m.group(1) if label_m else "<no-label>"
            warnings.append(
                f"{rel_posix}:{start + 1}: {kind} {label} -- "
                "witness/computation inside a statement env -- proof "
                "content; move to the proof env (statement/proof anatomy "
                f"law) [matched: {am.group(0)!r}]")
        idx = end + 1

    # Book register law (C2-E5): whole-document, comment-stripped scan
    # for rendered-text apparatus leakage -- citations, dashes, history
    # markers, filler phrases. Independent of env boundaries: a
    # provenance sentence between two envs is just as much a leak as one
    # inside a definition.
    for idx, line in enumerate(code_lines):
        cm = REGISTER_CITATION_RE.search(line)
        if cm:
            warnings.append(
                f"{rel_posix}:{idx + 1}: REGISTER -- bracket-citation "
                f"apparatus on the rendered page [matched: {cm.group(0)!r}] "
                "-- move to a % comment (book register law)")
        dm = REGISTER_DASH_RE.search(line)
        if dm:
            warnings.append(
                f"{rel_posix}:{idx + 1}: REGISTER -- dash on the rendered "
                f"page [matched: {dm.group(0)!r}] -- restructure with a "
                "comma, colon, period, or parentheses (book register law; "
                "hyphens in compound words and math minus signs are fine)")
        hm = REGISTER_HISTORY_RE.search(line)
        if hm:
            warnings.append(
                f"{rel_posix}:{idx + 1}: REGISTER -- history/provenance "
                f"marker on the rendered page [matched: {hm.group(0)!r}] "
                "-- move to a % comment plus PROGRESS.md/the ledger (book "
                "register law)")
        fm = REGISTER_FILLER_RE.search(line)
        if fm:
            warnings.append(
                f"{rel_posix}:{idx + 1}: REGISTER -- filler phrase on the "
                f"rendered page [matched: {fm.group(0)!r}] -- reword "
                "plainly (book register law)")

    # PLAIN-LANGUAGE DENSITY (C2-E7, USER DECREE 2026-08-09): see
    # density_scan's docstring. Whole-document, paragraph-granularity.
    warnings.extend(density_scan(raw_lines, rel_posix))

    # STRUCTURE-MIRROR advisory (C2-E6, USER DECREE 2026-08-09): a
    # \section/\subsection introduced or left without a trailing
    # `% lean-dir: <FolderName>' tag. Advisory only -- the hard gate is
    # scripts/blueprint.sh's structure-mirror CORRESPONDENCE subsection
    # and the commit-msg hook; this is just an instant nudge.
    for idx, raw in enumerate(raw_lines):
        m = STRUCTURE_MIRROR_SECTION_RE.match(raw.rstrip("\n"))
        if m and m.group(3) is None:
            kind, title = m.group(1), m.group(2)
            warnings.append(
                f"{rel_posix}:{idx + 1}: STRUCTURE-MIRROR -- "
                f"\\{kind}{{{title}}} carries no '% lean-dir: <FolderName>' "
                "tag (structure-mirror law; Introduction alone may tag "
                "'% lean-dir: -')")

    if not warnings:
        return

    out = {
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": (
                "lint-blueprint (non-blocking editorial-law reminders):\n"
                + "\n".join(warnings)
            ),
        }
    }
    print(json.dumps(out))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
