#!/usr/bin/env python3
"""Implementation for lint-lean.sh. Reads the PostToolUse hook JSON from
stdin, and if the touched file is a *.lean file under NeSyCat/, scans the
file on disk for FORMALIZE.md hard bans (axiom, native_decide) and for a
bare `sorry` lacking an adjacent `-- TODO:` comment. Never raises past
main()."""
import json
import os
import re
import sys

SORRY_RE = re.compile(r"(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)")
COMMENT_SORRY_RE = re.compile(r"^--.*sorry")
COMMENT_RE = re.compile(r"^--")
AXIOM_RE = re.compile(r"^[ \t]*(private[ \t]+|protected[ \t]+)?axiom[ \t]")
NATIVE_DECIDE_RE = re.compile(r"(^|[^A-Za-z0-9_])native_decide([^A-Za-z0-9_]|$)")
TODO_RE = re.compile(r"--.*TODO")

# FEEDBACK-LOOP / blueprint-correspondence additions (Run 5 finale, ticket
# H1): these are advisory only (additionalContext), never blocking -- the
# gate is scripts/blueprint.sh's CORRESPONDENCE section.
BLUEPRINT_LABEL_RE = re.compile(r"Blueprint\s+([A-Za-z]+:[A-Za-z0-9_-]+)")
DECL_NAME_RE = re.compile(
    r"^(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)")
TEX_LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
TEX_LEAN_RE = re.compile(r"\\lean\{([^}]*)\}")


def find_content_tex(project_dir):
    path = os.path.join(project_dir, "blueprint", "src", "content.tex")
    return path if os.path.isfile(path) else None


def blueprint_labels(content_tex_path):
    """Return the set of all \\label{...} keys in content.tex."""
    try:
        with open(content_tex_path, "r", encoding="utf-8", errors="replace") as fh:
            text = fh.read()
    except Exception:
        return set()
    return set(TEX_LABEL_RE.findall(text))


def blueprint_lean_name_index(content_tex_path):
    """Return {declared-name: nearest-preceding-\\label} for every name that
    appears in a \\lean{...} mark, by walking the file line-by-line and
    tracking the most recently seen \\label{...} (labels sit right after
    \\begin{...}, \\lean{...} shortly after -- matches the corpus layout)."""
    try:
        with open(content_tex_path, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.readlines()
    except Exception:
        return {}
    index = {}
    current_label = None
    for line in lines:
        lm = TEX_LABEL_RE.search(line)
        if lm:
            current_label = lm.group(1)
        for m in TEX_LEAN_RE.finditer(line):
            for nm in m.group(1).split(','):
                nm = nm.strip()
                if nm and current_label:
                    index[nm] = current_label
    return index


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

    if not rel_posix.startswith("NeSyCat/") or not rel_posix.endswith(".lean"):
        return

    if not os.path.isfile(abs_path):
        return

    try:
        with open(abs_path, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.read().splitlines()
    except Exception:
        return

    hard_bans = []  # list of "line N: detail"
    sorry_lines = []  # line numbers with sorry-but-no-TODO

    for idx, line in enumerate(lines):
        line_no = idx + 1
        trimmed = line.strip()
        is_comment_line = bool(COMMENT_RE.match(trimmed))

        # axiom / native_decide: skip pure comment lines.
        if not is_comment_line:
            if AXIOM_RE.match(line):
                hard_bans.append(f"{rel_posix}:{line_no}: axiom -- {trimmed}")
            elif NATIVE_DECIDE_RE.search(line):
                hard_bans.append(f"{rel_posix}:{line_no}: native_decide -- {trimmed}")

        # sorry: skip pure line-comments mentioning sorry.
        if COMMENT_SORRY_RE.match(trimmed):
            continue
        if SORRY_RE.search(line):
            same = bool(TODO_RE.search(line))
            prev_line = lines[idx - 1] if idx - 1 >= 0 else ""
            next_line = lines[idx + 1] if idx + 1 < len(lines) else ""
            adjacent = bool(TODO_RE.search(prev_line)) or bool(TODO_RE.search(next_line))
            if not (same or adjacent):
                sorry_lines.append(f"{rel_posix}:{line_no}")

    if hard_bans:
        detail = "; ".join(hard_bans)
        out = {
            "decision": "block",
            "reason": f"FORMALIZE.md hard ban violated: {detail}",
        }
        print(json.dumps(out))
        return

    advisories = []

    if sorry_lines:
        advisories.append(
            "Reminder: every sorry needs an adjacent -- TODO: note "
            f"(FORMALIZE.md sorry policy). Found at: {', '.join(sorry_lines)}"
        )

    # (i) doc comments citing "Blueprint <label>": the label must exist in
    # content.tex.
    content_tex_path = find_content_tex(project_dir)
    if content_tex_path:
        labels = blueprint_labels(content_tex_path)
        cited_missing = []
        for idx, line in enumerate(lines):
            for m in BLUEPRINT_LABEL_RE.finditer(line):
                label = m.group(1)
                if label not in labels:
                    cited_missing.append(f"{rel_posix}:{idx + 1}: '{label}'")
        if cited_missing:
            advisories.append(
                "Doc comment cites a blueprint label not found in "
                "content.tex (check the tex-label matches exactly): "
                + "; ".join(cited_missing)
            )

        # (ii) FEEDBACK-LOOP reminder: declaration names in this file that
        # are cited by a \lean{} mark in content.tex -- touching them means
        # the FORMALIZE.md/H1 feedback-loop duty applies (tighten the
        # blueprint text against the final Lean form; Blueprint-sync:
        # commit-message convention).
        lean_index = blueprint_lean_name_index(content_tex_path)
        if lean_index:
            declared_names = set()
            for line in lines:
                m = DECL_NAME_RE.match(line)
                if m:
                    declared_names.add(m.group(1))
            # Names in content.tex are namespaced NeSyCat.Foo; declarations
            # inside `namespace NeSyCat ... end NeSyCat` are written bare
            # (`Foo`), so match on both the bare and NeSyCat.-qualified form.
            affected_labels = set()
            for nm, label in lean_index.items():
                bare = nm[len("NeSyCat."):] if nm.startswith("NeSyCat.") else nm
                if nm in declared_names or bare in declared_names:
                    affected_labels.add(label)
            if affected_labels:
                advisories.append(
                    "FEEDBACK-LOOP duty (FORMALIZE.md / blueprint<->Lean "
                    "correspondence): this file touches declaration(s) "
                    "cited by blueprint item(s) "
                    f"{', '.join(sorted(affected_labels))}. After \\leanok, "
                    "tighten the blueprint text against the formalized "
                    "form and, if content.tex changes, commit it together "
                    "with this file or note the justified skip via a "
                    "'Blueprint-sync:' commit-message line."
                )

    if advisories:
        out = {
            "hookSpecificOutput": {
                "hookEventName": "PostToolUse",
                "additionalContext": "\n".join(advisories),
            }
        }
        print(json.dumps(out))
        return

    # else: silent.


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
