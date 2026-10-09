#!/usr/bin/env python3
"""Dump theorem-like statements from Parts A--G beside their Lean counterparts.

The matcher is deliberately conservative.  A blank Lean column is preferable
to claiming that a scalar ``*_core`` lemma formalizes a complete manuscript
theorem.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
import html
import json
import re
import sys
import unicodedata
from dataclasses import asdict, dataclass, replace
from difflib import SequenceMatcher
from pathlib import Path

from lean_audit_report import (read_audit, blueprint_consistency, hypothesis_panel,
                               consistency_panel, audit_panel, proof_summary)


THEOREM_ENVS = ("theorem", "lemma", "proposition", "corollary", "conjecture")
STOP_WORDS = {
    "a", "an", "and", "at", "bound", "by", "constant", "core", "exact",
    "for", "from", "in", "inequality", "lemma", "of", "on", "one", "part",
    "proposition", "the", "theorem", "to", "under", "with",
}
LEAN_DECL = re.compile(
    r"(?m)^(?P<kw>theorem|lemma|example)\s+(?P<name>[A-Za-z_][\w'.]*)"
)
PART_RE = re.compile(r"\\part\{Part\s+([A-G])\b", re.I)
BEGIN_RE = re.compile(
    r"\\begin\{(" + "|".join(THEOREM_ENVS) + r")\}"
    r"(?:\[(?P<title>[^\]]*)\])?",
    re.I,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
DOC_RE = re.compile(r"/--(?P<body>.*?)--/\s*$", re.S)


@dataclass
class ManuscriptItem:
    index: int
    part: str
    kind: str
    title: str
    label: str
    line: int
    source: str
    remark: str = ""


@dataclass
class LeanItem:
    name: str
    line: int
    file: str
    doc: str
    source: str
    remark: str = ""
    status: str = ""


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def strip_tex(value: str) -> str:
    value = re.sub(r"\\(?:Cref|cref|eqref|ref)\{([^}]*)\}", r"\1", value)
    value = re.sub(r"\\[A-Za-z@]+(?:\[[^\]]*\])?", " ", value)
    value = value.replace("{", " ").replace("}", " ").replace("~", " ")
    return re.sub(r"\s+", " ", value).strip()


def tokens(value: str) -> set[str]:
    value = re.sub(r"([a-z])([A-Z])", r"\1 \2", value)
    words = re.findall(r"[a-z0-9]+", value.lower().replace("_", " "))
    return {word for word in words if len(word) > 1 and word not in STOP_WORDS}


def extract_manuscript(path: Path) -> list[ManuscriptItem]:
    text = path.read_text(encoding="utf-8")
    parts = [(m.start(), m.group(1).upper()) for m in PART_RE.finditer(text)]
    # Part A is the front part of this manuscript and has no explicit \part
    # command.  Material after \appendix is supporting material, not Part G.
    appendix_match = re.search(r"(?m)^\\appendix\b", text)
    parts_end = appendix_match.start() if appendix_match else len(text)
    items: list[ManuscriptItem] = []
    for match in BEGIN_RE.finditer(text):
        if match.start() >= parts_end:
            continue
        end_marker = rf"\end{{{match.group(1)}}}"
        end = text.find(end_marker, match.end())
        if end < 0:
            raise ValueError(f"unclosed {match.group(1)} at {path}:{line_number(text, match.start())}")
        end += len(end_marker)
        part = "A"
        for offset, candidate in parts:
            if offset > match.start():
                break
            part = candidate
        if part not in "ABCDEFG":
            continue
        source = text[match.start():end].strip()
        label_match = LABEL_RE.search(source)
        label = label_match.group(1) if label_match else ""
        title = strip_tex(match.group("title") or label.replace("-", " "))
        kind = match.group(1).lower()
        notes = []
        if kind == "conjecture":
            notes.append("Open conjecture; a Lean theorem should only encode a conditional implication.")
        if not label:
            notes.append("No manuscript label; automatic matching is less reliable.")
        items.append(ManuscriptItem(
            index=len(items) + 1, part=part, kind=kind, title=title,
            label=label, line=line_number(text, match.start()), source=source,
            remark=" ".join(notes),
        ))
    return items


def declaration_end(text: str, start: int) -> int:
    next_decl = re.search(
        r"(?m)^(?:/--|theorem\s+|lemma\s+|example\s+|def\s+|"
        r"noncomputable\s+def\s+|inductive\s+|structure\s+|namespace\s+|end\b)",
        text[start + 1:],
    )
    return len(text) if next_decl is None else start + 1 + next_decl.start()


def trim_lean_diagnostics(source: str) -> str:
    """Do not attach a following #print/#check command to a declaration card.

    Mask comments (including nested ones) and strings before looking for a
    standalone command, so a quoted diagnostic in a docstring is preserved.
    """
    masked = list(source)
    i, depth, quoted = 0, 0, False
    while i < len(source):
        if not quoted and source.startswith('/-', i):
            depth += 1
            masked[i:i + 2] = '  '
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            masked[i:i + 2] = '  '
            i += 2
        elif depth:
            if source[i] != '\n': masked[i] = ' '
            i += 1
        elif not quoted and source.startswith('--', i):
            end = source.find('\n', i)
            end = len(source) if end < 0 else end
            masked[i:end] = ' ' * (end - i)
            i = end
        elif source[i] == '"':
            quoted = not quoted
            masked[i] = ' '
            i += 1
        elif quoted:
            masked[i] = '\n' if source[i] == '\n' else ' '
            if source[i] == '\\' and i + 1 < len(source):
                masked[i + 1] = ' '
                i += 1
            i += 1
        else:
            i += 1
    command = re.search(r'(?m)^\s*#(?:print|check|eval|reduce|synth|guard)\b', ''.join(masked))
    return source[:command.start()].rstrip() if command else source


# Blueprint `\lean{}` names are fully qualified and may name definitions,
# structures and Props, so the closed-case mode needs every declaration kind
# and the enclosing namespaces.  The Parts A--G mode keeps the narrower
# `LEAN_DECL`, whose bare names its ledger uses.
LEAN_ANY_DECL = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(?P<kw>theorem|lemma|alias|def|abbrev|structure|class|inductive|instance)\s+"
    r"(?P<name>[A-Za-z_][\w'.]*)"
)
# Whole-line scope commands only, so prose such as "section pins them down"
# or "end of this file" inside a comment is not mistaken for one.
SCOPE_RE = re.compile(
    r"(?m)^(?:noncomputable[ \t]+)?(?P<kw>namespace|section|end)"
    r"(?:[ \t]+(?P<name>[A-Za-z_][\w'.]*))?[ \t]*(?:--.*)?$"
)


def namespace_changes(text: str) -> tuple[list[int], list[str]]:
    """Offsets at which the open namespace changes, and the namespace from each."""
    stack: list[tuple[str, str]] = []
    offsets, spaces = [0], [""]
    for match in SCOPE_RE.finditer(text):
        kw, name = match.group("kw"), match.group("name") or ""
        if kw == "end":
            if not stack or (name and stack[-1][1] != name):
                continue
            stack.pop()
        else:
            stack.append((kw, name))
        offsets.append(match.start())
        spaces.append(".".join(n for k, n in stack if k == "namespace"))
    return offsets, spaces


def extract_lean(lean_dir: Path, qualified: bool = False) -> list[LeanItem]:
    result: list[LeanItem] = []
    for path in sorted(lean_dir.glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        offsets, spaces = namespace_changes(text) if qualified else ([0], [""])
        matches = list((LEAN_ANY_DECL if qualified else LEAN_DECL).finditer(text))
        for position, match in enumerate(matches):
            name = match.group("name")
            space = spaces[bisect_right(offsets, match.start()) - 1]
            if qualified and name.startswith("_root_."):
                name = name[len("_root_."):]
            elif space:
                name = f"{space}.{name}"
            # Attach the immediately preceding doc comment, when present.
            prefix = text[:match.start()]
            doc_match = DOC_RE.search(prefix)
            block_start = doc_match.start() if doc_match else match.start()
            doc = re.sub(r"\s+", " ", doc_match.group("body")).strip() if doc_match else ""
            end = declaration_end(text, match.start())
            if qualified and position + 1 < len(matches):
                # `declaration_end` does not stop at `@[simp]` or `private`
                # declarations, which would leak their bodies into this one.
                end = min(end, matches[position + 1].start())
            source = trim_lean_diagnostics(text[block_start:end].strip())
            lowered = f"{match.group('name')} {doc}".lower()
            notes = []
            if any(word in lowered for word in (" core", "_core", "scalar endpoint", "abstract ")):
                notes.append("Partial counterpart: algebraic/scalar core only.")
            if any(word in lowered for word in ("explicit hypothesis", "under the hypothesis", "assumed")):
                notes.append("Conditional counterpart: the open input is an explicit hypothesis.")
            result.append(LeanItem(
                name=name, line=line_number(text, match.start()),
                file=path.as_posix(), doc=doc, source=source,
                remark=" ".join(notes),
            ))
    return result


def part_hint(item: LeanItem) -> str:
    match = re.search(r"part_?([a-g])", f"{item.name} {item.file}", re.I)
    return match.group(1).upper() if match else ""


def similarity(manuscript: ManuscriptItem, lean: LeanItem) -> float:
    left = " ".join((manuscript.title, manuscript.label.replace("-", " ")))
    right = " ".join((lean.name, lean.doc))
    lt, rt = tokens(left), tokens(right)
    if not lt or not rt:
        return 0.0
    overlap = len(lt & rt) / len(lt | rt)
    sequence = SequenceMatcher(None, " ".join(sorted(lt)), " ".join(sorted(rt))).ratio()
    containment = len(lt & rt) / len(lt)
    score = 0.45 * overlap + 0.25 * sequence + 0.30 * containment
    hint = part_hint(lean)
    if hint and hint != manuscript.part:
        score *= 0.25
    elif hint == manuscript.part:
        score += 0.08
    return min(score, 1.0)


def load_overrides(path: Path | None) -> dict[str, object]:
    if path is None:
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("correspondence file must be a JSON object")
    return data


def manuscript_key(item: ManuscriptItem) -> str:
    return item.label or f"{item.part}:{item.index}"


def match_items(
    manuscripts: list[ManuscriptItem],
    lean_items: list[LeanItem],
    overrides: dict[str, object],
    threshold: float,
) -> list[tuple[ManuscriptItem, LeanItem | None, float]]:
    by_name = {item.name: item for item in lean_items}
    matches = []
    for manuscript in manuscripts:
        key = manuscript_key(manuscript)
        if key in overrides:
            entry = overrides[key]
            if isinstance(entry, dict):
                name = entry.get("lean")
                manuscript = replace(
                    manuscript,
                    remark=str(entry.get("manuscript_remark", manuscript.remark)),
                )
                curated_lean_remark = str(entry.get("lean_remark", ""))
                status = str(entry.get("status", "curated"))
            else:
                name = entry
                curated_lean_remark = ""
                status = "curated"
            if name is None:
                if not manuscript.remark:
                    manuscript = replace(
                        manuscript,
                        remark="No corresponding Lean declaration was found in the current repository.",
                    )
                matches.append((manuscript, None, 1.0))
                continue
            if not isinstance(name, str):
                raise ValueError(f"correspondence for {key!r} must use a Lean name string or null")
            if name not in by_name:
                raise ValueError(f"correspondence for {key!r} names unknown Lean declaration {name!r}")
            lean = by_name[name]
            scope = f"Curated classification: {status} counterpart."
            lean = replace(
                lean,
                remark=" ".join(filter(None, (scope, curated_lean_remark, lean.remark))),
                status=status,
            )
            matches.append((manuscript, lean, 1.0))
            continue
        candidates = sorted(
            ((similarity(manuscript, lean), lean) for lean in lean_items),
            key=lambda pair: pair[0], reverse=True,
        )
        score, lean = candidates[0] if candidates else (0.0, None)
        matches.append((manuscript, lean if score >= threshold else None, score))
    return matches


def combined_remarks(
    manuscript: ManuscriptItem, lean: LeanItem | None, score: float, threshold: float
) -> tuple[str, str]:
    manuscript_note = manuscript.remark
    if lean is None:
        extra = "No sufficiently confident Lean counterpart was found."
        manuscript_note = f"{manuscript_note} {extra}".strip()
        return manuscript_note, "Missing counterpart."
    lean_note = lean.remark
    if manuscript.kind == "conjecture":
        lean_note = (
            f"{lean_note} This is at most a conditional encoding; it does not "
            "constitute a proof of the manuscript conjecture."
        ).strip()
    if score < threshold + 0.12:
        lean_note = f"{lean_note} Heuristic match; review this pairing.".strip()
    if not lean_note:
        lean_note = "Candidate full counterpart; verify semantic scope before citing formalization."
    return manuscript_note or "No special manuscript-side remark.", lean_note


def status_group(manuscript: ManuscriptItem, lean: LeanItem | None) -> str:
    """Coarse display class without weakening the exact ledger wording."""
    if lean is None:
        return "unmatched"
    if lean.status == "full":
        return "complete"
    if manuscript.kind == "conjecture" or "open" in lean.status.lower():
        return "open"
    return "incomplete"


def render_markdown(
    matches: list[tuple[ManuscriptItem, LeanItem | None, float]],
    manuscript_path: Path,
    threshold: float,
) -> str:
    lines = [
        "# Parts A–G theorems and Lean counterparts",
        "",
        f"Generated from `{manuscript_path.as_posix()}`. Matches below 100% are "
        "heuristic unless supplied through an override file. “Partial counterpart” "
        "does not certify the complete manuscript statement.",
        "",
    ]
    current_part = ""
    for manuscript, lean, score in matches:
        if manuscript.part != current_part:
            current_part = manuscript.part
            lines += [f"## Part {current_part}", ""]
        title = manuscript.title or manuscript.label or f"unnamed {manuscript.kind}"
        manuscript_note, lean_note = combined_remarks(manuscript, lean, score, threshold)
        lean_location = (
            f"`{lean.file}:{lean.line}` · "
            + ("curated correspondence" if score == 1.0 else f"match score `{score:.2f}`")
            if lean else f"No match · best score `{score:.2f}`"
        )
        left = (
            f"<b>{html.escape(manuscript.kind.title())}</b><br>"
            f"<code>{html.escape(manuscript.label or '(no label)')}</code><br>"
            f"<small>{html.escape(manuscript_path.as_posix())}:{manuscript.line}</small>"
            f"<pre>{html.escape(manuscript.source)}</pre>"
            f"<b>Remark:</b> {html.escape(manuscript_note)}"
        )
        right_source = html.escape(lean.source) if lean else "(none)"
        right_name = html.escape(lean.name) if lean else "No Lean counterpart found"
        status_line = (
            f"<b>Ledger status:</b> <code>{html.escape(lean.status)}</code><br>"
            if lean and lean.status else ""
        )
        right = (
            f"<b>{right_name}</b><br><small>{html.escape(lean_location)}</small>"
            f"<br>{status_line}<pre>{right_source}</pre>"
            f"<b>Remark:</b> {html.escape(lean_note)}"
        )
        lines += [
            f"### {manuscript.index}. {title}",
            "",
            "<table><tr><th width=\"50%\">Manuscript</th>"
            "<th width=\"50%\">Lean counterpart</th></tr>",
            f"<tr><td valign=\"top\">{left}</td><td valign=\"top\">{right}</td></tr></table>",
            "",
        ]
    return "\n".join(lines)


def html_article(
    index: int, title: str, group: str, badge: str,
    kind: str, label: str, location: str, source: str, note: str,
    lean_name: str, lean_location: str, lean_source: str, lean_note: str,
    left_heading: str = "Manuscript", anchor: str = "", remark_html=html.escape,
    typeset: str = "", lean_extra: str = "", extra_badge: str = "", notice_html: str = "",
) -> str:
    """`remark_html` renders the two remarks; source columns are always escaped verbatim.

    `typeset`, when given, is Markdown-with-TeX that the page typesets in the
    browser; the verbatim source then moves into a collapsed block below it.
    """
    anchor_attr = f' id="{html.escape(anchor)}"' if anchor else ""
    source_html = f"<pre>{html.escape(source)}</pre>"
    if typeset:
        source_html = (
            f'<div class="tex" data-tex="{html.escape(typeset, quote=True)}"></div>\n'
            f"      <details><summary>LaTeX source</summary>{source_html}</details>"
        )
    return f"""
<article{anchor_attr} class="statement status-{group}" data-status="{html.escape(group)}">
  <h3>{index}. {html.escape(title)}
    <span class="status-badge">{html.escape(badge)}</span>{extra_badge}</h3>
{notice_html + chr(10) if notice_html else ''}  <div class="columns">
    <section>
      <h4>{left_heading}</h4>
      <div class="meta"><strong>{html.escape(kind.title())}</strong>
        · <code>{html.escape(label or "(no label)")}</code>
        · {html.escape(location)}</div>
      {source_html}
      <p class="remark"><strong>Remark:</strong> {remark_html(note)}</p>
    </section>
    <section>
      <h4>Lean counterpart</h4>
      <div class="meta"><strong>{html.escape(lean_name)}</strong>
        · {html.escape(lean_location)}</div>
      {lean_extra}
      <pre>{html.escape(lean_source)}</pre>
      <p class="remark"><strong>Remark:</strong> {remark_html(lean_note)}</p>
    </section>
  </div>
</article>"""


def render_html(
    matches: list[tuple[ManuscriptItem, LeanItem | None, float]],
    manuscript_path: Path,
    threshold: float,
) -> str:
    rows: list[str] = []
    current_part = ""
    for manuscript, lean, score in matches:
        if manuscript.part != current_part:
            current_part = manuscript.part
            rows.append(f'<h2 id="part-{current_part.lower()}">Part {current_part}</h2>')
        title = manuscript.title or manuscript.label or f"unnamed {manuscript.kind}"
        manuscript_note, lean_note = combined_remarks(manuscript, lean, score, threshold)
        lean_location = (
            f"{lean.file}:{lean.line} · "
            + ("curated correspondence" if score == 1.0 else f"match score {score:.2f}")
            if lean else f"No match · best score {score:.2f}"
        )
        lean_name = lean.name if lean else "No Lean counterpart found"
        lean_source = lean.source if lean else "(none)"
        group = status_group(manuscript, lean)
        ledger_status = lean.status if lean and lean.status else "unmatched"
        rows.append(html_article(
            manuscript.index, title, group, ledger_status,
            manuscript.kind, manuscript.label,
            f"{manuscript_path.as_posix()}:{manuscript.line}",
            manuscript.source, manuscript_note,
            lean_name, lean_location, lean_source, lean_note,
        ))
    matched = sum(lean is not None for _, lean, _ in matches)
    complete = sum(
        status_group(manuscript, lean) == "complete"
        for manuscript, lean, _ in matches
    )
    open_count = sum(
        status_group(manuscript, lean) == "open"
        for manuscript, lean, _ in matches
    )
    incomplete = len(matches) - complete - open_count - (len(matches) - matched)
    navigation = " ".join(
        f'<a href="#part-{part.lower()}">Part {part}</a>' for part in "ABCDEFG"
    )
    summary = (
        f"{len(matches)} statements: {complete} complete formalizations,\n"
        f"    {incomplete} partial/conditional or special-case links, {open_count} open conjectural\n"
        f"    interfaces, and {len(matches) - matched} with no declaration. A linked declaration is\n"
        "    not automatically a complete counterpart."
    )
    return html_page("Parts A–G theorems and Lean counterparts", summary, navigation, rows)


# --------------------------------------------------------------------------
# Standalone closed-case Blueprints
#
# The page is built from the Blueprint's own dependency graph (`\uses`), so it
# shows what `leanblueprint` would draw.  Order: external inputs, then the
# final theorem, then the statements between them bottom-up, so each appears
# after everything it uses.  The final theorem is whatever `--final` names; the
# graph cannot supply it, since its sinks are often corollaries.
# --------------------------------------------------------------------------

USES_RE = re.compile(r"\\uses\{([^}]*)\}")
TITLE_RE = re.compile(r"\[([^\]]*)\]")
EXTERNAL_CSS = (
    "    .status-external .status-badge { background: color-mix(in srgb, #8a6bff 28%, Canvas); }\n"
)


CLOSED_CASE_ENVS = (
    "theorem", "lemma", "proposition", "corollary", "definition",
    "question", "conjecture",
)
CLOSED_CASE_BEGIN_RE = re.compile(
    r"\\begin\{(" + "|".join(CLOSED_CASE_ENVS) + r")\}"
)
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
LEAN_MACRO_RE = re.compile(r"\\lean\{([^}]*)\}")


def closed_case_nodes(text: str) -> list[tuple[str, str, str, int]]:
    """Every environment, as (label, lean name, marker, insertion offset).

    The insertion point is after the statement, and after the proof that
    immediately follows it when there is one -- a remark wedged between a
    statement and its proof reads badly.
    """
    nodes = []
    for match in CLOSED_CASE_BEGIN_RE.finditer(text):
        env = match.group(1)
        end_marker = rf"\end{{{env}}}"
        end = text.find(end_marker, match.end())
        if end < 0:
            raise ValueError(f"unclosed {env} at offset {match.start()}")
        end += len(end_marker)
        body = text[match.start():end]
        label_match = LABEL_RE.search(body)
        if not label_match:
            continue
        # A node with no `\lean{}` still gets a generated remark: those are
        # exactly the nodes whose Lean status is prose, and prose is what rots.
        lean_names = LEAN_MACRO_RE.findall(body)
        if len(lean_names) > 1:
            raise ValueError(
                f"{label_match.group(1)}: {len(lean_names)} \\lean{{}} macros; "
                f"a closed-case node names exactly one declaration"
            )
        lean_name = lean_names[0] if lean_names else ""
        marker = "none"
        if r"\leanok" in body:
            marker = "leanok"
        elif r"\notready" in body:
            marker = "notready"
        tail = text[end:]
        proof = re.match(r"\s*\\begin\{proof\}", tail)
        if proof:
            proof_end = text.find(r"\end{proof}", end)
            if proof_end < 0:
                raise ValueError(f"unclosed proof after {label_match.group(1)}")
            end = proof_end + len(r"\end{proof}")
        nodes.append((label_match.group(1), lean_name, marker, end))
    return nodes


# One fully qualified declaration name.  leanblueprint itself accepts
# `\lean{A, B}`, but the ledger's `lean` field and the side-by-side page each
# resolve exactly one name: `\lean{A, B}` matched the ledger here as a string
# and then matched nothing on the page (prop:unate, for one commit).
LEAN_NAME_RE = re.compile(r"[A-Za-z_][\w'.]*")


def check_lean_names(
    named: list[tuple[str, str, bool]], source: Path, known: set[str], lean_dir: Path
) -> int:
    """Refuse a named Lean counterpart that is not one name, or is declared nowhere.

    `named` is (label, name, claimed) triples, `claimed` meaning the node is
    `\\leanok`; empty names are skipped.  `known` is the set of qualified
    declaration names `extract_lean` reads from
    `lean_dir`.  Comparing the Blueprint against the ledger as strings let
    `lem:onecapture` go green naming a declaration that did not exist.

    A malformed name, or a `\\leanok` node whose name resolves to nothing, is
    fatal.  An unclaimed node naming nothing already renders as an error card,
    so it is reported on stderr rather than blocking every page after it --
    and the count of those is **returned**, so a caller that regenerates
    several pages can still fail at the end.  Printing to stderr and returning
    normally is what let a caller exit 0 with errors on screen.

    This is a textual scan, so it catches a typo or a wrong namespace without
    compiling anything; it does not prove the name elaborates.  A per-case
    Lean marker audit is what asks Lean.
    """
    bad, unclaimed = [], []
    for label, name, claimed in named:
        if not name:
            continue
        if not LEAN_NAME_RE.fullmatch(name):
            bad.append(f"    {label}: {name!r} is not a single Lean declaration name")
        elif name not in known:
            line = f"    {label}: {name} is declared nowhere in {lean_dir.as_posix()}/*.lean"
            (bad if claimed else unclaimed).append(line)
    if unclaimed:
        print(
            f"ERROR: {source}: {len(unclaimed)} Lean name(s) resolve to nothing:\n"
            + "\n".join(unclaimed),
            file=sys.stderr,
        )
    if bad:
        listed = "\n".join(bad)
        raise ValueError(
            f"{source}: {len(bad)} Lean counterpart(s) do not resolve:\n{listed}\n"
            f"  Name exactly one fully qualified declaration per node; list any "
            f"further ones in the ledger's 'lean_statement'."
        )
    return len(unclaimed)


@dataclass
class BlueprintNode:
    item: ManuscriptItem
    lean: str
    marker: str
    proof_marker: str
    uses: list[str]
    # (reference, locator) pairs from `\literature{..}{..}`; see
    # the project's closed-case conventions, "Literature references for external inputs".
    literature: list[tuple[str, str]]


def balanced_arguments(text: str, start: int, count: int) -> tuple[list[str], int] | None:
    """The next `count` brace groups from `start`, and the offset after them."""
    args = []
    position = start
    for _ in range(count):
        while position < len(text) and text[position] in " \t\r\n":
            position += 1
        if position >= len(text) or text[position] != "{":
            return None
        depth, end = 0, position
        while end < len(text):
            if text[end] == "\\":
                end += 2
                continue
            if text[end] == "{":
                depth += 1
            elif text[end] == "}":
                depth -= 1
                if depth == 0:
                    break
            end += 1
        if depth:
            return None
        args.append(text[position + 1:end])
        position = end + 1
    return args, position


LITERATURE_RE = re.compile(r"\\literature(?![A-Za-z])")


def literature_references(source: str) -> list[tuple[str, str]]:
    references = []
    for match in LITERATURE_RE.finditer(source):
        parsed = balanced_arguments(source, match.end(), 2)
        if parsed:
            reference, locator = (" ".join(arg.split()) for arg in parsed[0])
            references.append((reference, locator))
    return references


def extract_blueprint(path: Path) -> list[BlueprintNode]:
    """Every labelled Blueprint node, with its statement, proof and `\\uses` edges."""

    text = path.read_text(encoding="utf-8")
    # `closed_case_nodes` ends each node after its proof, before any generated
    # Lean alignment remark, so the remark is not repeated in the source column.
    parsed = {label: (lean, marker, end) for label, lean, marker, end in closed_case_nodes(text)}
    nodes: list[BlueprintNode] = []
    for match in CLOSED_CASE_BEGIN_RE.finditer(text):
        env = match.group(1)
        label_match = LABEL_RE.search(text, match.end(), text.find(rf"\end{{{env}}}", match.end()))
        if not label_match:
            continue
        label = label_match.group(1)
        lean, marker, end = parsed[label]
        source = text[match.start():end].strip()
        proof_match = re.search(r"\\begin\{proof\}(.*?)\\end\{proof\}", source, re.S)
        proof_marker = "absent"
        if proof_match:
            proof_marker = "none"
            if r"\leanok" in proof_match.group(1):
                proof_marker = "leanok"
            elif r"\notready" in proof_match.group(1):
                proof_marker = "notready"
        uses = list(dict.fromkeys(
            used.strip()
            for group in USES_RE.findall(source) for used in group.split(",") if used.strip()
        ))
        title_match = TITLE_RE.match(text, match.end())
        nodes.append(BlueprintNode(
            ManuscriptItem(
                index=0, part="", kind=env,
                title=strip_tex(title_match.group(1)) if title_match else label,
                label=label, line=line_number(text, match.start()), source=source,
            ),
            lean, marker, proof_marker, uses, literature_references(source),
        ))
    return nodes


def external_reason(node: BlueprintNode, record: dict) -> str:
    if node.item.label.startswith("ext:"):
        return "its label carries the ext: prefix"
    if record.get("status") == "external-input":
        return "its ledger status is external-input"
    if any(part.startswith("EXT_") for part in node.lean.split(".")):
        return f"its Lean name {node.lean} is EXT_-prefixed"
    return ""


def bottom_up(group: list[BlueprintNode]) -> list[BlueprintNode]:
    """Each node after every node of `group` it uses; ties keep document order."""
    labels = {node.item.label for node in group}
    emitted: set[str] = set()
    pending, ordered = list(group), []
    while pending:
        ready = next((
            node for node in pending
            if all(used in emitted or used not in labels or used == node.item.label
                   for used in node.uses)
        ), None)
        if ready is None:
            raise ValueError("\\uses cycle among: " + ", ".join(n.item.label for n in pending))
        ordered.append(ready)
        emitted.add(ready.item.label)
        pending.remove(ready)
    return ordered


def closed_case_sections(
    nodes: list[BlueprintNode], ledger: dict, finals: list[str]
) -> list[tuple[str, str, list[BlueprintNode]]]:
    by_label = {node.item.label: node for node in nodes}
    unknown = [label for label in finals if label not in by_label]
    if unknown:
        raise ValueError(f"--final names labels that are not Blueprint nodes: {unknown}")
    external = {
        node.item.label for node in nodes
        if node.item.label not in finals and external_reason(node, ledger.get(node.item.label, {}))
    }
    rest = [n for n in nodes if n.item.label not in finals and n.item.label not in external]
    definitions = [n for n in rest if n.item.kind == "definition"]
    rest = [n for n in rest if n.item.kind != "definition"]
    needed: set[str] = set()
    stack = list(finals)
    while stack:
        for used in by_label[stack.pop()].uses:
            if used in by_label and used not in needed:
                needed.add(used)
                stack.append(used)
    sections = [
        ("external", "External inputs", [n for n in nodes if n.item.label in external]),
        ("final", "Final theorem", [by_label[label] for label in finals]),
        ("definitions", "Definitions", bottom_up(definitions)),
        ("middle", "Middle statements",
         bottom_up([n for n in rest if not finals or n.item.label in needed])),
    ]
    unused = [n for n in rest if finals and n.item.label not in needed]
    if unused:
        sections.append(("unused", "Not used by the final theorem", bottom_up(unused)))
    return sections


def check_leanok_has_counterpart(
    nodes: list[BlueprintNode], ledger: dict, blueprint: Path
) -> None:
    """Refuse a `\\leanok` node that names no Lean declaration.

    Such a node renders as complete on this page and green in the dependency
    graph while nothing in the development is checked against it, and the
    marker audits cannot catch it: their rules all begin by looking a
    declaration up, so an entry with `"lean": null` is skipped before any of
    them runs.  The Blueprint generator rejects the combination
    when the remarks are generated; this page is built from the same two
    sources and refuses it here too, so the error surfaces without Lean being
    compiled at all.

    The fix is a declaration, not a quieter marker, whenever the content is
    formalisable.
    """
    bad = []
    for node in nodes:
        record = ledger.get(node.item.label, {})
        ledger_lean = record.get("lean")
        if node.lean or (isinstance(ledger_lean, str) and ledger_lean.strip()):
            continue
        claimed = node.marker == "leanok" or record.get("marker") == "leanok"
        if claimed or record.get("status") == "full":
            claim = "\\leanok" if claimed else 'ledger status "full"'
            bad.append(f"    {node.item.label} (line {node.item.line}): {claim}")
    if bad:
        listed = "\n".join(bad)
        raise ValueError(
            f"{blueprint}: {len(bad)} node(s) claim formalisation with no Lean "
            f"counterpart:\n{listed}\n"
            f"  A node with no declaration renders complete here and green in "
            f"the dependency graph with nothing behind it, and the marker "
            f"audits skip null-lean entries. Give it a declaration and name it "
            f"in 'lean', or drop the claim (marker 'none')."
        )


def closed_case_group(node: BlueprintNode, record: dict) -> str:
    """Choose presentation status, with the Blueprint marker authoritative."""
    if node.marker == "notready":
        return "error"
    if node.marker == "leanok":
        if proof_required(node) and node.proof_marker != "leanok":
            return "error" if node.proof_marker == "notready" else "proof-missing"
        return "complete"
    return "incomplete"


def proof_required(node: BlueprintNode) -> bool:
    return node.item.kind in {"theorem", "lemma", "proposition", "corollary"}


def closed_case_badge(
    node: BlueprintNode, record: dict, lean_name: str, lean: LeanItem | None,
) -> str:
    """Give readiness failures an explicit badge instead of a theorem-kind label."""
    if node.marker == "notready":
        detail = "; no Lean counterpart" if not lean_name else ""
        return rf"ERROR: Blueprint \notready{detail}"
    if not lean_name:
        marker = (
            ""
            if node.marker == "leanok"
            else r"INCOMPLETE: Blueprint has no \leanok marker; "
        )
        return marker + "ERROR: no Lean counterpart"
    if lean is None:
        marker = (
            ""
            if node.marker == "leanok"
            else r"INCOMPLETE: Blueprint has no \leanok marker; "
        )
        return marker + f"ERROR: Lean declaration not found: {lean_name}"
    if node.marker == "leanok" and proof_required(node):
        if node.proof_marker == "notready":
            return r"ERROR: Blueprint proof is \notready"
        if node.proof_marker != "leanok":
            reason = (
                "no proof environment" if node.proof_marker == "absent"
                else r"proof has no \leanok marker"
            )
            return f"INCOMPLETE: {reason} (empty Blueprint node)"
        return r"Blueprint: statement and proof \leanok"
    if node.marker == "leanok":
        return r"Blueprint: \leanok"
    ledger_status = f"; ledger: {record['status']}" if record.get("status") else ""
    return rf"INCOMPLETE: Blueprint has no \leanok marker{ledger_status}"


# The Lean-only definitions and lemmas are always written into the page; these
# two checkboxes decide whether they are displayed, by toggling a body class.
TOGGLE_DRIVER = (
    "function syncRefs() {"
    "var on = {'lean-ref-def': document.body.classList.contains('show-lean-defs'),"
    "'lean-ref-lemma': document.body.classList.contains('show-lean-lemmas')};"
    "document.querySelectorAll('.refs').forEach(function (list) {"
    "var shown = Array.prototype.filter.call(list.children, function (item) {"
    "return !item.classList.contains('lean-ref-def') && "
    "!item.classList.contains('lean-ref-lemma') || "
    "on[item.classList.contains('lean-ref-def') ? 'lean-ref-def' : 'lean-ref-lemma']; });"
    "list.toggleAttribute('data-empty', shown.length === 0); }); }"
    "document.querySelectorAll('.toggles input').forEach(function (box) {"
    "box.addEventListener('change', function () {"
    "document.body.classList.toggle(box.dataset.bodyClass, box.checked); syncRefs(); }); });"
    "syncRefs();"
)


def toggle_checkbox(body_class: str, label: str, checked: bool) -> str:
    state = " checked" if checked else ""
    return (
        f'<label><input type="checkbox" data-body-class="{body_class}"{state}> '
        f"{html.escape(label)}</label>"
    )


LEAN_COMMENT_RE = re.compile(r"/-.*?-/|--[^\n]*", re.S)
LEAN_IDENT_RE = re.compile(r"[A-Za-z_][\w'.]*")
EXTERNAL_KEYS = ("external",)


def lean_kind(item: LeanItem) -> str:
    match = LEAN_ANY_DECL.search(LEAN_COMMENT_RE.sub("", item.source))
    return match.group("kw") if match else ""


def is_ext_name(name: str) -> bool:
    return any(part.startswith("EXT_") for part in name.split("."))


def lean_references(lean_items: list[LeanItem]) -> dict[str, set[str]]:
    """The declarations each declaration mentions, resolved textually.

    Comments are dropped first, so a docstring naming a declaration is not a
    use.  A short name resolves by suffix; when several declarations share it,
    those in the referring declaration's namespace win, and a name that is
    still ambiguous is skipped rather than guessed.
    """
    by_suffix: dict[str, set[str]] = {}
    for item in lean_items:
        parts = item.name.split(".")
        for start in range(len(parts)):
            by_suffix.setdefault(".".join(parts[start:]), set()).add(item.name)
    graph: dict[str, set[str]] = {}
    for item in lean_items:
        space = item.name.rpartition(".")[0]
        refs = graph.setdefault(item.name, set())
        for token in set(LEAN_IDENT_RE.findall(LEAN_COMMENT_RE.sub("", item.source))):
            candidates = by_suffix.get(token, set()) - {item.name}
            if len(candidates) > 1 and space:
                candidates = {c for c in candidates if c.startswith(space + ".")} or candidates
            if len(candidates) == 1:
                refs |= candidates
    return graph


# `LEAN_ANY_DECL` reads the sources textually, so a docstring line that begins
# "theorem in this repository ..." parses as a declaration named `in`.  Such a
# name is never a real declaration and must not become a card or a link target.
LEAN_KEYWORDS = frozenset({
    "in", "at", "with", "from", "by", "do", "then", "else", "fun", "let", "where", "if",
})
DEF_KINDS = ("def", "abbrev", "structure", "class", "inductive", "instance")
LEMMA_KINDS = ("theorem", "lemma", "alias")


def reachable_decls(
    roots: dict[str, list[str]], graph: dict[str, set[str]]
) -> dict[str, list[str]]:
    """Every declaration reachable from a root declaration, with the labels reaching it."""
    users: dict[str, list[str]] = {}
    for root, labels in roots.items():
        seen, stack = {root}, [root]
        while stack:
            for ref in graph.get(stack.pop(), ()):
                if ref not in seen:
                    seen.add(ref)
                    stack.append(ref)
        for name in sorted(seen - {root}):
            bucket = users.setdefault(name, [])
            bucket.extend(label for label in labels if label not in bucket)
    return users


def ext_users(roots: dict[str, list[str]], graph: dict[str, set[str]]) -> dict[str, list[str]]:
    """Every EXT_ declaration reachable from a root declaration, with the labels reaching it."""
    return {
        name: labels for name, labels in reachable_decls(roots, graph).items()
        if is_ext_name(name)
    }


# The header checkboxes that show or hide the cards for Lean declarations with
# no Blueprint node.  The card is always written; `.toggles` in the page CSS
# hides it unless `<body>` carries the matching class, so toggling costs no
# regeneration.
TOGGLE_DRIVER = (
    "document.querySelectorAll('.toggles input').forEach(function(box){"
    "function apply(){document.body.classList.toggle(box.dataset.cls,box.checked);}"
    "box.addEventListener('change',apply);apply();});"
)


def toggle_checkbox(css_class: str, label: str, checked: bool) -> str:
    """One header checkbox driving `css_class` on `<body>`."""
    return (
        f'<label><input type="checkbox" data-cls="{html.escape(css_class)}"'
        + (" checked" if checked else "")
        + f"> {html.escape(label)}</label>"
    )


FOOTPRINT_NAME = "axiom_footprint.json"

# Diagnostics printed to stderr during page generation.  They used to be
# printed and then forgotten: the script exited 0 with "ERROR: ..." on screen,
# so no CI step calling it could gate on them.  Counted here and turned into
# the exit status by `main`, unless `--allow-page-errors` says otherwise.
PAGE_ERRORS = 0


def load_footprint(lean_dir: Path) -> dict[str, dict]:
    """Per-declaration proof and statement dependencies, or `{}` if not emitted.

    Written by the project's Lean axiom-audit exporter.
    Absence is reported on the page rather than treated as cleanliness: a
    missing footprint means the check did not run, which must not look like
    "nothing depends on anything unproved".
    """
    path = lean_dir / FOOTPRINT_NAME
    if not path.exists():
        return {}
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
        return report if isinstance(report, dict) else {}
    except (OSError, ValueError):
        return {}


def dependency_gaps(
    name: str, footprint: dict[str, dict], declared: bool = False
) -> list[str]:
    """Why `name` is not unconditional, as sentences; empty when it is.

    The two fields answer different questions and neither implies the other.
    `axioms` is what the proof rests on -- a `sorry` reached through a `_deps`
    module, or a project axiom.  `assumes` is what the statement is conditional
    on: a theorem of the form `(h : CONJ_x ...) -> ...` is proved, is
    axiom-clean, and still establishes nothing until CONJ_x is.  That second
    shape is the preferred one for an unproved dependency, so a check that
    only looked at axioms would call the most conditional results in the
    development unconditional.
    """
    record = footprint.get(name)
    if record is None:
        if declared and footprint:
            return [
                f"Not covered by lean/{FOOTPRINT_NAME}, which predates this "
                "declaration; what it rests on is unknown until the footprint is "
                "re-emitted"
            ]
        return []
    gaps = []
    if record.get("axioms"):
        gaps.append("Proof depends on " + ", ".join(record["axioms"]))
    if record.get("assumes"):
        gaps.append("Statement is conditional on " + ", ".join(record["assumes"]))
    return gaps


def render_closed_case_html(
    sections: list[tuple[str, str, list[BlueprintNode]]],
    blueprint_path: Path,
    lean_items: list[LeanItem],
    ledger: dict,
    lean_dir: Path,
    with_defs: bool = True,
    with_lemmas: bool = True,
) -> str:
    by_name = {item.name: item for item in lean_items}
    footprint = load_footprint(lean_dir)
    audit = read_audit(lean_dir.parent)
    nodes = [node for _, _, group in sections for node in group]
    labels = {node.item.label for node in nodes}
    used_by: dict[str, list[str]] = {}
    for node in nodes:
        for used in node.uses:
            used_by.setdefault(used, []).append(node.item.label)

    def lean_name_of(node: BlueprintNode) -> str:
        record = ledger.get(node.item.label, {})
        return (record["lean"] if "lean" in record else node.lean) or ""

    consistency = blueprint_consistency(
        nodes, {node.item.label: lean_name_of(node) for node in nodes}, audit,
    )

    roots: dict[str, list[str]] = {}
    for node in nodes:
        if lean_name_of(node) in by_name:
            roots.setdefault(lean_name_of(node), []).append(node.item.label)
    graph = lean_references(lean_items)
    reachable = reachable_decls(roots, graph)
    # An `alias` imports no statement: it is a second name for a declaration
    # the page already reaches, so an `EXT_` alias is a naming device and not
    # an external input.  Carding it under "External inputs" made the page say
    # the closed case uses something it does not prove, which is what that
    # section means.  It is carded with the definitions instead.
    ext_aliases = {
        name for name, item in ((n, by_name.get(n)) for n in reachable)
        if is_ext_name(name) and name not in roots
        and item is not None and lean_kind(item) == "alias"
    }
    ext_used = {
        name: labels for name, labels in reachable.items()
        if is_ext_name(name) and name not in ext_aliases
    }

    def lean_only_of(kinds: tuple[str, ...]) -> list[str]:
        """Reachable declarations of these Lean kinds that the Blueprint gives no node."""
        return sorted(
            name for name, item in ((n, by_name.get(n)) for n in reachable)
            if item is not None and name not in roots and not is_ext_name(name)
            and name not in LEAN_KEYWORDS and lean_kind(item) in kinds
        )

    # Both groups are written by default and shown, with a header checkbox that
    # hides each again.  `--no-lean-defs` / `--no-lean-lemmas` leave a group out
    # of the page altogether -- the sources of a few hundred declarations are
    # megabytes, hidden or not -- and then its declarations appear in no
    # reference list either, so no card links to something that is not there.
    lean_only_defs = sorted(set(lean_only_of(DEF_KINDS)) | ext_aliases) if with_defs else []
    lean_only_lemmas = lean_only_of(LEMMA_KINDS) if with_lemmas else []

    # External inputs: the Blueprint's external nodes, then every EXT_
    # declaration that some declaration on this page reaches in Lean without
    # the Blueprint giving it a node.
    lean_only = [name for name in sorted(ext_used) if name not in roots]
    extra = {
        "external": lean_only,
        "definitions": lean_only_defs,
        "middle": lean_only_lemmas,
    }
    layout: list[tuple[str, str, list]] = [
        (key, heading, group + extra.get(key, []))
        for key, heading, group in sections
    ]

    # Lean-level references, restricted to declarations that have a card here so
    # that both directions resolve to an anchor on this page.
    carded = set(roots) | set(lean_only) | set(lean_only_defs) | set(lean_only_lemmas)
    def_names, lemma_names = set(lean_only_defs), set(lean_only_lemmas)
    lean_uses = {name: sorted(graph.get(name, set()) & carded) for name in carded}
    lean_used_by: dict[str, list[str]] = {name: [] for name in carded}
    for name in sorted(carded):
        for used in lean_uses[name]:
            lean_used_by[used].append(name)

    # Anchors every remark can link to: Blueprint labels, and the Lean names of
    # the declarations carded on this page.
    anchors = {label: f"node-{label}" for label in labels}
    # Only namespaced Lean names are linked: a bare name such as `Nat` would
    # otherwise turn every mention of the word in a remark into a link.
    for name in sorted(carded):
        if "." in name:
            anchors.setdefault(name, f"lean-{name}")
    for node in nodes:
        if lean_name_of(node) in carded:
            anchors[lean_name_of(node)] = f"node-{node.item.label}"
    anchor_re = re.compile(
        r"(?<![\w:.-])("
        + "|".join(map(re.escape, sorted(anchors, key=len, reverse=True)))
        # A trailing "." ends the sentence; only a "." that continues an
        # identifier means the match was a prefix of a longer name.
        + r")(?![\w:-])(?![.][A-Za-z_])"
    ) if anchors else None

    def linked(text: str) -> str:
        """Escape remark text and link every Blueprint label and carded Lean name in it."""
        escaped = html.escape(text)
        if anchor_re is None:
            return escaped
        return anchor_re.sub(
            lambda m: f'<a href="#{anchors[m.group(1)]}">{m.group(1)}</a>', escaped
        )

    def named_statement(name: str) -> str:
        """Show a named proposition's source beside the theorem proving it.

        Resolve the fully qualified compiled type, never an ambiguous short
        identifier guessed from the proof text. The source remains verbatim.
        """
        item = by_name.get(name)
        if audit.state != "current" or item is None or lean_kind(item) not in LEMMA_KINDS:
            return ""
        type_name = audit.details.get(name, {}).get("type", "").strip()
        definition = by_name.get(type_name)
        if definition is None or lean_kind(definition) not in ("def", "abbrev"):
            return ""
        if audit.details.get(type_name, {}).get("type", "").strip() != "Prop":
            return ""
        return (
            '<div class="named-statement"><h5>Statement definition</h5>'
            f'<p><code>{linked(type_name)}</code></p>'
            '<p>The theorem below proves this named proposition. Its source name '
            'is preserved; proof status is reported separately.</p>'
            f'<pre>{html.escape(definition.source)}</pre>'
            f'<p class="meta">{html.escape(definition.file)}:{definition.line}</p></div>'
        )

    def ref_list(names: list[str]) -> str:
        """A reference list whose entries carry the class of the card they point at.

        A reference to a hidden Lean-only card is hidden with it, so an
        unticked checkbox removes those declarations from the page completely
        rather than leaving links to cards that are not there.
        """
        if not names:
            return '<span class="refs" data-empty></span>'
        items = []
        for name in names:
            kind = ("lean-ref-def" if name in def_names
                    else "lean-ref-lemma" if name in lemma_names else "")
            anchor = anchors.get(name)
            text = html.escape(name)
            inner = f'<a href="#{anchor}">{text}</a>' if anchor else text
            items.append(f'<span class="ref {kind}">{inner}</span>')
        return '<span class="refs">' + "".join(items) + "</span>"

    def lean_two_way(name: str) -> str:
        return (
            "Uses in Lean: " + ref_list(lean_uses.get(name, [])) + " "
            "Used in Lean by: " + ref_list(lean_used_by.get(name, []))
        )

    rows: list[str] = []
    missing: list[str] = []
    conditional: list[BlueprintNode] = []
    index = 0
    for key, heading, entries in layout:
        rows.append(f'<h2 id="{key}">{heading}</h2>')
        if key == "final" and not entries:
            rows.append(
                '<p class="remark">No final theorem was specified (<code>--final LABEL</code>), '
                "so every node that is not an external input or a definition is listed as a "
                "middle statement.</p>"
            )
        for entry in entries:
            index += 1
            if isinstance(entry, str):
                lean = by_name[entry]
                lean_only_group = {
                    "external": "external",
                    "definitions": "lean-only-def",
                }.get(key, "lean-only-lemma")
                blueprint_notes = ["Not a Blueprint node."]
                blueprint_notes.extend(
                    f"{gap}." for gap in dependency_gaps(entry, footprint, declared=True)
                )
                if entry in ext_used:
                    blueprint_notes.append(
                        "Reached from Blueprint nodes: " + ", ".join(ext_used[entry]) + "."
                    )
                rows.append(html_article(
                    index, entry, lean_only_group,
                    f"Lean {lean_kind(lean)}",
                    "Lean only", "", "not a Blueprint node",
                    "(this declaration has no Blueprint node)",
                    linked(" ".join(blueprint_notes)) + " " + lean_two_way(entry),
                    entry, f"{lean.file}:{lean.line}", lean.source,
                    linked(
                        "Found by following identifier references through the Lean sources, "
                        "starting from the declarations on this page. References are read "
                        "textually, not elaborated."
                    ),
                    left_heading="Blueprint", anchor=f"lean-{entry}", remark_html=str,
                    lean_extra=named_statement(entry) + hypothesis_panel(entry, audit),
                ))
                continue
            node = entry
            label = node.item.label
            record = ledger.get(label, {})
            lean_name = lean_name_of(node)
            lean = by_name.get(lean_name) if lean_name else None
            if key in EXTERNAL_KEYS:
                # External proof absence is expected, but its statement must
                # still be registered and marked as aligned with Lean.
                group = {
                    "leanok": "external",
                    "notready": "error",
                }.get(node.marker, "incomplete")
            else:
                group = closed_case_group(node, record)
            notes = []
            if key in EXTERNAL_KEYS:
                notes.append(f"External input: {external_reason(node, record)}.")
                if not node.literature:
                    notes.append(
                        "No \\literature reference: the closed-case conventions require one, "
                        "with an exact locator, on every external input."
                    )
                elif not all(locator for _, locator in node.literature):
                    notes.append("A \\literature reference has no locator (theorem or equation number).")
            for reference, locator in node.literature:
                notes.append(f"Source: {tex_plain(literature_text(reference, locator or '(no locator)'))}.")
            notes.append(f"Blueprint marker: {node.marker}.")
            if proof_required(node):
                notes.append(f"Blueprint proof marker: {node.proof_marker}.")
            notes.append("Uses: " + (", ".join(node.uses) or "nothing") + ".")
            notes.append("Used by: " + (", ".join(used_by.get(label, [])) or "nothing") + ".")
            if lean_name in ext_used:
                notes.append("Reached from Blueprint nodes: " + ", ".join(ext_used[lean_name]) + ".")
            dangling = [used for used in node.uses if used not in labels]
            if dangling:
                notes.append("These \\uses name no Blueprint node: " + ", ".join(dangling) + ".")
            lean_notes = [record.get("lean_remark", "")]
            if record.get("lean_statement"):
                lean_notes.append(f"Lean statement: {record['lean_statement']}")
            if not lean_name:
                group = "error"
                lean_notes.insert(0, "The Blueprint names no Lean declaration for this node.")
            elif lean is None:
                missing.append(lean_name)
                group = "error"
                lean_notes.insert(0, f"{lean_name} was not found in {lean_dir.as_posix()}/*.lean.")
            # A \leanok node whose declaration is not unconditional is not
            # complete, whatever the marker says: the Blueprint records that a
            # formalisation exists, not what it rests on.  External inputs keep
            # their own status -- resting on an assumed published theorem is
            # what they are for -- but still report what that assumption is.
            gaps = (
                dependency_gaps(lean_name, footprint, declared=lean is not None)
                if lean_name else []
            )
            if gaps and key not in EXTERNAL_KEYS and group == "complete":
                group = "conditional"
                conditional.append(node)
            notes.extend(f"{gap}." for gap in gaps)
            badge = (
                "EXTERNAL-INPUT: Lean statement matched; proof supplied externally"
                if key in EXTERNAL_KEYS and node.marker == "leanok" and lean is not None
                else f"CONDITIONAL: {gaps[0]}" if group == "conditional"
                else closed_case_badge(node, record, lean_name, lean)
            )
            difference = consistency[label]["state"] == "review"
            notice_id = html.escape(f"dependency-{label}", quote=True)
            difference_messages = []
            for field, description in (
                ("unseen", "Blueprint dependencies not found in this Lean declaration's compiled dependency chain"),
                ("undocumented", "Lean dependencies with no documented Blueprint path"),
                ("unknown", "Blueprint references with no matching node"),
            ):
                affected = consistency[label][field]
                if affected:
                    links = ", ".join(
                        f'<a href="#node-{html.escape(target, quote=True)}">{html.escape(target)}</a>'
                        if target in labels else html.escape(target) for target in affected
                    )
                    difference_messages.append(f"<p>{description}: {links}.</p>")
            notice = (
                f'<aside class="dependency-notice" id="{notice_id}">'
                '<strong>Dependency difference</strong>' + "".join(difference_messages)
                + '<p>This compares the mapped declarations, not proof validity. '
                  'Specialized lemmas, separate proofs, or a node with several conclusions can explain a difference.</p></aside>'
            ) if difference else ""
            rows.append(html_article(
                index, node.item.title, group,
                badge,
                node.item.kind, label, f"{blueprint_path.as_posix()}:{node.item.line}",
                node.item.source,
                linked(" ".join(notes))
                + (" " + lean_two_way(lean_name) if lean_name in carded else ""),
                lean_name or "No Lean declaration",
                f"{lean.file}:{lean.line}" if lean else "not found",
                lean.source if lean else "(none)",
                linked(" ".join(filter(None, lean_notes)) or "No ledger remark."),
                left_heading="Blueprint", anchor=f"node-{label}", remark_html=str,
                typeset=tex_to_markdown(node.item.source, labels),
                lean_extra=named_statement(lean_name) + hypothesis_panel(lean_name, audit)
                + ("" if difference else consistency_panel(consistency[label])),
                extra_badge=(f' <a class="dependency-badge" href="#{notice_id}">Dependency difference</a>'
                             if difference else ""),
                notice_html=notice,
            ))
    counts = {key: len(entries) for key, _, entries in layout}
    finals = [node.item.label for key, _, group in sections if key == "final" for node in group]
    unsourced = [
        node for node in next(group for key, _, group in sections if key == "external")
        if not node.literature or not all(locator for _, locator in node.literature)
    ]
    external_labels = {
        node.item.label
        for key, _, group in sections if key == "external" for node in group
    }
    notready = [node for node in nodes if node.marker == "notready"]
    no_counterpart = [
        node for node in nodes if not lean_name_of(node)
    ]
    proof_gaps = [
        node for node in nodes
        if node.item.label not in external_labels
        and node.marker == "leanok" and proof_required(node)
        and node.proof_marker != "leanok"
    ]
    marker_gaps = [
        node for node in nodes
        if node.marker not in {"leanok", "notready"}
    ]
    errors = []
    if notready:
        errors.append(
            r"ERROR: Blueprint \notready on "
            + ", ".join(linked(node.item.label) for node in notready)
            + "."
        )
    if no_counterpart:
        errors.append(
            "ERROR: no Lean counterpart for "
            + ", ".join(linked(node.item.label) for node in no_counterpart)
            + "."
        )
    if missing:
        errors.append(
            "ERROR: named Lean declarations not found: "
            + ", ".join(f"<code>{html.escape(name)}</code>" for name in sorted(set(missing)))
            + "."
        )
    error_summary = "".join(
        f'<strong class="error-summary">{message}</strong>' for message in errors
    )
    warnings = []
    if not footprint:
        warnings.append(
            f"NOT CHECKED: lean/{FOOTPRINT_NAME} is absent, so no card on this page has "
            "been checked for what it rests on. Regenerate it with the project's "
            "Lean axiom-audit exporter."
        )
    if conditional:
        warnings.append(
            "CONDITIONAL: proved, but not unconditional -- the proof rests on an axiom or "
            "a <code>sorry</code>, or the statement carries an unproved hypothesis -- for "
            + ", ".join(linked(node.item.label) for node in conditional)
            + "."
        )
    if marker_gaps:
        warnings.append(
            r"INCOMPLETE: Blueprint statement has no <code>\leanok</code> marker for "
            + ", ".join(linked(node.item.label) for node in marker_gaps)
            + "."
        )
    if proof_gaps:
        warnings.append(
            '<strong class="warning-summary">INCOMPLETE: proof not marked '
            r'<code>\leanok</code> (empty Blueprint node) for '
            + ", ".join(linked(node.item.label) for node in proof_gaps)
            + ".</strong>"
        )
    warning_summary = "".join(
        message if message.startswith("<strong")
        else f'<strong class="warning-summary">{message}</strong>'
        for message in warnings
    )
    summary = (
        f"{len(nodes)} Blueprint nodes from <code>{html.escape(blueprint_path.as_posix())}</code>: "
        f"{counts['external']} external inputs ({len(lean_only)} of them reached only in Lean), "
        "final theorem "
        + (", ".join(linked(label) for label in finals) if finals else "not specified")
        + f", {counts['definitions']} definitions"
        + (f" ({len(lean_only_defs)} of them reached only in Lean)" if lean_only_defs else "")
        + f", {counts['middle']} middle statements"
        + (f" ({len(lean_only_lemmas)} of them reached only in Lean)" if lean_only_lemmas else "")
        + (f", {counts['unused']} not used by the final theorem" if "unused" in counts else "")
        + f". {len(missing)} named Lean declarations were not found. "
        + (
            f"<strong>The saved audit flags {len(conditional)} statements as conditional.</strong> "
            if footprint else
            f"Dependencies unchecked: lean/{FOOTPRINT_NAME} is absent. "
        )
        + f"{len(unsourced)} external inputs lack a \\literature reference with a locator. "
        "Middle statements are in "
        "dependency order: each appears after every node it uses. "
        '<span id="tex-status"></span>'
        + error_summary
        + warning_summary
    )
    navigation = " ".join(f'<a href="#{key}">{heading}</a>' for key, heading, _ in layout)
    navigation += ' <a href="lean_dump_about.html">About the Lean checks</a>'
    toggles = "".join(
        toggle_checkbox(body_class, f"{text} ({len(group)})", True)
        for body_class, text, group in (
            ("show-lean-defs", "Lean-only definitions", lean_only_defs),
            ("show-lean-lemmas", "Lean-only lemmas", lean_only_lemmas),
        ) if group
    )
    if toggles:
        navigation += (
            f'<span class="toggles">{toggles}</span><script>{TOGGLE_DRIVER}</script>'
        )
    title = html.escape(f"{blueprint_path.stem}: Blueprint nodes and Lean counterparts")
    css = (
        EXTERNAL_CSS
        + "    .audit-checks { margin: .6rem 0; padding: .65rem; border: 1px solid #b98927; border-radius: .35rem; overflow-wrap: anywhere; }\n"
        + "    .audit-checks[open] { max-height: 50vh; overflow: auto; }\n"
        + "    .dependency-badge { display: inline-block; padding: .2rem .55rem; border: 1px solid #b98927; border-radius: .3rem; background: #fff1cc; color: #624000; font-size: .85rem; text-decoration: none; }\n"
        + "    .dependency-notice { margin: .6rem 0; padding: .65rem .9rem; border-left: 4px solid #b98927; background: color-mix(in srgb, #dba844 12%, Canvas); overflow-wrap: anywhere; scroll-margin-top: 14rem; }\n"
        + "    .dependency-notice p { margin: .35rem 0; }\n"
        + "    .named-statement { margin: .7rem 0; padding: .75rem; border: 1px solid #708da3; border-radius: .35rem; background: color-mix(in srgb, #4b98c2 7%, Canvas); }\n"
        + "    .named-statement h5 { margin: 0 0 .4rem; font-size: 1rem; }\n"
        + "    .named-statement p { margin: .4rem 0; overflow-wrap: anywhere; }\n"
        + "    .audit-current { border-color: #2fa866; }\n"
        + "    .audit-checks summary { font-size: 1rem; font-weight: 600; opacity: 1; }\n"
        + "    .audit-note { font-size: .9rem; }\n"
        + "    .hypotheses, .consistency { margin-bottom: .6rem; overflow-wrap: anywhere; }\n"
        + "    article { scroll-margin-top: 11rem; }\n"
        + "    .status-complete section { border-left: 3px solid #2fa866; "
          "background: color-mix(in srgb, #2fa866 4%, Canvas); }\n"
        + "    .status-error .status-badge, .status-unmatched .status-badge { "
          "background: color-mix(in srgb, #d83232 30%, Canvas); }\n"
        + "    .status-error section, .status-unmatched section:last-child { "
          "border-color: #d83232; background: color-mix(in srgb, #d83232 6%, Canvas); }\n"
        + "    .status-conditional .status-badge { "
          "background: color-mix(in srgb, #2f6fd0 30%, Canvas); }\n"
        + "    .status-conditional section { border-color: #2f6fd0; "
          "background: color-mix(in srgb, #2f6fd0 7%, Canvas); }\n"
        + "    .status-proof-missing .status-badge { "
          "background: color-mix(in srgb, #e8a832 30%, Canvas); }\n"
        + "    .status-proof-missing section { border-color: #e8a832; "
          "background: color-mix(in srgb, #e8a832 6%, Canvas); }\n"
        + "    .error-summary { display: block; margin-top: .65rem; padding: .6rem; "
          "border: 2px solid #d83232; border-radius: .35rem; "
          "background: color-mix(in srgb, #d83232 9%, Canvas); }\n"
        + "    .warning-summary { display: block; margin-top: .65rem; padding: .6rem; "
          "border: 2px solid #e8a832; border-radius: .35rem; "
          "background: color-mix(in srgb, #e8a832 9%, Canvas); }\n"
        + "    .proof-summary { display: block; margin-bottom: .5rem; }\n"
        + "    .toggles { display: inline-flex; flex-wrap: wrap; gap: .3rem .8rem; margin-left: .6rem; max-width: 100%; }\n"
        + "    .toggles label { font-size: .9em; white-space: nowrap; }\n"
        + "    .refs { display: inline-flex; flex-wrap: wrap; gap: 0 .45rem; "
          "vertical-align: top; }\n"
        + "    .refs[data-empty]::after { content: 'nothing'; }\n"
        + "    body:not(.show-lean-defs) .lean-ref-def,\n"
        + "    body:not(.show-lean-lemmas) .lean-ref-lemma { display: none; }\n"
        + "    body:not(.show-lean-defs) .status-lean-only-def,\n"
        + "    body:not(.show-lean-lemmas) .status-lean-only-lemma { display: none; }\n"
        + TYPESET_CSS
    )
    body_class = " ".join(
        name for name, group in
        (("show-lean-defs", lean_only_defs), ("show-lean-lemmas", lean_only_lemmas)) if group
    )
    final_nodes = [node for node in nodes if node.item.label in finals]
    final_names = {lean_name_of(node) for node in final_nodes}
    return html_page(
        title, summary, navigation, rows, css,
        typeset_head(blueprint_preamble(blueprint_path)), body_class,
        audit_html=audit_panel(audit, consistency, proof_summary(
            audit, footprint, final_names,
            complete=bool(final_nodes) and all(
                node.marker == "leanok" and node.proof_marker == "leanok"
                and lean_name_of(node) in by_name for node in final_nodes
            ),
        )).replace("Blueprint consistency:", "Dependency comparison:")
        .replace(" to review", " dependency differences"),
    )


# --------------------------------------------------------------------------
# Typeset statements
#
# Statements are typeset in the browser by render.js from the gh-tex-viewer
# extension, a git submodule at vendor/gh-tex-viewer: it hides math
# behind placeholders, runs marked over the prose, and swaps KaTeX output back in.
# It reads Markdown with TeX, not LaTeX, so the Blueprint's text-mode markup
# (theorem environments, \label/\lean/\uses/\leanok, \cref, \emph, \texttt) is
# translated here first.  Math spans are passed through untouched.
# --------------------------------------------------------------------------

KATEX_VERSION = "0.16.11"
MARKED_VERSION = "12.0.2"
TEX_MATH_RE = re.compile(
    r"\\\[.*?\\\]|\\\(.*?\\\)|\$\$.*?\$\$|\$[^$\n]*\$"
    r"|\\begin\{(equation|align|gather|multline|aligned|cases)(\*?)\}.*?\\end\{\1\2\}",
    re.S,
)
TEX_INPUT_RE = re.compile(r"\\input\{([^}]+)\}")
TYPESET_CSS = """\
    .tex { margin-bottom: .75rem; overflow-wrap: anywhere; }
    .tex .katex-display { overflow-x: auto; overflow-y: hidden; padding: 2px 0; }
    details summary { cursor: pointer; opacity: .75; margin: .25rem 0; }
    .ghtex-matherr { background: #fff3cd; color: #7a5300; font-family: ui-monospace, Consolas, monospace; font-size: .85em; }
    .ghtex-matherr-block { display: block; padding: .4em .6em; margin: .8em 0; white-space: pre-wrap; }
    @media (prefers-color-scheme: dark) { .ghtex-matherr { background: #3a2f0b; color: #e3b341; } }
"""
TYPESET_DRIVER = """\
document.addEventListener("DOMContentLoaded", () => {
  const status = document.getElementById("tex-status");
  if (!window.katex || !window.marked) {
    if (status) status.textContent = "KaTeX could not be loaded from the CDN, so statements are shown as LaTeX source.";
    document.querySelectorAll(".tex + details").forEach((d) => { d.open = true; });
    return;
  }
  const macros = GHTeX.harvestMacros(TEX_PREAMBLE);
  let errors = 0;
  document.querySelectorAll(".tex[data-tex]").forEach((el) => {
    const out = GHTeX.render(el.dataset.tex, macros);
    el.innerHTML = out.html;
    errors += out.errors.length;
    if (out.errors.length) console.warn("[tex]", el.closest("article")?.id, out.errors);
  });
  if (status) status.textContent = errors
    ? errors + " math expression(s) failed to typeset; they are shown as source, in amber."
    : "Every statement typeset.";
});
"""


def tex_prose_to_markdown(prose: str, labels: set[str]) -> str:
    """Translate the text-mode LaTeX that Blueprint nodes use into Markdown."""
    prose = re.sub(r"(?<!\\)%[^\n]*", "", prose)
    prose = re.sub(r"\\(?:label|lean|uses|discussion)\{[^}]*\}|\\(?:leanok|notready|mathlibok)\b", "", prose)

    def begin(match: re.Match) -> str:
        env, title = match.group(1), match.group(2)
        if env == "proof":
            return "\n\n*Proof.*"
        if env in ("itemize", "enumerate"):
            return "\n"
        return f"\n\n**{env.title()}{f' ({title})' if title else ''}.** "

    prose = re.sub(r"\\begin\{(\w+)\}(?:\[([^\]]*)\])?", begin, prose)
    prose = re.sub(r"\\end\{proof\}", " ∎\n\n", prose)
    prose = re.sub(r"\\end\{\w+\}", "\n\n", prose)
    prose = re.sub(r"\\item\b\s*", "\n- ", prose)
    prose = re.sub(
        r"\\(?:[Cc]ref|ref|eqref)\{([^}]*)\}",
        lambda m: ", ".join(
            f"[{label}](#node-{label})" if label in labels else label
            for label in (part.strip() for part in m.group(1).split(","))
        ),
        prose,
    )
    prose = re.sub(
        r"\\texttt\{([^}]*)\}",
        lambda m: "`" + m.group(1).replace("\\allowbreak", "").replace("\\_", "_") + "`",
        prose,
    )
    prose = re.sub(r"\\S(?![A-Za-z])", "§", prose)
    # Accents, braced or bare, as a combining mark: \'e \'{e} \"{o} \H{o} \c{c} ...
    # This runs before `~` and `''` are replaced, since both are accent commands too.
    prose = re.sub(
        r"\\(['`^\"~=.]|[Hcvu](?![A-Za-z]))\s*(?:\{\s*([A-Za-z])\s*\}|([A-Za-z]))",
        lambda m: (m.group(2) or m.group(3)) + TEX_ACCENTS[m.group(1)],
        prose,
    )
    for tex, text in (("\\allowbreak", ""), ("---", "—"), ("--", "–"), ("``", "“"), ("''", "”"), ("~", " ")):
        prose = prose.replace(tex, text)
    # A brace group not opened by a command, as in `{\S}VII.3`, is only
    # grouping and prints nothing.
    previous = None
    while previous != prose:
        previous, prose = prose, re.sub(r"(?<![\\A-Za-z])\{([^{}]*)\}", r"\1", prose)
    # Leading indentation would make Markdown read a code block.
    return unicodedata.normalize("NFC", re.sub(r"(?m)^[ \t]+", "", prose))


TEX_ACCENTS = {
    "'": "\u0301", "`": "\u0300", "^": "\u0302", '"': "\u0308", "~": "\u0303", "=": "\u0304",
    ".": "\u0307", "H": "\u030b", "c": "\u0327", "v": "\u030c", "u": "\u0306",
}


TEX_EMPHASIS = {"emph": "*", "textit": "*", "textbf": "**"}
TEX_EMPHASIS_RE = re.compile(r"\\(emph|textit|textbf)\{")


def tex_emphasis_to_markdown(source: str) -> str:
    """`\\emph{...}` and friends, matched by balanced braces.

    This runs before math is split out, because the argument may itself hold
    math (`\\emph{General, \\(K=2C_{\\mathrm{sym}}\\).}`): split first, and the
    command is cut in two and survives as literal text.
    """
    match = TEX_EMPHASIS_RE.search(source)
    while match:
        if any(m.start() <= match.start() < m.end() for m in TEX_MATH_RE.finditer(source)):
            match = TEX_EMPHASIS_RE.search(source, match.end())
            continue
        depth, end = 1, match.end()
        while end < len(source) and depth:
            if source[end] == "\\":
                end += 2
                continue
            depth += {"{": 1, "}": -1}.get(source[end], 0)
            end += 1
        if depth:
            break
        mark = TEX_EMPHASIS[match.group(1)]
        body = source[match.end():end - 1].strip()
        source = source[:match.start()] + mark + body + mark + source[end:]
        match = TEX_EMPHASIS_RE.search(source, match.start())
    return source


def literature_text(reference: str, locator: str) -> str:
    return f"{reference}, {locator}" if locator else reference


def tex_plain(text: str) -> str:
    """Text-mode LaTeX as plain text, for remarks: markup dropped, accents and ~ resolved."""
    markdown = tex_prose_to_markdown(tex_emphasis_to_markdown(text), set())
    return " ".join(markdown.replace("*", "").replace("`", "").split())


def tex_literature_to_markdown(source: str) -> str:
    """`\\literature{ref}{locator}` as the Blueprint preamble prints it: *Source:* ref, locator."""
    parts, last = [], 0
    for match in LITERATURE_RE.finditer(source):
        parsed = balanced_arguments(source, match.end(), 2) if match.start() >= last else None
        if not parsed:
            continue
        (reference, locator), end = parsed
        parts += [source[last:match.start()], f"\n\n*Source:* {literature_text(reference, locator)}.\n\n"]
        last = end
    return "".join(parts) + source[last:]


def tex_to_markdown(source: str, labels: set[str]) -> str:
    source = tex_emphasis_to_markdown(tex_literature_to_markdown(source))
    parts, last = [], 0
    for match in TEX_MATH_RE.finditer(source):
        parts.append(tex_prose_to_markdown(source[last:match.start()], labels))
        parts.append(match.group(0))
        last = match.end()
    parts.append(tex_prose_to_markdown(source[last:], labels))
    return re.sub(r"\n{3,}", "\n\n", "".join(parts)).strip()


def blueprint_preamble(path: Path) -> str:
    """The macro definitions a Blueprint compiles with.

    A standalone document supplies its own preamble; a body file (no
    `\\begin{document}`) takes the preamble of every sibling wrapper that
    `\\input`s it.  Files a preamble `\\input`s are included too.
    """
    def preamble_of(text: str) -> str:
        head = text.split("\\begin{document}", 1)[0]
        inputs = [path.parent / (name if name.endswith(".tex") else f"{name}.tex")
                  for name in TEX_INPUT_RE.findall(head)]
        return "\n".join([head] + [f.read_text(encoding="utf-8") for f in inputs if f.exists()])

    text = path.read_text(encoding="utf-8")
    if "\\begin{document}" in text:
        return preamble_of(text)
    input_re = re.compile(r"\\input\{" + re.escape(path.stem) + r"(?:\.tex)?\}")
    return "\n".join(
        preamble_of(other_text)
        for other in sorted(path.parent.glob("*.tex")) if other != path
        for other_text in [other.read_text(encoding="utf-8")] if input_re.search(other_text)
    )


def typeset_head(preamble: str) -> str:
    cdn = "https://cdn.jsdelivr.net/npm"
    render_path = Path(__file__).resolve().parent / "vendor/gh-tex-viewer/render.js"
    if not render_path.exists():
        raise SystemExit(
            f"{render_path} is missing: the gh-tex-viewer submodule is not checked out. "
            "Run: git submodule update --init --recursive"
        )
    render_js = render_path.read_text(encoding="utf-8")
    # A JSON string is a valid JS literal; escaping "</" keeps it inside <script>.
    preamble_js = json.dumps(preamble).replace("</", "<\\/")
    return (
        f'  <link rel="stylesheet" href="{cdn}/katex@{KATEX_VERSION}/dist/katex.min.css">\n'
        f'  <script defer src="{cdn}/katex@{KATEX_VERSION}/dist/katex.min.js"></script>\n'
        f'  <script defer src="{cdn}/marked@{MARKED_VERSION}/marked.min.js"></script>\n'
        "  <script>\n" + render_js + "\n  </script>\n"
        "  <script>\nconst TEX_PREAMBLE = " + preamble_js + ";\n" + TYPESET_DRIVER + "  </script>\n"
    )


def html_page(
    title: str, summary: str, navigation: str, rows: list[str],
    extra_css: str = "", extra_head: str = "", body_class: str = "",
    audit_html: str = "",
) -> str:
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{title}</title>
  <style>
    :root {{ color-scheme: light dark; font-family: system-ui, sans-serif; }}
    html {{ scroll-padding-top: var(--header-height, 9rem); }}
    body {{ margin: 0 auto; max-width: 1800px; padding: 1.5rem; line-height: 1.45; }}
    header {{ position: sticky; top: 0; z-index: 2; padding: 1rem;
      background: Canvas; border-bottom: 1px solid color-mix(in srgb, CanvasText 25%, transparent); }}
    header h1 {{ margin: 0 0 .5rem; font-size: clamp(1.05rem, 2vw, 1.6rem); overflow-wrap: anywhere; }}
    .header-details {{ padding: 1rem; }}
    nav a {{ margin-right: .8rem; }}
    h2 {{ margin-top: 2.5rem; border-bottom: 2px solid #6b7cff; padding-bottom: .3rem; }}
    .statement {{ margin: 1.25rem 0 2rem; }}
    .status-badge {{ display: inline-block; margin-left: .5rem; padding: .12rem .45rem;
      border-radius: 999px; font-size: .72em; font-weight: 600; vertical-align: middle;
      background: color-mix(in srgb, CanvasText 10%, Canvas); }}
    .status-complete .status-badge {{ background: color-mix(in srgb, #2fa866 28%, Canvas); }}
    .status-incomplete .status-badge {{ background: color-mix(in srgb, #e8a832 28%, Canvas); }}
    .status-open .status-badge {{ background: color-mix(in srgb, #c46b32 28%, Canvas); }}
    .columns {{ display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); gap: 1rem; }}
    section {{ min-width: 0; padding: 1rem; border: 1px solid color-mix(in srgb, CanvasText 22%, transparent);
      border-radius: .6rem; }}
    .status-unmatched section:last-child {{ border-color: #c46b32; }}
    .meta {{ margin-bottom: .75rem; opacity: .8; overflow-wrap: anywhere; }}
    pre {{ margin: 0; padding: .9rem; overflow: auto; white-space: pre-wrap; overflow-wrap: anywhere;
      background: color-mix(in srgb, CanvasText 7%, Canvas); border-radius: .35rem; tab-size: 2; }}
    .remark {{ padding: .65rem; background: color-mix(in srgb, #e8a832 15%, Canvas); border-radius: .35rem; }}
    @media (max-width: 900px) {{ .columns {{ grid-template-columns: 1fr; }} }}
    @media print {{ header {{ position: static; }} .statement {{ break-inside: avoid; }} }}
{extra_css}  </style>
{extra_head}</head>
<body{f' class="{body_class}"' if body_class else ""}>
<header id="page-header">
  <h1>{title}</h1>
  <nav>{navigation}</nav>
</header>
<div class="header-details">
  {audit_html}
  <p>{summary}</p>
</div>
<main>
{''.join(rows)}
</main>
<script>
(() => {{
  const header = document.getElementById('page-header');
  const updateOffset = () => document.documentElement.style.setProperty(
    '--header-height', `${{Math.ceil(header.getBoundingClientRect().height) + 16}}px`);
  updateOffset();
  new ResizeObserver(updateOffset).observe(header);
}})();
</script>
</body>
</html>
"""


def write_closed_case_page(
    blueprint: Path, ledger_path: Path | None, finals: list[str], output: Path,
    lean_items: list[LeanItem], lean_dir: Path,
    with_defs: bool = True, with_lemmas: bool = True,
) -> None:
    nodes = extract_blueprint(blueprint)
    ledger = {
        key: value for key, value in load_overrides(ledger_path).items()
        if not key.startswith("_")
    }
    check_leanok_has_counterpart(nodes, ledger, blueprint)
    # Every node, not only the configured final: a name that does not resolve
    # used to surface on stderr only when it was the final theorem's, and was
    # otherwise just an "error" card in a page nobody had opened yet.

    global PAGE_ERRORS
    PAGE_ERRORS += check_lean_names(
        [
            (node.item.label,
             ledger.get(node.item.label, {}).get("lean", node.lean) or "",
             "leanok" in (node.marker, ledger.get(node.item.label, {}).get("marker")))
            for node in nodes
        ],
        blueprint, {item.name for item in lean_items}, lean_dir,
    )
    sections =closed_case_sections(nodes, ledger, finals)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        render_closed_case_html(
            sections, blueprint, lean_items, ledger, lean_dir, with_defs, with_lemmas
        ),
        encoding="utf-8",
    )
    print(f"Wrote {len(nodes)} Blueprint nodes to {output}: "
          + ", ".join(f"{len(group)} {heading.lower()}" for _, heading, group in sections))

    by_name = {item.name for item in lean_items}
    by_label = {node.item.label: node for node in nodes}
    final_issues = []
    for label in finals:
        node = by_label[label]
        record = ledger.get(label, {})
        lean_name = (record["lean"] if "lean" in record else node.lean) or ""
        issues = []
        if node.marker == "notready":
            issues.append(r"statement is marked \notready")
        elif node.marker != "leanok":
            issues.append(r"statement has no \leanok marker")
        if not lean_name:
            issues.append("no Lean counterpart is named")
        elif lean_name not in by_name:
            issues.append(f"Lean declaration {lean_name!r} was not found")
        if proof_required(node) and node.proof_marker != "leanok":
            issues.append(
                r"proof has no \leanok marker (empty Blueprint node)"
                if node.proof_marker != "notready"
                else r"proof is marked \notready"
            )
        if issues:
            final_issues.append(f"{label}: " + "; ".join(issues))
    if final_issues:
        # `global` is declared once, at the `check_lean_names` call above; a
        # second declaration after that assignment is a SyntaxError, and one
        # that `ast.parse` does not report -- only `compile` does.
        PAGE_ERRORS += 1
        print(
            f"ERROR: {output}: configured final theorem is not fully Lean-ready:\n  "
            + "\n  ".join(final_issues),
            file=sys.stderr,
        )


def _exit_on_page_errors(allowed: bool) -> None:
    """Turn the stderr diagnostics into an exit status.

    A page that reports an unresolved name or a final theorem that is not
    Lean-ready is a page that should not be published silently; exiting 0 with
    the reason on screen is how those two reports stayed unnoticed on master.
    `--allow-page-errors` is the deliberate override for callers that
    regenerate the known-bad pages today.
    """
    if PAGE_ERRORS and not allowed:
        print(
            f"{PAGE_ERRORS} page error(s) reported above; failing. Pass "
            f"--allow-page-errors to regenerate anyway.",
            file=sys.stderr,
        )
        raise SystemExit(1)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manuscript", type=Path, help="manuscript .tex (manuscript mode)")
    parser.add_argument("--lean-dir", type=Path, default=Path("lean"))
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--overrides", type=Path,
        help="curated JSON correspondence ledger (optional)",
    )
    parser.add_argument("--threshold", type=float, default=0.55)
    parser.add_argument("--format", choices=("markdown", "html", "json"), default="markdown")
    parser.add_argument(
        "--closed-case-pages", type=Path, metavar="CONFIG",
        help="write every closed-case page listed in CONFIG, with its Blueprint, ledger and "
             "final theorem",
    )
    parser.add_argument(
        "--blueprint", type=Path,
        help="one closed-case Blueprint .tex: write its nodes beside their Lean declarations, "
             "ordered external inputs, final theorem, middle statements bottom-up (HTML only)",
    )
    parser.add_argument(
        "--ledger", type=Path,
        help="with --blueprint: correspondence JSON keyed by Blueprint label (optional)",
    )
    parser.add_argument(
        "--allow-page-errors", action="store_true",
        help="exit 0 even when a page reported an ERROR on stderr. Without it, any "
             "'resolve to nothing' or 'final theorem is not fully Lean-ready' report "
             "makes the run fail, so a CI step can gate on it",
    )
    parser.add_argument(
        "--no-lean-defs", action="store_true",
        help="closed-case pages: do not write the Lean definitions (def, abbrev, structure, "
             "class, inductive, instance) the page's declarations reach that have no Blueprint "
             "node. They are written by default, shown, with a header checkbox that hides them "
             "again; with this they are in neither the page nor its reference lists",
    )
    parser.add_argument(
        "--no-lean-lemmas", action="store_true",
        help="closed-case pages: likewise leave out the reached Lean theorems and lemmas with "
             "no Blueprint node",
    )
    parser.add_argument(
        "--final", action="append", default=[], metavar="LABEL",
        help="with --blueprint: the final theorem's label (repeatable); omit when unknown",
    )
    args = parser.parse_args()

    if args.closed_case_pages:
        config = json.loads(args.closed_case_pages.read_text(encoding="utf-8"))
        lean_items = extract_lean(args.lean_dir, qualified=True)
        for page in config["pages"]:
            write_closed_case_page(
                Path(page["blueprint"]),
                Path(page["ledger"]) if page.get("ledger") else None,
                list(page.get("final", [])), Path(page["output"]),
                lean_items, args.lean_dir,
                not (args.no_lean_defs or page.get("no_lean_defs")),
                not (args.no_lean_lemmas or page.get("no_lean_lemmas")),
            )
        _exit_on_page_errors(args.allow_page_errors)
        return
    if args.blueprint:
        if args.format != "html":
            parser.error("--blueprint writes HTML only; pass --format html")
        if args.output is None:
            parser.error("--blueprint needs --output")
        write_closed_case_page(
            args.blueprint, args.ledger, args.final, args.output,
            extract_lean(args.lean_dir, qualified=True), args.lean_dir,
            not args.no_lean_defs, not args.no_lean_lemmas,
        )
        _exit_on_page_errors(args.allow_page_errors)
        return

    if args.manuscript is None or args.output is None:
        parser.error("manuscript mode needs --manuscript and --output")
    manuscripts = extract_manuscript(args.manuscript)
    lean_items = extract_lean(args.lean_dir)
    matches = match_items(
        manuscripts, lean_items, load_overrides(args.overrides), args.threshold
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.format == "json":
        payload = []
        for manuscript, lean, score in matches:
            manuscript_note, lean_note = combined_remarks(manuscript, lean, score, args.threshold)
            row = {
                "manuscript": asdict(manuscript),
                "lean": asdict(lean) if lean else None,
                "score": round(score, 4),
                "manuscript_remark": manuscript_note,
                "lean_remark": lean_note,
            }
            payload.append(row)
        output = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    elif args.format == "html":
        output = render_html(matches, args.manuscript, args.threshold)
    else:
        output = render_markdown(matches, args.manuscript, args.threshold)
    args.output.write_text(output, encoding="utf-8")
    matched = sum(lean is not None for _, lean, _ in matches)
    print(f"Wrote {len(matches)} statements ({matched} matched, {len(matches) - matched} unmatched) to {args.output}")


if __name__ == "__main__":
    main()
