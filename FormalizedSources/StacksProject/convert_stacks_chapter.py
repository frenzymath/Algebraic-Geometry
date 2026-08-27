#!/usr/bin/env python3
"""Convert a Stacks Project chapter .tex into a part-level blueprint fragment.

Usage:
  convert_stacks_chapter.py \\
      --src /tmp/stacks-project/schemes.tex \\
      --stem schemes \\
      --title Schemes \\
      --part Part02_Schemes \\
      --project ch01-schemes \\
      --out-root FormalizedSources/StacksProject

Writes one chapter file below the single blueprint for the requested part:
  <out-root>/<part>/blueprint/src/<project>.tex

The parent part's ``blueprint/src/content.tex`` is the only hgraph entry point;
the ``project`` argument names a descriptive chapter file stem (for example
``ch01-schemes``), not a
separate project.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

THM_ENVS = {
    "definition", "lemma", "proposition", "theorem", "corollary",
    "remark", "example", "notation", "convention", "conjecture",
    "situation",
}

# Strip Stacks-only chrome that is useless or harmful in hgraph blueprints.
DROP_ENVS = {"slogan"}  # slogans are lifted into optional titles when present


def load_tags(tags_path: Path, stem: str) -> dict[str, str]:
    """Map local label (e.g. definition-foo) -> stacks tag (e.g. 01HB)."""
    local_to_tag: dict[str, str] = {}
    if not tags_path.is_file():
        return local_to_tag
    prefix = stem + "-"
    for line in tags_path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "," not in line:
            continue
        tag, full = line.split(",", 1)
        if full.startswith(prefix):
            local = full[len(prefix):]
            local_to_tag[local] = tag
    return local_to_tag


def strip_preamble(text: str) -> str:
    """Drop stacks chapter wrapper through \tableofcontents."""
    # Prefer content after \tableofcontents if present.
    m = re.search(r"\\tableofcontents\s*", text)
    if m:
        text = text[m.end():]
    else:
        m = re.search(r"\\begin\{document\}", text)
        if m:
            text = text[m.end():]
    text = re.sub(r"\\end\{document\}\s*$", "", text)
    # Drop title/maketitle leftovers if still present
    text = re.sub(r"\\title\{[^}]*\}", "", text)
    text = re.sub(r"\\maketitle", "", text)
    text = re.sub(r"\\phantomsection\s*", "", text)
    text = re.sub(r"\\label\{section-phantom\}\s*", "", text)
    return text


def normalize_refs(text: str, stem: str) -> str:
    """Rewrite \\ref{lab} that lack a chapter prefix when lab is local-looking.

    Stacks uses chapter-local labels inside a chapter file and resolves them
    with the chapter stem at book build time. We keep local labels but prefix
    them with ``stem-`` so cross-chapter and within-chapter labels are unique
    in the multi-project workspace. Cross-chapter refs of the form
    ``otherchapter-label`` are left alone.
    """

    def fix_ref(m: re.Match) -> str:
        cmd, lab = m.group(1), m.group(2)
        if "-" in lab and not lab.startswith(
            ("item-", "equation-", "eq-")
        ):
            # Heuristic: already chapter-qualified if it contains a known pattern
            # stacks full labels are like schemes-lemma-foo or algebra-section-bar.
            head = lab.split("-", 1)[0]
            # local labels start with definition/lemma/section/…
            if head in {
                "definition", "lemma", "proposition", "theorem", "corollary",
                "remark", "example", "notation", "convention", "conjecture",
                "situation", "section", "subsection", "item", "equation",
                "diagram", "equation",
            }:
                return f"\\{cmd}{{{stem}-{lab}}}"
            return m.group(0)
        if lab.startswith(("definition-", "lemma-", "proposition-", "theorem-",
                           "corollary-", "remark-", "example-", "notation-",
                           "convention-", "conjecture-", "situation-",
                           "section-", "subsection-")):
            return f"\\{cmd}{{{stem}-{lab}}}"
        return m.group(0)

    text = re.sub(r"\\(ref|cref|eqref)\{([^}]+)\}", fix_ref, text)
    return text


def _balanced_group(text: str, start: int, opening: str = "{", closing: str = "}") -> tuple[str, int] | None:
    """Return the contents and end offset of a balanced TeX group."""
    if start >= len(text) or text[start] != opening:
        return None
    depth = 1
    escaped = False
    for pos in range(start + 1, len(text)):
        char = text[pos]
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
        elif char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0:
                return text[start + 1 : pos], pos + 1
    return None


def _split_tex_grid(text: str, separator: str) -> list[str]:
    """Split a matrix row/body outside nested TeX groups."""
    parts: list[str] = []
    start = 0
    depth = 0
    escaped = False
    pos = 0
    while pos < len(text):
        char = text[pos]
        if escaped:
            escaped = False
            pos += 1
            continue
        if char == "\\":
            if separator == "\\" and pos + 1 < len(text) and text[pos + 1] == "\\" and depth == 0:
                parts.append(text[start:pos])
                pos += 2
                start = pos
                continue
            escaped = True
        elif char == "{":
            depth += 1
        elif char == "}" and depth:
            depth -= 1
        elif char == separator and depth == 0:
            parts.append(text[start:pos])
            start = pos + 1
        pos += 1
    parts.append(text[start:])
    return parts


def _xy_label(text: str, pos: int) -> tuple[str, int] | None:
    """Read one Xy-pic superscript/subscript label after an arrow."""
    while pos < len(text) and text[pos].isspace():
        pos += 1
    if pos < len(text) and text[pos] == "-":
        pos += 1
        while pos < len(text) and text[pos].isspace():
            pos += 1
    if pos >= len(text):
        return None
    if text[pos] == "{":
        return _balanced_group(text, pos)
    if text[pos] == "\\":
        end = pos + 1
        while end < len(text) and text[end].isalpha():
            end += 1
        return text[pos:end], end
    return text[pos], pos + 1


def _xy_arrow_token(direction: str, style: str, labels: dict[str, str]) -> str:
    """Approximate an Xy-pic arrow with a KaTeX-supported directional symbol."""
    direction = direction.lower()
    if "r" in direction and "l" not in direction:
        if "d" in direction and "u" not in direction:
            arrow = r"\searrow"
        elif "u" in direction and "d" not in direction:
            arrow = r"\nearrow"
        elif style in {"=", "<=>"}:
            arrow = r"\xlongequal" if style == "=" else r"\Longleftrightarrow"
        elif style in {"..>", ".>", "-->"}:
            arrow = r"\dashrightarrow"
        elif style in {"~>"}:
            arrow = r"\rightsquigarrow"
        elif style in {"|->"}:
            arrow = r"\longmapsto"
        elif style in {"->>"}:
            arrow = r"\twoheadrightarrow"
        elif style in {"=>"}:
            arrow = r"\Longrightarrow"
        else:
            arrow = r"\longrightarrow"
    elif "l" in direction and "r" not in direction:
        if "d" in direction and "u" not in direction:
            arrow = r"\swarrow"
        elif "u" in direction and "d" not in direction:
            arrow = r"\nwarrow"
        elif style in {"=", "<=>"}:
            arrow = r"\xlongequal" if style == "=" else r"\Longleftrightarrow"
        elif style in {"..>", ".>", "-->"}:
            arrow = r"\dashleftarrow"
        elif style in {"~>"}:
            arrow = r"\leftsquigarrow"
        elif style in {"->>"}:
            arrow = r"\twoheadleftarrow"
        elif style in {"=>"}:
            arrow = r"\Longleftarrow"
        else:
            arrow = r"\longleftarrow"
    elif "d" in direction and "u" not in direction:
        arrow = r"\downarrow"
    elif "u" in direction and "d" not in direction:
        arrow = r"\uparrow"
    else:
        arrow = r"\longrightarrow"

    upper = labels.get("^")
    lower = labels.get("_")
    if arrow.startswith(r"\xlong"):
        if upper is not None:
            return arrow + "{" + upper + "}"
        return arrow + "{}"
    if upper is not None and lower is not None:
        return r"\overset{" + upper + r"}{\underset{" + lower + r"}{" + arrow + r"}}"
    if upper is not None:
        return r"\overset{" + upper + "}{" + arrow + "}"
    if lower is not None:
        return r"\underset{" + lower + "}{" + arrow + "}"
    return arrow


def _normalize_xy_cell(cell: str) -> str:
    """Turn Xy-pic ``\ar`` commands in one cell into visible math arrows."""
    out: list[str] = []
    pos = 0
    while pos < len(cell):
        match = re.search(r"\\ar(?![A-Za-z])", cell[pos:])
        if not match:
            out.append(cell[pos:])
            break
        start = pos + match.start()
        out.append(cell[pos:start])
        cursor = start + 3
        style = ""
        while True:
            while cursor < len(cell) and cell[cursor].isspace():
                cursor += 1
            if cursor >= len(cell) or cell[cursor] != "@":
                break
            cursor += 1
            if cursor < len(cell) and cell[cursor] == "{":
                parsed = _balanced_group(cell, cursor)
                if parsed is None:
                    break
                style, cursor = parsed
            elif cursor < len(cell) and cell[cursor] == "<":
                end = cell.find(">", cursor + 1)
                cursor = len(cell) if end < 0 else end + 1
            elif cursor < len(cell) and cell[cursor] == "/":
                end = cell.find("/", cursor + 1)
                cursor = len(cell) if end < 0 else end + 1
            elif cursor < len(cell) and cell[cursor] == "(":
                end = cell.find(")", cursor + 1)
                cursor = len(cell) if end < 0 else end + 1
            else:
                cursor += 1
        while cursor < len(cell) and cell[cursor].isspace():
            cursor += 1
        if cursor < len(cell) and cell[cursor] == "'":
            cursor += 1
            while cursor < len(cell) and cell[cursor].isspace():
                cursor += 1
        # A backtick path (``\ar`r[d] `d[l] [dll]``) is a curved Xy-pic
        # route. Keep its final target coordinate as the visible direction.
        while cursor < len(cell) and cell[cursor] == "`":
            cursor += 1
            while cursor < len(cell) and cell[cursor].isalpha():
                cursor += 1
            while cursor < len(cell) and cell[cursor].isspace():
                cursor += 1
            if cursor < len(cell) and cell[cursor] == "[":
                path_end = cell.find("]", cursor + 1)
                if path_end < 0:
                    cursor = len(cell)
                    break
                cursor = path_end + 1
            while cursor < len(cell) and cell[cursor].isspace():
                cursor += 1
        labels: dict[str, str] = {}
        # Xy-pic also allows labels before the target coordinate:
        # ``\ar^{f}[r]``. Read them now and merge with post-target labels.
        while cursor < len(cell):
            while cursor < len(cell) and cell[cursor].isspace():
                cursor += 1
            if cursor >= len(cell) or cell[cursor] not in "^_":
                break
            kind = cell[cursor]
            parsed = _xy_label(cell, cursor + 1)
            if parsed is None:
                break
            labels[kind], cursor = parsed
        if cursor >= len(cell) or cell[cursor] != "[":
            pos = cursor
            continue
        end = cell.find("]", cursor + 1)
        if end < 0:
            pos = len(cell)
            continue
        direction = cell[cursor + 1 : end]
        cursor = end + 1
        # Xy-pic permits a second target coordinate, e.g. ``\ar[r][rr]``.
        # KaTeX has one visible arrow per cell, so consume the extra target
        # while retaining the primary direction.
        while True:
            while cursor < len(cell) and cell[cursor].isspace():
                cursor += 1
            if cursor >= len(cell) or cell[cursor] != "[":
                break
            extra_end = cell.find("]", cursor + 1)
            if extra_end < 0:
                cursor = len(cell)
                break
            cursor = extra_end + 1
        while cursor < len(cell):
            while cursor < len(cell) and cell[cursor].isspace():
                cursor += 1
            if cursor >= len(cell) or cell[cursor] not in "^_":
                break
            kind = cell[cursor]
            parsed = _xy_label(cell, cursor + 1)
            if parsed is None:
                break
            labels[kind], cursor = parsed
        out.append(_xy_arrow_token(direction, style, labels))
        pos = cursor
    normalized = "".join(out)
    # Xy-pic line decorations (`|\hole`, `|!{...}\hole`) have no semantic
    # equivalent in KaTeX; the arrow and its labels are already retained.
    normalized = re.sub(r"\|!\{[^{}]*\}\\hole", "", normalized)
    normalized = normalized.replace(r"|\hole", "").replace(r"\hole", "")
    return normalized


def _normalize_rtwocell(text: str) -> str:
    """Replace the common Xy-pic two-cell arrow with a labeled arrow."""
    out: list[str] = []
    pos = 0
    while True:
        match = re.search(r"\\rtwocell(?![A-Za-z])", text[pos:])
        if not match:
            out.append(text[pos:])
            break
        start = pos + match.start()
        out.append(text[pos:start])
        cursor = start + len(r"\rtwocell")
        labels: dict[str, str] = {}
        while cursor < len(text) and text[cursor] in "^_":
            kind = text[cursor]
            parsed = _xy_label(text, cursor + 1)
            if parsed is None:
                break
            labels[kind], cursor = parsed
        while cursor < len(text) and text[cursor].isspace():
            cursor += 1
        parsed = _balanced_group(text, cursor)
        if parsed is None:
            out.append(r"\longrightarrow")
            pos = cursor
            continue
        label, cursor = parsed
        parts = [value for value in (labels.get("^"), labels.get("_"), label) if value]
        out.append(r"\xrightarrow{\substack{" + r"\\".join(parts) + "}}")
        pos = cursor
    normalized = "".join(out)
    # Xy-pic line decorations (`|\hole`, `|!{...}\hole`) have no semantic
    # equivalent in KaTeX; the arrow and its labels are already retained.
    normalized = re.sub(r"\|!\{[^{}]*\}\\hole", "", normalized)
    normalized = normalized.replace(r"|\hole", "").replace(r"\hole", "")
    return normalized


def normalize_xymatrix(text: str) -> str:
    """Convert Xy-pic matrices to simple KaTeX-compatible arrays.

    Xy-pic is a TeX package and KaTeX does not implement it. The conversion
    keeps the grid, labels, and arrow directions visible while flattening
    Xy-pic-specific bends and offsets that cannot be represented in KaTeX.
    """
    text = _normalize_rtwocell(text)
    out: list[str] = []
    pos = 0
    pattern = re.compile(r"\\xymatrix(?:\s*@[^\s{]+)*\s*\{")
    while True:
        match = pattern.search(text, pos)
        if not match:
            out.append(text[pos:])
            break
        opening = match.end() - 1
        parsed = _balanced_group(text, opening)
        if parsed is None:
            out.append(text[pos:])
            break
        body, end = parsed
        rows = _split_tex_grid(body, "\\")
        cells = [_split_tex_grid(row, "&") for row in rows]
        width = max((len(row) for row in cells), default=1)
        rendered_rows = []
        for row in cells:
            padded = row + [""] * (width - len(row))
            rendered_rows.append(" & ".join(_normalize_xy_cell(cell.strip()) for cell in padded))
        replacement = r"\begin{array}{" + "c" * width + "}" + r" \\ ".join(rendered_rows) + r"\end{array}"
        out.append(text[pos:match.start()])
        out.append(replacement)
        pos = end
    return "".join(out)


def prefix_labels(text: str, stem: str) -> str:
    """Prefix every \\label{local} with stem- when it looks chapter-local."""

    def fix_lab(m: re.Match) -> str:
        lab = m.group(1)
        if lab.startswith(stem + "-"):
            return m.group(0)
        if lab.startswith((
            "definition-", "lemma-", "proposition-", "theorem-", "corollary-",
            "remark-", "example-", "notation-", "convention-", "conjecture-",
            "situation-", "section-", "subsection-", "item-",
        )):
            return f"\\label{{{stem}-{lab}}}"
        return m.group(0)

    return re.sub(r"\\label\{([^}]+)\}", fix_lab, text)


def extract_slogan(inner: str) -> tuple[str | None, str]:
    m = re.search(r"\\begin\{slogan\}(.*?)\\end\{slogan\}", inner, re.S)
    if not m:
        return None, inner
    slogan = re.sub(r"\s+", " ", m.group(1)).strip()
    # Strip TeX for a short title
    slogan = re.sub(r"\\[a-zA-Z]+\*?\{([^}]*)\}", r"\1", slogan)
    slogan = re.sub(r"[{}]", "", slogan)
    slogan = slogan.strip()
    if len(slogan) > 90:
        slogan = slogan[:87] + "..."
    inner2 = inner[: m.start()] + inner[m.end() :]
    return (slogan or None), inner2


def first_label(inner: str) -> str | None:
    # Ignore labels inside display math roughly by taking the first \label
    m = re.search(r"\\label\{([^}]+)\}", inner)
    return m.group(1) if m else None


def decorate_statement(
    env: str,
    inner: str,
    stem: str,
    tags: dict[str, str],
) -> str:
    """Rewrite one thm-env body: optional title, source tag/link, group.

    Stacks ``situation`` environments are emitted as ``definition`` so hgraph
    (which has no situation content type) still creates graph nodes; labels keep
    the ``…-situation-…`` form so ``\\ref`` / ``\\uses`` stay stable.
    """
    slogan, inner = extract_slogan(inner)
    # Drop empty slogan leftovers
    inner = re.sub(r"\\begin\{slogan\}.*?\\end\{slogan\}", "", inner, flags=re.S)

    lab = first_label(inner)
    local_lab = None
    if lab and lab.startswith(stem + "-"):
        local_lab = lab[len(stem) + 1 :]
    elif lab:
        local_lab = lab

    tag = tags.get(local_lab or "", None) if local_lab else None

    # Build title: slogan preferred, else humanized local label tail
    title = slogan
    if not title and local_lab:
        # definition-locally-ringed-space -> Locally ringed space
        parts = local_lab.split("-")
        if parts and parts[0] in THM_ENVS:
            parts = parts[1:]
        if parts:
            title = " ".join(parts)
            title = title[:1].upper() + title[1:]

    out_env = "definition" if env == "situation" else env
    if env == "situation":
        title = f"Situation: {title}" if title else "Situation"

    # Inject metadata after \begin{env}[title] — caller wraps begin/end.
    meta_lines = []
    if tag:
        meta_lines.append(f"\\source{{stacks:{tag}}}")
        # hgraph renders standard LaTeX hyperlinks in statement bodies. Keep
        # the structured source marker above for graph metadata, and expose
        # the canonical Stacks tag URL directly on the node as well.
        meta_lines.append(
            f"\\href{{https://stacks.math.columbia.edu/tag/{tag}}}"
            f"{{\\texttt{{Stacks tag {tag}}}}}"
        )
    meta_lines.append(f"\\group{{{stem}}}")

    # Place metadata right after the first \label{...} if present, else at start.
    meta = "\n".join(meta_lines) + "\n"
    if lab:
        # Use a callable replacement so backslashes in \source/\group are literal.
        lab_pat = re.compile(r"(\\label\{" + re.escape(lab) + r"\})")
        inner, n = lab_pat.subn(lambda m: m.group(1) + "\n" + meta, inner, count=1)
        if n == 0:
            inner = meta + inner
    else:
        inner = meta + inner

    begin = f"\\begin{{{out_env}}}"
    if title:
        # Escape unprotected ] in title
        safe = title.replace("]", "{]}")
        begin = f"\\begin{{{out_env}}}[{safe}]"
    return begin + inner + f"\\end{{{out_env}}}"


def _collect_labels(text: str) -> set[str]:
    return set(re.findall(r"\\label\{([^}]+)\}", text))


_STMT_KINDS = (
    "definition", "lemma", "proposition", "theorem", "corollary",
    "remark", "example", "notation", "convention", "conjecture",
    "situation",
)


def _is_statement_label(lab: str) -> bool:
    """True for chapter-kind-rest labels (e.g. schemes-lemma-foo), not sections."""
    parts = lab.split("-")
    if len(parts) < 3:
        return False
    # stacks full labels: <stem>-<kind>-<rest…>
    return parts[1] in _STMT_KINDS


def _refs_in(text: str, known: set[str]) -> list[str]:
    found = re.findall(r"\\(?:ref|cref|eqref)\{([^}]+)\}", text)
    out: list[str] = []
    seen: set[str] = set()
    for r in found:
        if r in known and r not in seen and _is_statement_label(r):
            out.append(r)
            seen.add(r)
    return out


def inject_uses_from_refs(body: str, stem: str) -> str:
    """Add \\uses{…} on statements and proofs from same-chapter \\ref targets."""
    known = _collect_labels(body)
    env_alt = "|".join(sorted(THM_ENVS, key=len, reverse=True))
    # Optional [title] after \begin{env}; titles may contain nested [...].
    env_pat = re.compile(
        r"\\begin\{(" + env_alt + r")\}"
        r"(?:\[((?:[^\[\]]|\[[^\[\]]*\])*)\])?"
        r"(.*?)"
        r"\\end\{\1\}",
        re.S,
    )

    def stmt_sub(m: re.Match) -> str:
        env, title, inner = m.group(1), m.group(2), m.group(3)
        lab_m = re.search(r"\\label\{([^}]+)\}", inner)
        self_lab = lab_m.group(1) if lab_m else None
        refs = [r for r in _refs_in(inner, known) if r != self_lab]
        if not refs or "\\uses{" in inner:
            return m.group(0)
        uses = "\\uses{" + ", ".join(refs) + "}\n"
        if lab_m:
            # after label block / existing meta: insert after \group{...} if present
            g = re.search(r"\\group\{[^}]*\}\s*", inner)
            if g:
                pos = g.end()
                inner2 = inner[:pos] + uses + inner[pos:]
            else:
                inner2 = re.sub(
                    r"(\\label\{" + re.escape(self_lab) + r"\})",
                    lambda mm: mm.group(1) + "\n" + uses,
                    inner,
                    count=1,
                )
        else:
            inner2 = uses + inner
        begin = f"\\begin{{{env}}}"
        if title is not None:
            begin += f"[{title}]"
        return begin + inner2 + f"\\end{{{env}}}"

    body = env_pat.sub(stmt_sub, body)

    def proof_sub(m: re.Match) -> str:
        inner = m.group(1)
        if "\\uses{" in inner:
            return m.group(0)
        refs = _refs_in(inner, known)
        if not refs:
            return m.group(0)
        uses = "\\uses{" + ", ".join(refs) + "}\n"
        return "\\begin{proof}\n" + uses + inner + "\\end{proof}"

    body = re.sub(r"\\begin\{proof\}(.*?)\\end\{proof\}", proof_sub, body, flags=re.S)
    return body


def convert_body(text: str, stem: str, tags: dict[str, str]) -> str:
    text = strip_preamble(text)
    # Chapter files retain the upstream bibliography commands for standalone
    # book builds, but the Part aggregate owns bibliography discovery in hgraph.
    text = re.sub(r"\\bibliography(?:style)?\s*\{[^{}]*\}", "", text)
    text = normalize_xymatrix(text)
    text = prefix_labels(text, stem)
    text = normalize_refs(text, stem)

    # Remove \noindent noise at line starts (keep content)
    text = re.sub(r"(?m)^\\noindent\s*", "", text)
    # Collapse huge blank runs
    text = re.sub(r"\n{4,}", "\n\n\n", text)

    env_alt = "|".join(sorted(THM_ENVS, key=len, reverse=True))
    # Match \begin{env}[opt title]...\end{env}; keep optional title for decorate.
    env_pat = re.compile(
        r"\\begin\{(" + env_alt + r")\}"
        r"(?:\[((?:[^\[\]]|\[[^\[\]]*\])*)\])?"
        r"(.*?)"
        r"\\end\{\1\}",
        re.S,
    )
    out: list[str] = []
    pos = 0
    for m in env_pat.finditer(text):
        out.append(text[pos : m.start()])
        env, opt_title, inner = m.group(1), m.group(2), m.group(3)
        # Upstream Stacks rarely uses [title]; if present, put it back as slogan-like.
        if opt_title and "\\begin{slogan}" not in inner:
            inner = "\\begin{slogan}" + opt_title + "\\end{slogan}\n" + inner
        out.append(decorate_statement(env, inner, stem, tags))
        pos = m.end()
    out.append(text[pos:])
    body = "".join(out)

    # Drop leftover slogan environments outside statements (shouldn't remain)
    body = re.sub(r"\\begin\{slogan\}.*?\\end\{slogan\}", "", body, flags=re.S)
    body = inject_uses_from_refs(body, stem)
    return body.strip() + "\n"


def split_sections(body: str, stem: str) -> list[tuple[str, str, str]]:
    """Return list of (filename_stem, section_title, section_body)."""
    # Match \section{Title} optionally followed by \label{...}
    parts = re.split(r"(?m)^\\section\{", body)
    if len(parts) == 1:
        return [("01-body", "Body", body)]

    sections: list[tuple[str, str, str]] = []
    # parts[0] is preamble before first section (often empty or intro prose)
    head = parts[0].strip()
    idx = 1
    if head:
        sections.append(("00-front", "Front matter", head + "\n"))

    for chunk in parts[1:]:
        # chunk starts with Title} ...
        bm = re.match(r"([^}]*)\}(.*)$", chunk, re.S)
        if not bm:
            continue
        title, rest = bm.group(1).strip(), bm.group(2)
        # optional label right after
        lab_m = re.match(r"\s*\\label\{([^}]+)\}\s*", rest)
        label = None
        if lab_m:
            label = lab_m.group(1)
            rest = rest[lab_m.end() :]
        slug = re.sub(r"[^a-zA-Z0-9]+", "-", title).strip("-").lower()
        if not slug:
            slug = f"section-{idx:02d}"
        fname = f"{idx:02d}-{slug[:60]}"
        sec_body = f"\\section{{{title}}}\n"
        if label:
            sec_body += f"\\label{{{label}}}\n"
        sec_body += rest
        # ensure trailing newline
        if not sec_body.endswith("\n"):
            sec_body += "\n"
        sections.append((fname, title, sec_body))
        idx += 1
    return sections


def write_project(
    *,
    src: Path,
    stem: str,
    title: str,
    part: str,
    project: str,
    out_root: Path,
    tags_path: Path,
) -> dict:
    tags = load_tags(tags_path, stem)
    raw = src.read_text(encoding="utf-8", errors="replace")
    body = convert_body(raw, stem, tags)
    sections = split_sections(body, stem)

    root = out_root / part
    bp = root / "blueprint" / "src"
    bp.mkdir(parents=True, exist_ok=True)
    chapter_file = bp / f"{project}.tex"

    n_statements = 0
    chapter_parts = []
    env_re = re.compile(
        r"\\begin\{(" + "|".join(THM_ENVS) + r")\}"
    )
    for fname, sec_title, sec_body in sections:
        n_statements += len(env_re.findall(sec_body))
        chapter_parts.append(sec_body)
    chapter_file.write_text("\n".join(chapter_parts), encoding="utf-8")

    return {
        "project": project,
        "sections": len(sections),
        "approx_envs": n_statements,
        "root": str(root),
        "chapter_file": str(chapter_file),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", type=Path, required=True)
    ap.add_argument("--stem", required=True)
    ap.add_argument("--title", required=True)
    ap.add_argument("--part", required=True)
    ap.add_argument("--project", required=True)
    ap.add_argument("--out-root", type=Path, required=True)
    ap.add_argument("--tags", type=Path, default=None)
    args = ap.parse_args()
    tags = args.tags or (args.src.parent / "tags" / "tags")
    info = write_project(
        src=args.src,
        stem=args.stem,
        title=args.title,
        part=args.part,
        project=args.project,
        out_root=args.out_root,
        tags_path=tags,
    )
    print(info)


if __name__ == "__main__":
    main()
