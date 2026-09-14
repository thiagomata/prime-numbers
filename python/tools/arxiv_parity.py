#!/usr/bin/env python3
r"""arXiv parity check: Markdown article <-> LaTeX package <-> built PDF.

Repo maintenance tool (python/tools/, alongside check_scala_cycles.py).
Enforces the arxiv-sync rule (AGENTS.md) mechanically, replacing the manual
parity passes described in articles/arxiv/CONVERSION_GUIDE.md section 5.
Invoked by the `just arxiv-parity` recipe.

Usage: arxiv_parity.py <package-dir>   (e.g. articles/arxiv/integral-cycle)

Layout follows python/ARCHITECTURE.md Convention 1: the normalization and
extraction functions below are pure (no I/O) and are covered by
python/tests/test_arxiv_parity.py; main() is the I/O runner that reads the
sources, shells out to git/gs, prints the report, and sets the exit code.

Checks (a FAIL exits 1 for the package):
  1. freshness  - output/pdf/<name>.pdf mtime must postdate the Markdown
                  source, main.tex, every assembled sections/*.tex (per
                  main.tex's \input directives) and references.bib.
  2. headings   - bidirectional: every Markdown ## / ### heading (minus
                  guide-documented substitutions) matches a \\section /
                  \\subsection title in the tex, and vice versa, with counts
                  equal.
  3. identifiers- every assert* / *Properties name in the Markdown appears
                  in the tex sources and in the PDF text layer (names that
                  occur only as link URLs are link targets, not text).
  4. tags       - every bracketed label inside Markdown ```math blocks
                  (e.g. [Unit Cycle], [Q.E.D.]) appears in the tex sources.
  5. pdf tags   - warn-level: tags present in the gs text layer of the PDF.

Allowed absences (CONVERSION_GUIDE substitutions, same for every package):
  headings "Abstract" and "References" (LaTeX front matter / bibliography)
  and any "Appendix B: ..." heading (dropped as GitHub-only). An optional
  per-package file .parity-skip lists extra headings/URLs to exempt, one
  per line.
"""

import re
import os
import sys
import glob
import subprocess
import tempfile

BUILTIN_HEADING_SKIPS = (
    lambda h: h == "Abstract",
    lambda h: h == "References",
    lambda h: h.startswith("Appendix B:"),
)


def git(*args):
    return subprocess.run(
        ["git", *args], capture_output=True, text=True, check=False
    ).stdout


def effective_time(path):
    """Content time of a source file.

    mtime, corrected by git: a file unmodified in the working tree has
    the content of its last commit, and branch switches rewrite mtimes
    without changing bytes -- so the commit date is the truth.
    """
    if git("status", "--porcelain", "--", path).strip() == "":
        ct = git("log", "-1", "--format=%ct", "--", path).strip()
        if ct:
            return float(ct)
    return os.path.getmtime(path)


def norm_space(s):
    return re.sub(r"\s+", " ", s).strip()


CMD_MAP = [
    (r"\\bmod(?![a-zA-Z])", "mod"),
    (r"\\pmod(?![a-zA-Z])", "mod"),
    (r"\\lt(?![a-zA-Z])", "<"),
    (r"\\gt(?![a-zA-Z])", ">"),
    (r"\\leq(?![a-zA-Z])", "<="),
    (r"\\geq(?![a-zA-Z])", ">="),
    (r"\\le(?![a-zA-Z])", "<="),
    (r"\\ge(?![a-zA-Z])", ">="),
    (r"\\mid(?![a-zA-Z])", "|"),
]


def plain_tex(s):
    """Reduce LaTeX markup to comparable plain text (guide normalizations)."""
    # LaTeX line breaks (e.g. inside \substack) split labels across
    # source lines; join them before anything else.
    s = s.replace("\\\\", " ")
    # \texorpdfstring{texy}{plain} -> plain (one nesting level)
    s = re.sub(
        r"\\texorpdfstring\{((?:[^{}]|\{[^{}]*\})*)\}\{((?:[^{}]|\{[^{}]*\})*)\}",
        r"\2",
        s,
    )
    s = re.sub(
        r"\\(?:text|operatorname|mathrm|texttt|mathbf|mathbin|allowbreak|substack)\{?", "", s
    )
    s = s.replace("\\protect", "").replace("\\newline", " ")
    s = s.replace("\\ ", " ").replace("\\;", " ").replace("\\,", " ")
    s = s.replace("\\!", "")
    s = re.sub(r"\\'([eE])", lambda m: "\u00e9" if m.group(1) == "e" else "\u00c9", s)
    for pat, rep in CMD_MAP:
        s = re.sub(pat, rep, s)
    s = s.replace("\\S", "").replace("\u00a7", "")
    s = re.sub(r"(Subsection|Section|Appendix)~?\s*(?=\d)", "", s)
    s = s.replace("$", "")
    s = re.sub(r"['\u2018\u2019]", "", s)
    s = re.sub(r"[`]", "", s)
    s = s.replace("--", "-")
    s = s.replace("\u2264", "<=").replace("\u2265", ">=")
    s = s.replace("\u2260", "!=")
    s = re.sub(r"[\u2013\u2014\u2212]", "-", s)
    s = re.sub(r"[{}]", "", s)
    s = re.sub(r"\^", "", s)
    s = s.replace("~", "")
    s = re.sub(r"\s+", "", s)
    return s


def heading_title(raw):
    """Markdown heading text -> normalized comparable title."""
    t = raw.strip()
    t = re.sub(
        r"^(?:Appendix [A-Z]:\s+|[A-Z]\.\d+\s+|\d+(?:\.\d+)*\.?\s+)", "", t
    )
    # Drop the identifier suffix of appendix entries (--- / em dash).
    t = re.split(r"\s+---\s+|\s+\u2014\s+", t)[0]
    return norm_space(plain_tex(t)).lower()


def brace_match(s, i):
    """Given s[i] == '{', return (content, index_after_close)."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "{":
            depth += 1
        elif s[j] == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1 : j], j + 1
    return None, -1


def unwrap_texorpdfstring(s):
    """Replace every \\texorpdfstring{texy}{plain} with its plain arg."""
    out = []
    i = 0
    while True:
        m = re.search(r"\\texorpdfstring\s*", s[i:])
        if not m:
            out.append(s[i:])
            break
        start = i + m.start()
        out.append(s[i:start])
        j = start + m.end()
        if j < len(s) and s[j] == "{":
            first, j = brace_match(s, j)
            while j < len(s) and s[j].isspace():
                j += 1
            if j < len(s) and s[j] == "{":
                second, j = brace_match(s, j)
                out.append(second)
                i = j
                continue
        # Malformed: keep as-is (will surface as a parity failure).
        out.append(s[start : start + len(m.group(0))])
        i = start + len(m.group(0))
    return "".join(out)


def extract_tex_headings(tex):
    """All \\section{...} / \\subsection{...} titles, brace-matched."""
    titles = []
    for m in re.finditer(r"\\(section|subsection)\*?\s*\{", tex):
        i = m.end()
        depth = 1
        j = i
        while j < len(tex) and depth > 0:
            if tex[j] == "{":
                depth += 1
            elif tex[j] == "}":
                depth -= 1
            j += 1
        if depth == 0:
            content = tex[i : j - 1]
            # Unwrap \texorpdfstring BEFORE splitting off identifier
            # suffixes: the " --- " / " -- " separators can live inside
            # its first argument.
            content = unwrap_texorpdfstring(content)
            title = re.split(r"\s+---\s+|\s+--\s+", content)[0]
            titles.append(norm_space(plain_tex(title)).lower())
    return titles


def tex_parity_titles(tex):
    """Tex section/subsection titles that are parity targets.

    Excludes headings inside lstlisting environments (listings are
    verbatim source text, not document structure) and verification-log
    section titles: whatever each package did with the log appendix
    (dropped, or converted to a log section) is intentional, never a
    parity target.
    """
    stripped = re.sub(
        r"\\begin\{lstlisting\}.*?\\end\{lstlisting\}", "", tex, flags=re.S
    )
    return [t for t in extract_tex_headings(stripped) if "verificationlog" not in t]


def md_parity_titles(md, extra_skips=()):
    """(parity-target titles, allowed-absent raw headings) for the Markdown.

    Guide substitutions, matched on raw text OR normalized title (some
    articles number their References heading): Abstract and References
    live in LaTeX front matter / the bibliography, and the log-output
    appendix is GitHub-only material.
    """
    skipped, titles = [], []
    for raw in re.findall(r"^#{2,3}\s+(.+?)\s*$", md, re.M):
        title = heading_title(raw)
        if (
            raw.strip() in extra_skips
            or any(f(raw.strip()) for f in BUILTIN_HEADING_SKIPS)
            or title in ("abstract", "references")
            or "verificationlog" in title
        ):
            skipped.append(raw.strip())
            continue
        titles.append(title)
    return titles, skipped


def extract_md_math_tags(md):
    """Bracketed labels inside ```math blocks (e.g. [Unit Cycle], [Q.E.D.]).

    Excludes subscripted math literals like [v_0, v_1, \\dots] (list
    syntax, not labels) and bare expressions like [(k+j) \\bmod n] or
    [0, n - 1]: real labels carry a capitalized word (or are Q.E.D.).
    """
    tags = set()
    for block in re.findall(r"```math\n(.*?)```", md, re.S):
        for tag in re.findall(r"\[([^\[\]\n]{2,60})\]", block):
            if "_" in tag:
                continue
            if not (re.search(r"[A-Z][a-z]", tag) or "Q.E.D." in tag):
                continue
            tags.add(norm_space(tag))
    return sorted(tags)


def extract_identifiers(md):
    """Sorted assert* / *Properties names mentioned in the Markdown."""
    return sorted(
        set(re.findall(r"\bassert[A-Z]\w*\b", md))
        | set(re.findall(r"\b[A-Z]\w*Properties\b", md))
    )


def prose_identifiers(md, identifiers):
    """Identifiers that occur outside URLs: candidates for rendered text.

    Identifiers whose only Markdown occurrences are inside link URLs are
    link targets, not rendered text -- the PDF text layer legitimately
    never shows them.
    """
    md_no_urls = re.sub(r"https?://\S+", "", md)
    return {
        i
        for i in identifiers
        if re.search(r"\b" + re.escape(i) + r"\b", md_no_urls)
    }


def url_norm(u):
    """Release-pinning-agnostic URL key (blob/<ref>/ -> blob/*/)."""
    return re.sub(r"blob/[^/]+/", "blob/*/", u)


def extract_md_urls(md):
    return set(
        u.rstrip(".,;:")
        for u in re.findall(r"https?://[^\s<>\"()\[\]]+", md)
    )


DANGLING_ARTICLE = re.compile(
    r"\.\s+A"
    r"(?![ \t]*(?:\\(?:textbf|emph|textit)\{|\*\*))"
    r"(?![ \t]*\n?[ \t]*[A-Za-z{])"
)


def find_dangling_articles(text):
    """Offsets of sentence-final 'A' left paragraph-final.

    Sentence surgery (the de-drafting pass removed 'A supplementary
    record ...' pointer sentences) can leave the article behind:
    'found none. A' at a paragraph end renders as a stray 'A' in the
    PDF. A legitimate wrapped sentence continues with a word directly
    after the A (same line or the next line), so it is not flagged;
    a paragraph genuinely ending in a standalone 'A' (e.g. 'Plan A')
    would false-positive -- none exists in the current packages.
    'A' immediately (same line, no blank-line break) introducing an
    emphasized term -- '\\textbf{2-gap}' or Markdown '**2-gap**' -- is
    also a legitimate continuation (survival-frontiers defines several
    terms this way); the same shape after a blank line still flags,
    since that is the paragraph-final surgery leftover shape.
    """
    return [m.start() for m in DANGLING_ARTICLE.finditer(text)]


def input_section_paths(main_tex):
    """Ordered unique sections/ paths assembled by main.tex.

    Follows \\input{...} and \\IfFileExists{...}{\\input{...}} directives
    (both name the file in packages that use the guard, hence the
    dedupe). Unhooked-but-kept files on disk (never-destroy) are not
    part of the assembly and must not count against parity.
    """
    paths = []
    for m in re.finditer(r"\\(?:input|IfFileExists)\{([^}]+)\}", main_tex):
        rel = m.group(1)
        if rel.startswith("sections/"):
            rel = rel[:-4] if rel.endswith(".tex") else rel
            if rel not in paths:
                paths.append(rel)
    return paths


def die(msg):
    print(f"ERROR: {msg}")
    sys.exit(1)


def main():
    if len(sys.argv) != 2:
        die("usage: arxiv_parity.py <package-dir>")
    pkg = sys.argv[1].rstrip("/")
    name = os.path.basename(pkg)
    if not os.path.isfile(os.path.join(pkg, "main.tex")):
        die(f"{pkg} has no main.tex")

    # Locate the Markdown source edition for this article.
    md_candidates = glob.glob(
        os.path.join(os.path.dirname(pkg), "..", "chapter*", f"{name}.md")
    )
    if len(md_candidates) != 1:
        die(f"cannot locate unique Markdown source for '{name}': {md_candidates}")
    md_path = os.path.normpath(md_candidates[0])

    md = open(md_path, encoding="utf-8").read()
    main_tex = open(os.path.join(pkg, "main.tex"), encoding="utf-8").read()
    assembled = [
        os.path.join(pkg, rel + ".tex")
        for rel in input_section_paths(main_tex)
        if os.path.isfile(os.path.join(pkg, rel + ".tex"))
    ]
    # Fallback for nonstandard assemblies.
    tex_files = [os.path.join(pkg, "main.tex")] + (
        assembled
        if assembled
        else sorted(glob.glob(os.path.join(pkg, "sections", "*.tex")))
    )
    bib = os.path.join(pkg, "references.bib")
    if os.path.isfile(bib):
        tex_files.append(bib)
    tex = "\n".join(open(f, encoding="utf-8").read() for f in tex_files)
    skip_file = os.path.join(pkg, ".parity-skip")
    extra_skips = (
        set(open(skip_file, encoding="utf-8").read().splitlines())
        if os.path.isfile(skip_file)
        else set()
    )

    failures = []
    warnings = []

    def check(label, ok, detail):
        print(f"  [{label:<11}] {'PASS' if ok else 'FAIL'}  {detail}")
        if not ok:
            failures.append(f"{label}: {detail}")

    print(f"== {name} (md: {os.path.relpath(md_path)}) ==")

    # ---- 1. freshness -------------------------------------------------
    pdf = os.path.join(pkg, "output", "pdf", f"{name}.pdf")
    if not os.path.isfile(pdf):
        check("freshness", False, f"missing {os.path.relpath(pdf)}")
    else:
        # Same git-corrected content time as the sources: a pdf committed
        # together with its sources reads as equal commit times even when
        # its working-tree mtime is older (built before the commit). The
        # asymmetric raw-mtime comparison failed every package after any
        # such commit.
        pdf_mtime = effective_time(pdf)
        stale = [
            f
            for f in [md_path] + tex_files
            if effective_time(f) > pdf_mtime
        ]
        check(
            "freshness",
            not stale,
            f"pdf newer than {len(tex_files) + 1} sources"
            if not stale
            else f"stale pdf, newer sources: "
            + ", ".join(os.path.relpath(f) for f in stale),
        )

    # ---- 2. headings (bidirectional) ----------------------------------
    md_titles, skipped = md_parity_titles(md, extra_skips)
    tex_titles = tex_parity_titles(tex)
    md_set, tex_set = set(md_titles), set(tex_titles)
    md_missing = md_set - tex_set
    tex_missing = tex_set - md_set
    counts_ok = len(md_titles) == len(tex_titles)
    check(
        "headings",
        not md_missing and not tex_missing and counts_ok,
        f"{len(md_titles)} md <-> {len(tex_titles)} tex titles, "
        f"{len(skipped)} allowed-absent"
        if not md_missing and not tex_missing
        else f"md-only: {sorted(md_missing)}; tex-only: {sorted(tex_missing)}",
    )

    # ---- 3./4. identifiers + tags vs tex ------------------------------
    searchable = re.sub(r"\\allowbreak\s*", "", tex)
    searchable_key = plain_tex(searchable)

    identifiers = extract_identifiers(md)
    prose_ids = prose_identifiers(md, identifiers)
    missing_ids_tex = [
        i for i in identifiers if i not in searchable_key
    ]
    check(
        "identifiers",
        not missing_ids_tex,
        f"{len(identifiers)} verified names in tex"
        if not missing_ids_tex
        else f"missing from tex: {missing_ids_tex}",
    )

    tags = extract_md_math_tags(md)
    tag_keys = {t: plain_tex(t) for t in tags}
    missing_tags_tex = [t for t, k in tag_keys.items() if k not in searchable_key]
    check(
        "tags-tex",
        not missing_tags_tex,
        f"{len(tags)} math labels in tex"
        if not missing_tags_tex
        else f"missing from tex: {missing_tags_tex}",
    )

    # ---- dangling articles (sentence-surgery tripwire) -----------------
    dangling = []
    for f in [md_path] + tex_files:
        n = len(find_dangling_articles(open(f, encoding="utf-8").read()))
        if n:
            dangling.append(f"{os.path.relpath(f)}: {n}")
    check(
        "dangling-a",
        not dangling,
        "no sentence-final 'A' left by sentence surgery"
        if not dangling
        else "possible sentence-surgery leftovers: " + "; ".join(dangling),
    )

    # ---- 5. PDF text layer ---------------------------------------------
    if os.path.isfile(pdf):
        try:
            with tempfile.NamedTemporaryFile(suffix=".txt", delete=False) as tf:
                out = tf.name
            subprocess.run(
                [
                    "gs", "-q", "-dNOPAUSE", "-dBATCH", "-sDEVICE=txtwrite",
                    f"-o{out}", pdf,
                ],
                check=True,
                capture_output=True,
                timeout=120,
            )
            pdf_key = plain_tex(
                open(out, encoding="utf-8", errors="ignore").read()
            )
            os.unlink(out)
            missing_ids_pdf = [i for i in prose_ids if i not in pdf_key]
            url_only = [i for i in identifiers if i not in prose_ids]
            check(
                "pdf-ids",
                not missing_ids_pdf,
                f"{len(prose_ids)} verified names in pdf text"
                + (f" (+{len(url_only)} as link targets)" if url_only else "")
                if not missing_ids_pdf
                else f"missing from pdf text: {missing_ids_pdf}",
            )
            missing_tags_pdf = [t for t, k in tag_keys.items() if k not in pdf_key]
            if missing_tags_pdf:
                warnings.append(f"tags not found in pdf text: {missing_tags_pdf}")
            print(
                f"  [pdf-tags    ] {'PASS' if not missing_tags_pdf else 'WARN'}  "
                f"{len(tags) - len(missing_tags_pdf)}/{len(tags)} math labels in pdf text"
            )
        except (subprocess.SubprocessError, FileNotFoundError) as e:
            warnings.append(f"pdf text extraction skipped ({e})")
            print("  [pdf-text    ] WARN  extraction skipped (gs unavailable?)")
    else:
        warnings.append("pdf text check skipped (no pdf)")

    # ---- 6. URLs (warn-level) ------------------------------------------
    md_urls = extract_md_urls(md)
    url_skip = {u for u in extra_skips if u.startswith("http")}
    tex_urls = url_norm(tex)
    missing_urls = sorted(
        u
        for u in md_urls
        if u not in url_skip and url_norm(u) not in tex_urls
    )
    if missing_urls:
        warnings.append(f"urls not in tex/bib: {missing_urls}")
    print(
        f"  [urls        ] {'WARN' if missing_urls else 'PASS'}  "
        f"{len(md_urls) - len(missing_urls)}/{len(md_urls)} urls present"
    )

    for w in warnings:
        print(f"  WARN {w}")
    verdict = "PASS" if not failures else "FAIL"
    print(f"  SUMMARY: {verdict}" + (f" ({len(warnings)} warnings)" if warnings else ""))
    sys.exit(0 if not failures else 1)


if __name__ == "__main__":
    main()
