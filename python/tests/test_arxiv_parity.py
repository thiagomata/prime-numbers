r"""Tests for python/tools/arxiv_parity.py (the arXiv parity gate).

Every case below is a real normalization or extraction challenge that
surfaced while running the tool against the nine article packages --
texorpdfstring titles, substack-split labels, section-sign encodings,
release-pinned URLs, list-literal false tags, stray \section lines inside
listings -- plus an end-to-end run over a synthetic package.
"""

import os
import sys
import time

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "tools"))

import arxiv_parity  # noqa: E402


# --- plain_tex: LaTeX-side markup -> comparable plain text ---------------


def test_plain_tex_joins_substack_split_labels():
    """cycle.md labels one step `[Modulo Idempotence + Distributivity over
    Addition]`; the tex splits it across a \\substack line break."""
    tex_form = (
        "\\substack{\\text{[Modulo Idempotence + Distributivity}\\\\\n"
        "                \\text{over Addition]}}"
    )
    md_form = "[Modulo Idempotence + Distributivity over Addition]"
    assert arxiv_parity.plain_tex(tex_form) == arxiv_parity.plain_tex(md_form)


def test_plain_tex_equates_section_sign_encodings():
    """The tex encodes the section sign as \\S; the Markdown uses the
    literal character. Cross-references are hardcoded as Subsection~N.M."""
    md_form = "[Full-cycle shift, \u00a75.1]"
    tex_form = "[Full-cycle shift, \\S5.1]"
    hardcoded_form = "[Full-cycle shift, Subsection~5.1]"
    key = arxiv_parity.plain_tex(md_form)
    assert arxiv_parity.plain_tex(tex_form) == key
    assert arxiv_parity.plain_tex(hardcoded_form) == key


def test_plain_tex_maps_command_shorthands_without_letter_boundaries():
    """`\\lt2r` and `\\ge5` must map even though no word boundary separates
    the command from a digit (a \\b-based pattern silently misses them)."""
    assert arxiv_parity.plain_tex(r"n\lt2r") == "n<2r"
    assert arxiv_parity.plain_tex(r"r\ge5") == "r>=5"
    assert arxiv_parity.plain_tex(r"x\le n") == "x<=n"
    assert arxiv_parity.plain_tex(r"a\bmod n") == "amodn"
    assert arxiv_parity.plain_tex(r"k\pmod 7") == "kmod7"


def test_plain_tex_maps_unicode_relations():
    assert arxiv_parity.plain_tex("n\u2264Q") == "n<=Q"
    assert arxiv_parity.plain_tex("x\u22655") == "x>=5"
    assert arxiv_parity.plain_tex("a\u2260b") == "a!=b"


def test_plain_tex_unwraps_texorpdfstring_and_wrappers():
    s = r"\texorpdfstring{\texttt{assert\allowbreak Foo}}{assertFoo}"
    assert arxiv_parity.plain_tex(s) == "assertFoo"


def test_plain_tex_strips_inline_math_markers_and_dashes():
    assert arxiv_parity.plain_tex("Base Case ($i < n$)") == "BaseCase(i<n)"
    assert arxiv_parity.plain_tex("Cauchy--Schwarz") == "Cauchy-Schwarz"
    assert arxiv_parity.plain_tex("a\u2014b\u2013c") == "a-b-c"


def test_plain_tex_normalizes_accented_escapes_and_quotes():
    # plain_tex preserves case: main() matches mixed-case identifiers
    # (assertNextPosition, ...Properties) against its output verbatim.
    assert arxiv_parity.plain_tex("B\\'ezout") == "B\u00e9zout"
    assert arxiv_parity.plain_tex("the article's gap") == "thearticlesgap"


# --- heading_title: Markdown heading -> comparable title -----------------


def test_heading_title_strips_numbering_forms():
    assert arxiv_parity.heading_title("1. Introduction") == "introduction"
    assert arxiv_parity.heading_title("4.6 Unit-Cycle Generation") == "unit-cyclegeneration"
    assert arxiv_parity.heading_title("A.17 Unit-Cycle Generation") == "unit-cyclegeneration"
    assert (
        arxiv_parity.heading_title("Appendix A: Scala Verification Code")
        == "scalaverificationcode"
    )


def test_heading_title_drops_identifier_suffix():
    raw = (
        "A.12 Cycle-Period Shifts \u2014 assertPeriodicShift, "
        "assertFullCycleShift, assertMultiCycleShift"
    )
    assert arxiv_parity.heading_title(raw) == "cycle-periodshifts"


def test_heading_title_normalizes_code_spans_and_math():
    assert arxiv_parity.heading_title("`euclidTheorem`") == "euclidtheorem"
    assert arxiv_parity.heading_title("Base Case ($i < n$)") == "basecase(i<n)"


# --- extract_tex_headings / tex_parity_titles -----------------------------


def test_extract_tex_headings_handles_nested_texorpdfstring_suffix():
    """cycle's `Propagate Modulo` title keeps its identifier suffix inside
    the \\texorpdfstring first argument, with a ` -- ` separator in the
    plain-text argument."""
    tex = (
        "\\subsection{\\texorpdfstring{Propagate Modulo --- \\protect\\texttt{"
        "propagateModFromValueToCycle /}\\newline \\protect\\texttt{"
        "assertCycleOfPosEqualsCycleOfModPos}} {Propagate Modulo -- "
        "propagateModFromValueToCycle / assertCycleOfPosEqualsCycleOfModPos}}"
    )
    assert arxiv_parity.extract_tex_headings(tex) == ["propagatemodulo"]


def test_extract_tex_headings_splits_identifier_suffix():
    tex = (
        "\\subsection{Gap Telescoping --- \\texorpdfstring{\\texttt{"
        "assert\\allowbreak Consecutive\\allowbreak Gap\\allowbreak Sum\\"
        "allowbreak Equals\\allowbreak Diff}}{assertConsecutiveGapSumEqualsDiff}}"
    )
    assert arxiv_parity.extract_tex_headings(tex) == ["gaptelescoping"]


def test_tex_parity_titles_ignores_listings_and_log_sections():
    """A stray \\section inside a lstlisting is source text, not document
    structure (the corrupted A.9 listing in integral-cycle); verification
    -log sections are a documented per-package substitution."""
    tex = (
        "\\section{Core Verified Properties}\n"
        "\\begin{lstlisting}[style=scala]\n"
        "  shiftedCI(i) == originalCI(i + 1)\n"
        "\\section{Scala Verification Code}\n"
        "\\end{lstlisting}\n"
        "\\subsection{Next Position}\n"
        "\\section{Stainless Verification Log Output}\n"
    )
    assert arxiv_parity.tex_parity_titles(tex) == [
        "coreverifiedproperties",
        "nextposition",
    ]


# --- md_parity_titles ------------------------------------------------------


def test_md_parity_titles_skips_guide_substitutions():
    md = "\n".join(
        [
            "# Title",
            "## Abstract",
            "## 1. Introduction",
            "### 4.1 Next Position",
            "## 9. References",
            "## Appendix B: Stainless Verification Log Output",
            "## 7. Conclusion",
        ]
    )
    titles, skipped = arxiv_parity.md_parity_titles(md)
    assert titles == ["introduction", "nextposition", "conclusion"]
    assert len(skipped) == 3  # Abstract, numbered References, Appendix B


def test_md_parity_titles_honors_extra_skips():
    md = "## 1. Introduction\n## Custom Heading"
    titles, skipped = arxiv_parity.md_parity_titles(md, {"Custom Heading"})
    assert titles == ["introduction"]
    assert skipped == ["Custom Heading"]


# --- extract_md_math_tags --------------------------------------------------


def test_extract_md_math_tags_keeps_real_labels():
    md = "\n".join(
        [
            "```math",
            "CI_i &= CI_{i-1} + \\text{Cycle}([1])_i &&\\text{[Step Property, \u00a73.1]} \\\\",
            "&= init + i + 1 &&\\text{[Q.E.D.]} \\\\",
            "&&\\text{[existsZero]} \\\\",
            "```",
        ]
    )
    assert arxiv_parity.extract_md_math_tags(md) == [
        "Q.E.D.",
        "Step Property, \u00a73.1",
        "existsZero",
    ]


def test_extract_md_math_tags_rejects_math_literals():
    """List syntax and bare index expressions are not labels."""
    md = "\n".join(
        [
            "```math",
            "L &= [v_0, v_1, \\dots, v_{n-1}]",
            "L_i &= L[(k+j) \\bmod n]",
            "R &:= [i \\dots j] && [0, n - 1]",
            "S &:= [init]",
            "```",
        ]
    )
    assert arxiv_parity.extract_md_math_tags(md) == []


# --- identifiers ------------------------------------------------------------


def test_extract_identifiers_collects_asserts_and_property_objects():
    md = (
        "Verified in CycleIntegralOnesProperties::assertCycleIntegralOfOnes "
        "and ModIdempotence, see assertNextPosition."
    )
    assert arxiv_parity.extract_identifiers(md) == [
        "CycleIntegralOnesProperties",
        "assertCycleIntegralOfOnes",
        "assertNextPosition",
    ]


def test_prose_identifiers_excludes_url_only_names():
    """modulo.md mentions two ModIdempotence lemmas only as link targets
    behind display text like `positive shift` -- they are not rendered
    PDF text."""
    md = (
        "This invariant is verified for the [positive shift]"
        "(https://github.com/x/ModIdempotence.scala#assertDivModWithMoreDivAndLessModSameSolution). "
        "See also assertModSum and the [listing]"
        "(https://github.com/x/ModSum.scala#assertModSum)."
    )
    ids = arxiv_parity.extract_identifiers(md)
    prose = arxiv_parity.prose_identifiers(md, ids)
    assert "assertDivModWithMoreDivAndLessModSameSolution" in ids
    assert "assertDivModWithMoreDivAndLessModSameSolution" not in prose
    assert "assertModSum" in ids
    assert "assertModSum" in prose  # also appears as display text


# --- url_norm ----------------------------------------------------------------


def test_url_norm_ignores_release_pinning():
    master = "https://github.com/x/blob/master/src/A.scala#f"
    pinned = "https://github.com/x/blob/list-article-v1.0.0/src/A.scala#f"
    assert arxiv_parity.url_norm(master) == arxiv_parity.url_norm(pinned)
    other = "https://github.com/x/blob/master/src/B.scala#f"
    assert arxiv_parity.url_norm(master) != arxiv_parity.url_norm(other)


# --- find_dangling_articles ---------------------------------------------------

def test_find_dangling_articles_flags_paragraph_final_articles():
    """The real shapes left by the gap-dynamics de-drafting surgery."""
    flagged = [
        "found none. A \n\n\\textbf{How the two compose.}",
        "proves the exact product count. A \\par}",
        "its endpoint discipline. A\n\\par}",
        "and its exact boundary. A",
    ]
    for s in flagged:
        assert arxiv_parity.find_dangling_articles(s), s


def test_find_dangling_articles_allows_wrapped_sentences_and_math():
    kept = [
        "a single signed quantity. A\nweighted conservation law",  # next line
        "as an endpoint. A value could belong",  # same paragraph, next line
        "window. A struck value need not be a 2-gap endpoint",  # same line
    ]
    for s in kept:
        assert arxiv_parity.find_dangling_articles(s) == [], s


def test_find_dangling_articles_allows_inline_emphasized_terms():
    """'A \\textbf{term}' / 'A **term**' on the same line define a term
    (survival-frontiers §1, §2); the blank-line-separated shape above
    remains flagged since it is not a same-line continuation."""
    kept = [
        "smallest possible gap. A \\textbf{2-gap} is a pair",
        "possible gap. A **2-gap** is a pair",
        "one of three policies. A \\textbf{random parent} draws",
    ]
    for s in kept:
        assert arxiv_parity.find_dangling_articles(s) == [], s
    assert arxiv_parity.find_dangling_articles(
        "found none. A \n\n\\textbf{How the two compose.}"
    ), "blank-line-separated \\textbf must still flag"


# --- input_section_paths ------------------------------------------------------

def test_input_section_paths_follows_assembly_and_dedupes():
    """Packages guard inputs with \\IfFileExists, naming each file twice;
    unhooked-but-kept files must not appear."""
    main_tex = (
        "\\input{sections/00-abstract}\n"
        "\\IfFileExists{sections/01-body.tex}{\\input{sections/01-body}}{}\n"
        "\\IfFileExists{sections/14-removed.tex}{\\input{sections/14-removed}}{}\n"
        "\\input{../figures/ignored.tex}\n"
    )
    assert arxiv_parity.input_section_paths(main_tex) == [
        "sections/00-abstract",
        "sections/01-body",
        "sections/14-removed",
    ]


# --- effective_time (git-corrected freshness) ---------------------------------


def test_effective_time_uses_commit_time_for_clean_files(monkeypatch):
    monkeypatch.setattr(
        arxiv_parity, "git",
        lambda *a: {"status": "", "log": "1700000000"}.get(
            "status" if a[0] == "status" else "log", ""
        ),
    )
    monkeypatch.setattr(os.path, "getmtime", lambda p: 9999999999.0)
    assert arxiv_parity.effective_time("clean.md") == 1700000000.0


def test_effective_time_uses_mtime_for_dirty_files(monkeypatch):
    monkeypatch.setattr(
        arxiv_parity, "git",
        lambda *a: " M dirty.md" if a[0] == "status" else "",
    )
    monkeypatch.setattr(os.path, "getmtime", lambda p: 9999999999.0)
    assert arxiv_parity.effective_time("dirty.md") == 9999999999.0


def test_effective_time_falls_back_to_mtime_without_commits(monkeypatch):
    monkeypatch.setattr(arxiv_parity, "git", lambda *a: "")
    monkeypatch.setattr(os.path, "getmtime", lambda p: 1234.0)
    assert arxiv_parity.effective_time("new.md") == 1234.0


def test_freshness_compares_content_time_on_both_sides(tmp_path, capsys, monkeypatch):
    """Regression: the pdf side must be git-corrected like the sources.

    A pdf committed together with its sources has an older working-tree
    mtime (built before the commit) but equal commit time; the asymmetric
    raw-mtime comparison reported every package stale after such a commit.
    """
    pkg = _write_package(tmp_path)
    content_times = {}
    for base, _, files in os.walk(tmp_path):
        for f in files:
            content_times[os.path.join(base, f)] = 100.0
    monkeypatch.setattr(arxiv_parity, "effective_time", lambda p: content_times[p])
    monkeypatch.setattr(sys, "argv", ["arxiv_parity.py", pkg])
    with pytest.raises(SystemExit) as exc:
        arxiv_parity.main()
    out = capsys.readouterr().out
    assert exc.value.code == 0
    assert "freshness  ] PASS" in out


# --- end-to-end over a synthetic package ---------------------------------------


def _write_package(root, with_heading=True):
    articles = root / "articles"
    (articles / "arxiv" / "demo").mkdir(parents=True)
    (articles / "chapter9").mkdir(parents=True)

    md = "\n".join(
        [
            "# Demo Article",
            "",
            "**Author:** Demo",
            "",
            "## 1. Introduction",
            "",
            "Verified in [DemoProperties::assertDemoHolds](https://github.com/x/Demo.scala).",
            "",
            "```math",
            "x &= 1 &&\\text{[Demo Label]} \\\\",
            "```",
            "",
            "## References",
        ]
    )
    (articles / "chapter9" / "demo.md").write_text(md, encoding="utf-8")

    body = (
        "\\section{Introduction}\n"
        "Text about DemoProperties and assertDemoHolds, "
        "labeled \\text{[Demo Label]}.\n"
    ) if with_heading else "Text only.\n"
    (articles / "arxiv" / "demo" / "main.tex").write_text(
        "\\input{sections/01-body}\n", encoding="utf-8"
    )
    (articles / "arxiv" / "demo" / "sections").mkdir()
    (articles / "arxiv" / "demo" / "sections" / "01-body.tex").write_text(
        body, encoding="utf-8"
    )
    (articles / "arxiv" / "demo" / "references.bib").write_text(
        "% empty\n", encoding="utf-8"
    )
    pdf_dir = articles / "arxiv" / "demo" / "output" / "pdf"
    pdf_dir.mkdir(parents=True)
    (pdf_dir / "demo.pdf").write_text("not a real pdf", encoding="utf-8")
    return str(articles / "arxiv" / "demo")


def test_end_to_end_passes_on_synced_package(tmp_path, capsys, monkeypatch):
    """The fake pdf makes gs fail, exercising the warn-and-continue path:
    FAIL-level checks (freshness, headings, ids, tags-tex) must still pass."""
    pkg = _write_package(tmp_path)
    # Sources are written before the pdf inside _write_package? No --
    # ensure ordering explicitly: touch the pdf last.
    pdf = os.path.join(pkg, "output", "pdf", "demo.pdf")
    with open(pdf, "a", encoding="utf-8"):
        os.utime(pdf, (time.time() + 5, time.time() + 5))
    monkeypatch.setattr(sys, "argv", ["arxiv_parity.py", pkg])
    with pytest.raises(SystemExit) as exc:
        arxiv_parity.main()
    out = capsys.readouterr().out
    assert exc.value.code == 0
    assert "SUMMARY: PASS" in out
    assert "[headings" in out and "FAIL" not in out.split("SUMMARY")[0]


def test_end_to_end_fails_when_tex_drops_a_heading(tmp_path, capsys, monkeypatch):
    pkg = _write_package(tmp_path, with_heading=False)
    pdf = os.path.join(pkg, "output", "pdf", "demo.pdf")
    with open(pdf, "a", encoding="utf-8"):
        os.utime(pdf, (time.time() + 5, time.time() + 5))
    monkeypatch.setattr(sys, "argv", ["arxiv_parity.py", pkg])
    with pytest.raises(SystemExit) as exc:
        arxiv_parity.main()
    out = capsys.readouterr().out
    assert exc.value.code == 1
    assert "md-only: ['introduction']" in out
