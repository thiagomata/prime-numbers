# integral-cycle — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Formal Verification of Cycle
Integral Properties from First Principles*, converted from the canonical
Markdown edition
[`articles/chapter4/integral-cycle.md`](../../chapter4/integral-cycle.md).
The Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                         document setup, metadata, Scala listing
                                 style, and section assembly
sections/
  00-abstract.tex                abstract and license notice
  01-introduction.tex            introduction and related work
  02-preliminaries.tex           companion-article foundations
  03-definitions.tex             recursive and modulo cycle integrals (3.1–3.3)
  04-core-properties.tex         core verified properties (4.1–4.5)
  05-periodic-properties.tex     persistent and periodic properties (5.1–5.6)
  06-deriving.tex                deriving new cycle integrals (6.1–6.10)
  07-conclusion.tex              conclusion recap and future work
  08-appendix.tex                Scala excerpts A.1–A.16
references.bib                   seven cited works
output/pdf/                      built by `just arxiv-pdf` (generated,
                                 untracked)
```

## Build

```bash
just arxiv-pdf integral-cycle
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch output directory under `$TMPDIR` and writes
`output/pdf/integral-cycle.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (Ghostscript `png16m` and
   `txtwrite` when Poppler is unavailable).
3. Content parity against `articles/chapter4/integral-cycle.md`: headings,
   statements, equations and their rows, code excerpts, references, and
   links.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 08-appendix.tex
references.bib
main.bbl                         generated; include so arXiv need not run BibTeX
```

Build it with a staging directory so the generated `main.bbl` is included
without polluting the package root:

```bash
stage=$(mktemp -d)
cp main.tex references.bib "$stage/"
cp -r sections "$stage/"
cp "${TMPDIR:-/tmp}/arxiv-build-integral-cycle/main.bbl" "$stage/"
tar czf output/arxiv-integral-cycle-source.tar.gz -C "$stage" \
    main.tex sections references.bib main.bbl
```

Compile the extracted archive once in a clean temporary directory before
uploading. The author performs the actual arXiv submission; this package only
prepares the source.
