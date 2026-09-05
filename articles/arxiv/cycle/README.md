# cycle — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Formal Verification of Cyclic
Lists*, converted from the canonical Markdown edition
[`articles/chapter4/cycle.md`](../../chapter4/cycle.md). The Markdown article
remains the frozen source edition; this package is a reviewed, one-time
conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                         document setup, metadata, Scala listing
                                 style, and section assembly
sections/
  00-abstract.tex                abstract and license notice
  01-introduction.tex            introduction and related work
  02-preliminaries.tex           notation and supporting definitions
  03-cycle-definitions.tex       recursive, modulo, and memory cycles
  04-cycle-equivalence.tex       base and inductive equivalence proofs
  05-cycle-properties.tex        cycle properties (5.1–5.12)
  06-conclusion.tex              conclusion and future work
  07-appendix.tex                Scala excerpts and verification log
figures/cycle-classes.png        cycle-representation class diagram
references.bib                   five cited works
output/pdf/                      built by `just arxiv-pdf` (generated,
                                 untracked)
```

The Mermaid source for the class diagram is retained as
`figures/cycle-classes.mmd`; arXiv needs only the rendered PNG.

## Build

```bash
just arxiv-pdf cycle
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch output directory under `$TMPDIR` and writes
`output/pdf/cycle.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (Ghostscript `png16m` and
   `txtwrite` when Poppler is unavailable).
3. Content parity against `articles/chapter4/cycle.md`: headings, statements,
   equations and their rows, code excerpts, references, links, and the class
   diagram.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 07-appendix.tex
figures/cycle-classes.png
references.bib
main.bbl                         generated; include so arXiv need not run BibTeX
```

Build it with a staging directory so the generated `main.bbl` is included
without polluting the package root:

```bash
stage=$(mktemp -d)
mkdir -p "$stage/figures"
cp main.tex references.bib "$stage/"
cp -r sections "$stage/"
cp figures/cycle-classes.png "$stage/figures/"
cp "${TMPDIR:-/tmp}/arxiv-build-cycle/main.bbl" "$stage/"
tar czf output/arxiv-cycle-source.tar.gz -C "$stage" \
    main.tex sections figures references.bib main.bbl
```

Compile the extracted archive once in a clean temporary directory before
uploading. The author performs the actual arXiv submission; this package only
prepares the source.
