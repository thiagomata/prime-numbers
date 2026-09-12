# sieve-sequence — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Formal Verification of Sieve
Sequence Stages and Their Transitions*, converted from the canonical
Markdown edition
[`articles/chapter6/sieve-sequence.md`](../../chapter6/sieve-sequence.md).
The Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                          document setup, metadata, Scala listing
                                   style, and section assembly
figures/
  hit-miss-matrices.pdf           vector conversion of charts/hit-miss-matrices.svg
sections/
  00-abstract.tex                 abstract and license notice
  01-introduction.tex             introduction
  02-preliminaries.tex            stage definition, period/gap cycle, evidence map (2.1-2.4)
  03-linear-stage-semantics.tex   accepted values, completeness, strict increase (3.1-3.2)
  04-period-and-cycle-reconstruction.tex
                                   block shift, gap-cycle reconstruction, repetition (4.1-4.3)
  05-installing-current-head-as-filter.tex
                                   survivor count, 2-gap lift law, copy-or-merge (5.1-5.4)
  06-next-stage.tex               next-head primality and next-stage agreement (6.1-6.4)
  07-exact-proof-boundary.tex     conditional assumptions and open problems
  08-open-proof-work.tex          open proof obligations
  09-conclusion.tex               conclusion recap
references.bib                    nine cited works
output/pdf/                       built by `just arxiv-pdf` (generated,
                                   untracked)
```

## Build

```bash
just arxiv-pdf sieve-sequence
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch output directory under `$TMPDIR` and writes
`output/pdf/sieve-sequence.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Figure

The Markdown embeds one SVG figure (`charts/hit-miss-matrices.svg`) by
GitHub-raw URL. pdfLaTeX cannot include raw SVG, so the figure was
converted once to a vector PDF (`cairosvg`, 2x scale) and committed at
`figures/hit-miss-matrices.pdf`; `\includegraphics` draws it like any
other image asset. If the source SVG changes, regenerate with:

```bash
python3 -c "import cairosvg; cairosvg.svg2pdf(url='charts/hit-miss-matrices.svg', write_to='articles/arxiv/sieve-sequence/figures/hit-miss-matrices.pdf', scale=2)"
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (Ghostscript `png16m`).
3. Content parity against `articles/chapter6/sieve-sequence.md`: headings,
   statements, equations and their rows, code excerpts, the figure,
   references, and links.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 09-conclusion.tex
figures/hit-miss-matrices.pdf
references.bib
main.bbl                          generated; include so arXiv need not run BibTeX
```

Build it with a staging directory so the generated `main.bbl` is included
without polluting the package root:

```bash
stage=$(mktemp -d)
cp main.tex references.bib "$stage/"
cp -r sections figures "$stage/"
cp "${TMPDIR:-/tmp}/arxiv-build-sieve-sequence/main.bbl" "$stage/"
tar czf output/arxiv-sieve-sequence-source.tar.gz -C "$stage" \
    main.tex sections figures references.bib main.bbl
```

Compile the extracted archive once in a clean temporary directory before
uploading. The author performs the actual arXiv submission; this package
only prepares the source.
