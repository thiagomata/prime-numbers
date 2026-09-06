# integral — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Formal Verification of Discrete
Integration Properties from First Principles*, converted from the canonical
Markdown edition [`articles/chapter4/integral.md`](../../chapter4/integral.md).
The Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                        document setup, metadata, Scala listing
                                style, section assembly
sections/
  00-abstract.tex               abstract + license notice placement
  01-introduction.tex           introduction and related work
  02-preliminaries.tex          preliminaries and notation
  03-definition.tex             discrete integral definition (3.1-3.2)
  04-core-properties.tex        core integral properties (4.1-4.6)
  05-consistency-lemmas.tex     implementation consistency lemmas (5.1-5.5)
  06-limitations.tex            limitations
  07-conclusion.tex             conclusion recap and future work
  08-appendix.tex               Appendix A (A.1-A.8 Scala excerpts) and
                                Appendix B (verification log pointer)
references.bib                  list article and Rocq stdlib entries
output/pdf/                     built by `just arxiv-pdf` (generated,
                                untracked)
```

## Build

```bash
just arxiv-pdf         # build every article under articles/arxiv/
just arxiv-pdf integral  # build this one
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch outdir under `$TMPDIR` and writes
`output/pdf/integral.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (ghostscript
   `png16m`/`txtwrite` when poppler is unavailable).
3. Content parity against `articles/chapter4/integral.md`: headings,
   statements, equations (blocks and rows), code excerpts, references, and
   links.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 08-appendix.tex
references.bib
main.bbl                 generated; include so arXiv need not run BibTeX
```

Build it with a staging directory, so the generated `main.bbl` is included
without polluting the package root:

```bash
stage=$(mktemp -d)
cp main.tex references.bib "$stage/"
cp -r sections "$stage/"
cp "${TMPDIR:-/tmp}/arxiv-build-integral/main.bbl" "$stage/"
tar czf output/arxiv-integral-source.tar.gz -C "$stage" \
    main.tex sections references.bib main.bbl
```

Then compile the archive contents once from a clean temporary directory
before uploading. The author performs the actual arXiv submission; this
package only prepares the source.
