# modulo — arXiv LaTeX Package

LaTeX source for the arXiv submission of
*Division and Modulo from Recursive Normalization*, converted from the
canonical Markdown edition [`articles/chapter2/modulo.md`](../../chapter2/modulo.md).
The Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex              document setup, metadata, Scala listing style,
                      conditional assembly of all sections
sections/
  00-abstract.tex     abstract + license notice placement
  01-introduction.tex introduction and limitations
  02-definitions.tex  traditional and recursive definitions
  03-shift-invariance.tex  linear-shift invariant and div/mod operations
  04-properties.tex   Section 6 properties (6.1-6.14)
  05-conclusion.tex   conclusion recap and future work
  06-appendix.tex     A.1-A.4 Scala excerpts and verification log
references.bib        Hardy & Wright entry
output/pdf/           built by `just arxiv-pdf` (generated, untracked)
```

Every section include in `main.tex` is wrapped in `\IfFileExists`, so a
partially converted package still compiles.

## Build

```bash
just arxiv-pdf            # build every article under articles/arxiv/
just arxiv-pdf modulo     # build this one
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch outdir under `$TMPDIR` and writes
`output/pdf/modulo.pdf`. The `-g` is required: latexmk does not track the
`\IfFileExists` probes, so a newly added section file would otherwise be
missed.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (ghostscript
   `png16m`/`txtwrite` when poppler is unavailable).
3. Content parity against `articles/chapter2/modulo.md`: headings,
   statements, equations, code excerpts, references, and links.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 06-appendix.tex
references.bib
main.bbl                 generated; include so arXiv need not run BibTeX
```

Build it with a staging directory, so the generated `main.bbl` is included
without polluting the package root:

```bash
stage=$(mktemp -d)
cp main.tex references.bib "$stage/"
cp -r sections "$stage/"
cp "${TMPDIR:-/tmp}/arxiv-build-modulo/main.bbl" "$stage/"
tar czf output/arxiv-modulo-source.tar.gz -C "$stage" \
    main.tex sections references.bib main.bbl
```

Then compile the archive contents once from a clean temporary directory
before uploading. The author performs the actual arXiv submission; this
package only prepares the source.
