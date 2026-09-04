# list — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Using Formal Verification to Prove
Properties of Lists Recursively Defined*, converted from the canonical
Markdown edition [`articles/chapter3/list.md`](../../chapter3/list.md). The
Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                        document setup, metadata, Scala listing
                                style, section assembly
sections/
  00-abstract.tex               abstract + license notice placement
  01-introduction.tex           introduction and related work
  02-definitions.tex            list construction through product (2.1-2.9)
  03-index-access.tex           index and access properties (3.1-3.3)
  04-slice.tex                  slice properties (4.1-4.4)
  05-sum.tex                    sum properties (5.1-5.5)
  06-product.tex                product properties (6.1-6.5)
  07-product-divisibility.tex   product divisibility properties (7.1-7.3)
  08-bound-order.tex            bound and order properties (8.1-8.7)
  09-equivalence.tex            slice equivalence lemma (9.1)
  10-shifted-list.tex           shifted-list properties (10.1-10.3)
  11-rotation.tex               rotation properties (11.1-11.2)
  12-conclusion.tex             conclusion recap and future work
  13-limitations.tex            limitations (14.1-14.5)
  14-appendix.tex               Appendix A (A.1-A.24 Scala excerpts) and
                                Appendix B (verification log pointer)
references.bib                  Hamza et al., Wikipedia, Rocq stdlib, Lean
                                mathlib entries
output/pdf/                     built by `just arxiv-pdf` (generated,
                                untracked)
```

## Build

```bash
just arxiv-pdf         # build every article under articles/arxiv/
just arxiv-pdf list    # build this one
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch outdir under `$TMPDIR` and writes `output/pdf/list.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (ghostscript
   `png16m`/`txtwrite` when poppler is unavailable).
3. Content parity against `articles/chapter3/list.md`: headings,
   statements, equations (blocks and rows), code excerpts, references, and
   links.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 14-appendix.tex
references.bib
main.bbl                 generated; include so arXiv need not run BibTeX
```

Build it with a staging directory, so the generated `main.bbl` is included
without polluting the package root:

```bash
stage=$(mktemp -d)
cp main.tex references.bib "$stage/"
cp -r sections "$stage/"
cp "${TMPDIR:-/tmp}/arxiv-build-list/main.bbl" "$stage/"
tar czf output/arxiv-list-source.tar.gz -C "$stage" \
    main.tex sections references.bib main.bbl
```

Then compile the archive contents once from a clean temporary directory
before uploading. The author performs the actual arXiv submission; this
package only prepares the source.
