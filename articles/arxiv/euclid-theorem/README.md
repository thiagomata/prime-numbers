# euclid-theorem — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Formal Verification of Euclid's
Theorem on the Infinitude of Primes*, converted from the canonical
Markdown edition
[`articles/chapter5/euclid-theorem.md`](../../chapter5/euclid-theorem.md).
The Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                         document setup, metadata, Scala listing
                                  style, and section assembly
sections/
  00-abstract.tex                abstract and license notice
  01-introduction.tex            introduction
  02-preliminaries.tex           key definitions and finite prime operations (2.1-2.2)
  03-proof-strategy.tex          the four-stage Euclid construction (3.1-3.4)
  04-supporting-lemmas.tex       supporting verified lemmas (4.1-4.4)
  05-verification-status.tex     verification status
  06-related-work.tex            related work
  07-conclusion.tex              conclusion recap and future work
  08-appendix.tex                Scala excerpts A.1-A.3 and verification log
references.bib                   eight cited works
output/pdf/                      built by `just arxiv-pdf` (generated,
                                  untracked)
```

## Build

```bash
just arxiv-pdf euclid-theorem
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch output directory under `$TMPDIR` and writes
`output/pdf/euclid-theorem.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (Ghostscript `png16m` and
   `txtwrite` when Poppler is unavailable).
3. Content parity against `articles/chapter5/euclid-theorem.md`: headings,
   statements, equations and their rows, code excerpts, references, and
   links.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 08-appendix.tex
references.bib
main.bbl                          generated; include so arXiv need not run BibTeX
```

Build it with a staging directory so the generated `main.bbl` is included
without polluting the package root:

```bash
stage=$(mktemp -d)
cp main.tex references.bib "$stage/"
cp -r sections "$stage/"
cp "${TMPDIR:-/tmp}/arxiv-build-euclid-theorem/main.bbl" "$stage/"
tar czf output/arxiv-euclid-theorem-source.tar.gz -C "$stage" \
    main.tex sections references.bib main.bbl
```

Compile the extracted archive once in a clean temporary directory before
uploading. The author performs the actual arXiv submission; this package
only prepares the source.
