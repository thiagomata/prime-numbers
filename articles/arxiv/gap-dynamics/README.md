# gap-dynamics — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Structural Properties and Signed
Boundaries of 2-Gaps in Sieve Sequences*, converted from the canonical
Markdown edition [`articles/chapter6/gap-dynamics.md`](../../chapter6/gap-dynamics.md). The
Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                        document setup, metadata, Scala listing
                                style, section assembly
sections/
  00-abstract.tex               abstract
  01-introduction.tex           introduction
  02-preliminaries.tex          roles, populations, evidence boundary
  03-complete-period-two-gap-properties.tex
                                complete-period identities (3.1-3.6)
  04-local-certification.tex    local certification (4.1-4.4 + notation)
  05-weighted-harmful-excess-survival.tex
                                conservation + terminal criterion (5.1-5.2)
  06-why-capacity-envelope-exhausted.tex
                                exhaustion argument (6.1-6.7)
  07-exact-filter-seven-localization.tex
                                filter-7 localization
  08-open-estimates.tex         open estimates (8.1-8.2)
  09-copy-block-harmful-excess.tex
                                copy-block bridge to residue energy
  10-routes-classified.tex      classified routes + scale conflict
  11-almost-prime-program.tex   almost-prime program + Type-II barrier
  12-conclusion.tex             conclusion recap
  13-appendix-a-evidence-status.tex
                                evidence and verification status table
  15-appendix-c-proofs.tex      self-contained exhaustion proofs (C.1-C.6)
references.bib                  companion Sieve Sequence article entry
figures/
  gap-two-frequency.pdf         2-gap frequency curve (Section 3)
  gap-heatmap-2focused.pdf      2-focused compression heatmap (Section 3)
  gap-two-cluster-size.pdf      consecutive 2-gap distance (Section 4.2)
output/pdf/gap-dynamics.pdf     built by `just arxiv-pdf` (generated,
                                untracked)
```

## Build

```bash
just arxiv-pdf         # build every article under articles/arxiv/
just arxiv-pdf gap-dynamics   # build this one
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch outdir under `$TMPDIR` and writes `output/pdf/gap-dynamics.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (ghostscript
   `png16m`/`txtwrite` when poppler is unavailable).
3. Content parity against `articles/chapter6/gap-dynamics.md`: headings,
   statements, equations (blocks and rows), labels, links, and tables.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 15-appendix-c-proofs.tex
references.bib
main.bbl                 generated; include so arXiv need not run BibTeX
figures/*.pdf            embedded figures
```

Build it with a staging directory, so the generated `main.bbl` is included
without polluting the package root:

```bash
stage=$(mktemp -d)
cp main.tex references.bib "$stage/"
cp -r sections figures "$stage/"
cp "${TMPDIR:-/tmp}/arxiv-build-gap-dynamics/main.bbl" "$stage/"
tar czf output/arxiv-gap-dynamics-source.tar.gz -C "$stage" \
    main.tex sections figures references.bib main.bbl
```

Then compile the archive contents once from a clean temporary directory
before uploading. The author performs the actual arXiv submission; this
package only prepares the source.
