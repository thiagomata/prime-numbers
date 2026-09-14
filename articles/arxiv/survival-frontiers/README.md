# survival-frontiers — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Survival Frontiers in Balanced
2-Gap Companion Processes*, converted from the canonical Markdown edition
[`articles/chapter7/survival-frontiers.md`](../../chapter7/survival-frontiers.md).
The Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                        document setup, metadata, section assembly
sections/
  00-abstract.tex                abstract
  01-introduction.tex            introduction + 2-focused heatmap views
  02-preliminaries-companion-models.tex
                                 roles, populations, balanced companion models
  03-relative-hazard-survival-frontiers.tex
                                 relative-hazard identities + phase diagram
  04-absolute-share-mixtures.tex adversarial/random parent phase diagrams
  05-allocation-and-the-protective-parent.tex
                                 allocation bounds + protective parent policy
  06-allocation-mechanisms-and-local-damage.tex
                                 allocation mechanisms and local damage
  07-exact-quota-companion-processes.tex
                                 exact-quota and biased-quota companions
  08-relation-to-the-real-sieve.tex
                                 relation to the real sieve
  09-limitations.tex             limitations
  10-conclusion.tex              conclusion
  13-appendix-a-proof-records.tex
                                 Appendix A: selected companion proof records
references.bib                  Sieve Sequence companion article entry
figures/
  gap-heatmap-2focused.pdf           independent 2-focused snapshots (Sec. 1)
  gap-heatmap-2focused-aligned.pdf   shared-safe-2 aligned compression (Sec. 1)
  phase-transition-window.pdf        fixed relative-hazard factors (Sec. 3)
  phase-transition-head.pdf          Borel-Cantelli head threshold (Sec. 3)
  per-sequence-frontier.pdf          per-sequence survival frontier (Sec. 8)
  frontier-comparison-stages.pdf     frontier comparison across stages (Sec. 8)
  full-cycle-destruction.pdf         full-cycle destruction (Sec. 8)
  full-cycle-survival.pdf            full-cycle survival (Sec. 8)
  fixed-lineage-hazard.pdf           fixed-lineage hazard (Sec. 9)
output/pdf/survival-frontiers.pdf   built by `just arxiv-pdf` (generated,
                                    untracked)
```

## Build

```bash
just arxiv-pdf                     # build every article under articles/arxiv/
just arxiv-pdf survival-frontiers  # build this one
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch outdir under `$TMPDIR` and writes
`output/pdf/survival-frontiers.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (ghostscript
   `png16m`/`txtwrite` when poppler is unavailable).
3. Content parity against `articles/chapter7/survival-frontiers.md`:
   headings, statements, equations (blocks and rows), labels, links, and
   tables.

## arXiv Packaging

The upload archive contains only the files arXiv requires:

```text
main.tex
sections/00-abstract.tex ... 13-appendix-a-proof-records.tex
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
cp "${TMPDIR:-/tmp}/arxiv-build-survival-frontiers/main.bbl" "$stage/"
tar czf output/arxiv-survival-frontiers-source.tar.gz -C "$stage" \
    main.tex sections figures references.bib main.bbl
```

Then compile the archive contents once from a clean temporary directory
before uploading. The author performs the actual arXiv submission; this
package only prepares the source.
