# relaxed-almost-prime — arXiv LaTeX Package

LaTeX source for the arXiv submission of *Relaxed Almost-Prime Production in
Sieve Sequences*, converted from the canonical Markdown edition
[`articles/chapter6/relaxed-almost-prime.md`](../../chapter6/relaxed-almost-prime.md).
The Markdown article remains the frozen source edition; this package is a
reviewed, one-time conversion. Conversion conventions live in
[`../CONVERSION_GUIDE.md`](../CONVERSION_GUIDE.md).

## Layout

```text
main.tex                        document setup, metadata, section assembly
sections/
  00-abstract.tex                abstract
  01-introduction.tex            introduction, scope, relation to known results
  02-preliminaries.tex           sieve vocabulary, relaxed candidate weight
  03-relaxed-positivity-implies-production.tex
                                 Theorem 1: relaxed positivity implies prime-plus-P2
  04-exact-divisor-local-factor.tex
                                 Theorem 2: exact divisor local factor + boundary remainder
  05-shifted-divisor-discrepancy.tex
                                 Theorem 3: shifted-divisor prime-progression reduction
  06-exact-bilinear-character-decomposition.tex
                                 Theorem 4: exact bilinear character decomposition
  07-refuted-route-scalar-density-type-ii.tex
                                 Theorem 5: refutation of the scalar-density Type-II shortcut
  08-remaining-program.tex       the correct remaining analytic program
  09-claim-boundary.tex          what is and is not proved
  10-conclusion.tex              conclusion
  13-appendix-a-evidence-status.tex
                                 Appendix A: evidence and verification status
references.bib                  6 internal cross-references + 4 external
                                 sieve-theory literature entries (Chen,
                                 Halberstam-Richert, Iwaniec-Kowalski,
                                 Friedlander-Iwaniec)
output/pdf/relaxed-almost-prime.pdf   built by `just arxiv-pdf` (generated,
                                       untracked)
```

No figures: this article is pure analytic number theory (no diagrams in the
Markdown source).

## Build

```bash
just arxiv-pdf                        # build every article under articles/arxiv/
just arxiv-pdf relaxed-almost-prime   # build this one
```

The recipe runs `latexmk -g -pdf -interaction=nonstopmode -halt-on-error`
with a scratch outdir under `$TMPDIR` and writes
`output/pdf/relaxed-almost-prime.pdf`.

Manual equivalent:

```bash
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Validation

1. Exit code 0 and a log free of `Warning`, `Error`, `Overfull`,
   `Underfull`, `undefined`, and `Missing`.
2. Every page rendered and visually inspected (ghostscript
   `png16m` when poppler is unavailable) -- confirmed the `\mid` divisor
   symbol (thin at low DPI) renders correctly at 300 DPI.
3. `just arxiv-parity relaxed-almost-prime`: headings, math-block tags,
   URLs, and (there are none) verified-identifier citations all PASS
   against `articles/chapter6/relaxed-almost-prime.md`.

## Conversion notes specific to this package

- The Markdown's two-tier References section (items 1-6: internal
  cross-references to `properties/`/`candidates/` working notes and the
  companion Sieve Sequence article; "External references:" 7-10: the sieve
  literature) is rendered as a single unified bibliography via
  `references.bib` + `\bibliography`, matching the pattern already used by
  `survival-frontiers` -- not a separate manual list plus a second
  auto-generated heading.
- Section 3's Markdown heading contains inline math (`Prime-Plus-$P_2$`).
  A `\texorpdfstring{$P_2$}{P_2}` fallback still trips hyperref's "Token not
  allowed in a PDF string" warning on the bare underscore, and escaping it
  (`P\_2`) desyncs the heading from the Markdown's own literal `P_2` text
  under the parity checker's title normalization (which does not strip
  backslashes). Resolved by renaming the heading to the plain-English
  synonym the article already uses in its own prose --
  "prime-plus-almost-prime production" -- in both the Markdown and the
  `.tex`, avoiding math in the section title entirely rather than fighting
  the pdfstring/underscore conflict.
- The Appendix A heading is titled `Evidence And Verification Status` in
  the `.tex` (no "Appendix A:" prefix) to match `gap-dynamics`'s precedent:
  the parity checker's title-normalization only strips the colon-style
  `Appendix X:` prefix on the Markdown side, so the `.tex` section title
  must omit it to match after normalization (`survival-frontiers` avoids
  this by using period-style `Appendix A.` on both sides instead).
