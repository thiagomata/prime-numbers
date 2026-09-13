# integral-cycle arXiv LaTeX package

**Created:** 2026-09-06
**Status:** Complete — all sections converted; compile green (31 pages,
zero warnings); parity checked; PDF rebuilt
**Branch:** `feature/article/integral-cycle`
**Depends on:** none (follow-on to the completed `cycle-arxiv-latex` /
`integral-arxiv-latex` conversions; same method, same house style)

## START HERE

Convert `articles/chapter4/integral-cycle.md` (*Formal Verification of
Cycle Integral Properties from First Principles*, 2003 lines) into an
arXiv LaTeX package at `articles/arxiv/integral-cycle/`, following
`articles/arxiv/CONVERSION_GUIDE.md`.

Section plan (order must mirror the Markdown numbering exactly):

- 00-abstract
- 01-introduction (§1 incl. Related work)
- 02-preliminaries (§2)
- 03-definitions (§3, 3.1–3.3)
- 04-core-properties (§4, 4.1–4.5)
- 05-periodic-properties (§5, 5.1–5.6)
- 06-deriving (§6, 6.1–6.10)
- 07-conclusion (§7 Conclusion + §8 Future Work)
- 08-appendix (Appendix A code excerpts)

## Current State

- Markdown fixes already on the branch: display name, reference [4]
  (modulo) archived link.
- references.bib: 7 entries (list, integral, cycle, modulo-viXra,
  Hardy & Wright, Lean Periodic, Lean Cycles).

## Current State (updated)

- All 9 section files converted; full document compiles green at
  31 pages with zero warnings/errors.
- Mechanical parity: 41/41 subsections, 16/16 Scala listings, all
  GitHub links preserved except the 4 intentional substitutions
  (references -> references.bib; Appendix B dropped as GitHub-only).
- Page-by-page visual review done for title page, conclusion recap,
  and appendix; no clipping or overflow visible.

## Sync 2026-09-13 (unit-cycle properties, Markdown -> LaTeX)

- The Markdown article gained §4.6 Unit-Cycle Generation of Consecutive
  Integers + Appendix A.17 (moved in from the draft bridge article per
  the chapter4 publish-prep ticket). Carried into the LaTeX package in
  the same unit of work (new `arxiv-sync` rule in AGENTS.md):
  - `04-core-properties.tex`: new Subsection 4.6 (claim, induction
    proof, strict-increase corollary, two source references, itemize
    bullet).
  - `01-introduction.tex`: verifies list extended to Subsections 4.1--4.6.
  - `07-conclusion.tex`: prose sentence + two recap equations
    ([Unit-Cycle Generation], [Unit-Cycle Strict Increase]).
  - `08-appendix.tex`: A.17 with both `assertCycleIntegralOfOnes`
    listings.
- One Overfull \hbox (10.5pt) surfaced in the A.17 subsection heading
  (two long identifiers on one line); fixed with the same `\\` title
  break pattern A.12 uses.
- PDF rebuilt: 33 pages (was 31), exit 0, zero-warning log; text-layer
  parity checked (ToC entry, §4.6 content, recap tags, A.17 listings);
  pages 7-8 visually verified clean.

## Learning Log

- Shared-column blowup in `aligned` with long [label] columns was the
  dominant overfull source; fixed case-by-case with the guide's
  escape hatches (continuation rows, per-row displays, inline labels).
- Listings package (this TeX Live) has no `breakanywhere` option; the
  one >80-char Scala line needed a per-listing
  `breakatwhitespace=false` override.
- Literal em-dash inside `lstlisting` is a fatal UTF-8 error under
  `columns=fixed`; code excerpts must be pure ASCII.
- Appendix subsections must NOT repeat the A.n prefix (LaTeX numbers
  appendix subsections automatically); long identifiers in headings
  need `\texorpdfstring` + `\allowbreak` camel-case breakpoints.
- (2026-09-13) A two-identifier appendix heading exceeds the line even
  with `\allowbreak` camel-case breaks — the fix is the A.12 pattern: a
  `\\` line break inside the `\texorpdfstring` display argument, one
  identifier per line.
- (2026-09-13) `just arxiv-pdf` now enforces the zero-warning gate
  itself: after each build it greps the temp-dir log for
  Warning/Error/Overfull/Underfull/undefined/Missing and exits 1 with
  the offending lines printed — the CONVERSION_GUIDE manual log-grep
  step is machine-enforced and the temp dir never needs to be inspected
  by hand. Validated: clean article passes silently; fake dirty log
  fails the gate.
