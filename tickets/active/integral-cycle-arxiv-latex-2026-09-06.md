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

## Learning Log

- (empty)
