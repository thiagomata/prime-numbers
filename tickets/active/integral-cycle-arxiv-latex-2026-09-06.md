# integral-cycle arXiv LaTeX package

**Created:** 2026-09-06
**Status:** In progress — skeleton staged; converting unit-by-unit per
`articles/arxiv/CONVERSION_GUIDE.md`
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

## Next Action

Stage main.tex + references.bib + section stubs; convert 00+01; compile.

## Learning Log

- (empty)
