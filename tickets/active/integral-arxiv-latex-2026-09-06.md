# arXiv LaTeX — integral article

**Created:** 2026-09-06
**Branch:** `feature/article/integral`
**Status:** In progress — pre-conversion fixes applied; conversion not yet started

## Goal

Convert `articles/chapter4/integral.md` into an arXiv LaTeX package
at `articles/arxiv/integral/`, release with tag `integral-article-v1.0.0`,
then merge so `feature/article/cycle` can follow.

## Strategy

Same as the completed list/modulo/cycle conversions:
markdown source = frozen edition; standard article class; latexmk/pdf;
one unit per compile cycle; release with pinned links and Chapter 4
verify-log evidence (same tree, same 2995/0/0 totals).

## Current state

- Pre-conversion fixes 3 (References wording) and 5 (`:=` conversions)
  applied on this branch per author approval. Fixes 1 and 2 held;
  fix 4 (classDiagram) rejected.
- Branch `feature/article/integral` exists, based on master.
- Chapter 4 verify log is committed on `feature/article/cycle` and will be
  retrieved via `git show` at release time; no fresh Stainless run needed.

## Pending

Scaffold `articles/arxiv/integral/` and begin unit-by-unit conversion.
