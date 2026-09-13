# Survival Frontiers — promotion from draft to chapter article

**Created:** 2026-09-13
**Branch:** `feature/draft-to-article`
**Depends on:** survival-frontiers-article-review-2026-09-13 (deep audit,
complete); review-draft-articles-2026-08-15 (notes/); arxiv-sync rule;
CONVERSION_GUIDE

## Goal

Promote `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md`
(*Survival Frontiers in Balanced 2-Gap Companion Processes*, 3087 lines) to
a published chapter article with PDF: `articles/chapter7/survival-frontiers.md`
+ `articles/arxiv/survival-frontiers/` package, zero-warning build, parity PASS.

## Strategy

Phase 1 — markdown editing pass in draft/ (one commit each):
1. Front matter: full author name, ORCID, license `../LICENSE`, status date.
2. Coverage-audit requirement: cite the six proved `companions/properties/`
   lemmas by path (Appendix A records).
3. Internal §N references -> anchored Markdown links (~32, review pattern D).
4. Abstract: attach spatial premise to the square-window claim (item 6.6).
5. Optional: kappa/w consolidation (6.2) — decide later.

Phase 2 — conversion per CONVERSION_GUIDE: move md to chapter7/, build the
arXiv package section by section, `just arxiv-pdf`, `just arxiv-parity`,
.parity-skip for the four master-pinned figure URLs + verify.log quirks.

## Current State

Branch created; ticket opened. Phase 1.1 in progress.

## Open Concerns

- Chapter number 7 is free (chapters 2-6 published).
- File name `survival-frontiers` proposed; confirm at conversion time.
- Appendix A mirrors body proofs — LaTeX edition page count will grow;
  acceptable (proof-record surface, review 6.2 disposition).

## Learning Log

| Date | Learning | Action |
|---|---|---|
