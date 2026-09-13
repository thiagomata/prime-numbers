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
2. ~~Coverage-audit requirement: cite the six proved `companions/properties/`
   lemmas by path~~ REVERSED per owner (pattern C: never cite internal notes
   as authority from an article).
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
| 2026-09-13 | Owner directive: articles must be self-contained. Generalized into the no-ticket-references rule (AGENTS.md): never cite internal working materials as authority; permitted links are published siblings, verified sources, provenance, external literature. Audit of the draft confirms compliance — only data/candidates CSVs (datasets, not research notes) matched the internal-ish paths. | Rule generalized; Phase 1 self-containment checkpoint PASS. |
| 2026-09-13 | The 2026-09-01 coverage-audit item "cite the companions/properties records by path" is REVERSED: adding those links reintroduced pattern C (internal notes cited as mathematical authority), which the repo ranked as its most severe finding and which the gap-dynamics de-drafting just purged. The article's own appendix proofs are the authority; the companion records stay working notes. | Record-citation sentences removed from A.1-A.4, A.6, and 5.1; zero companions/properties links remain. |
| 2026-09-13 | Pattern D (bare §N refs) was ALREADY satisfied — 35/35 in-file refs linked during the post-audit revision. The only bare §s were inside cross-article link labels ("[Gap Dynamics §5.2](url)"), where plain text is correct. A regex sweep without a link-text exclusion corrupted 4 of them into nested links (partial §5 match of §5.2). | Repaired all 4 on retry; verified working tree identical to HEAD; lesson: exclude `\[...\]\(...\)` spans before any ref rewriting, and never rewrite what link labels intentionally contain. |
