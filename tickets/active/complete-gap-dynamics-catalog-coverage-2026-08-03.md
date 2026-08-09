# Complete Gap Dynamics Catalog Coverage

**Created:** 2026-08-03
**Updated:** 2026-08-03
**Status:** Complete
**Depends on:** `update-final-program-articles-2026-08-03.md` (complete;
Markdown-only, recorded Stainless baseline 30 valid / 0 invalid / 0 unknown)

## START HERE

Complete the review-ready Gap Dynamics v2 by adding canonical Properties #2
and #13, separating Property #25's exact conservation law from Property #66's
terminal quadratic consequence, and adding a one-row-per-property coverage
appendix for the 86-property sieve-sequence catalog. Do not modify published
`articles/chapter6/gap-dynamics.md`.

## Related Tickets

- `update-final-program-articles-2026-08-03.md` — created and completed the
  two current review drafts. Its main lesson is that mechanical Markdown
  validity is not proof completeness.
- `verify-19-21-escape-wall-2026-07-27.md` — developed Properties #25 and
  #66--#82 and records the capacity-route classifications summarized by the
  planned coverage appendix.

## Related Articles

- `articles/chapter6/gap-dynamics-v2.md` — only article to modify.
- `articles/chapter6/gap-dynamics.md` — published v1; keep unchanged.
- `articles/draft/draft-relaxed-almost-prime-sieve-sequence.md` — already
  contains Properties #84--#86; reference it from the coverage appendix.
- `articles/learnings/learnings-capacity-argument.md` — summary treatment for
  the #66--#83 investigation chain, not a replacement for canonical proofs.

## Goal

Make Gap Dynamics v2 complete with respect to the newly identified structural
omissions and make the article/canonical-note boundary discoverable for every
numbered sieve-sequence property. Completion requires full three-form article
treatment for #2, #13, and #25/#66, plus an accurate coverage row for every
property #1--#86.

## Strategy

Add one theorem section at a time in dependency order. Property #2 follows the
global count/copy-index theorems; Property #13 follows rotation and closes the
complete-period copy-or-merge group. In §5, retain the existing telescoping
proof but label it Property #25 and make #66 the separate weighted-Cauchy
corollary. Generate the coverage appendix from the canonical catalog, then
manually classify article treatment so related refinements are not mislabeled
as duplicate proofs.

## Current State

- Gap Dynamics v2 fully treats #1--#8, #12, #13, #66, #82, and #83,
  including the newly added §3.4 and §3.6 treatments of Properties #2 and #13.
- Property #2 now derives the four distinct forbidden copy classes (including
  incoming primes 5 and 7), excludes newly created `(2,4,2)` clusters, proves
  `C_(rM)=(r-4)C_M`, and states the global-to-local limitation. Stainless
  packaging remains pending, as the article says explicitly.
- Property #13 now proves the global copy-or-merge stable-absence implication,
  its induction over later stages, and its non-localization limitation.
- Section 5 now separates Property #25's exact identity
  `sum w_i b_i=T-N_m` from Property #66's weighted-Cauchy lower bound and
  candidate #24's still-open infinite-head hypothesis. Both are explicitly
  marked as mathematically proved with Stainless packaging pending.
- The introduction map, conclusion recap, References, and Appendix A now
  include #2, #13, and #25 and preserve #25/#66 as separate results.
- Appendix B now contains one linked row for every Property #1--#86. Its
  generated audit reports 86 unique continuous rows, uniform table shape,
  and 104 resolved local links.
- All changes are Markdown-only. Recorded Stainless baseline is 30 valid,
  0 invalid, 0 unknown.

## What Is Learned

- Similar algebra at different quantifier scopes is not a duplicate theorem:
  #1, #3, and #4 are global, batched, and one-filter copy-index statements.
- #82 is a sharp arbitrary-interval filter-7 result; #83 is a general
  complete-block energy bridge with partial boundaries. Neither subsumes the
  other.
- #84 and #86 constrain different divisibility variables (`m|n` versus
  `d|n+2`) and must remain separate.
- A coverage appendix should identify where a proof is treated, not reproduce
  every canonical property note inside the article.
- Property #25 is the signed conservation identity; Property #66 is a genuine
  corollary using a quadratic majorant. Keeping them under one heading hid
  which part was exact bookkeeping and which part imposed new strength.
- Properties #67--#81 are classified collectively in Capacity Learnings
  §22.2; the appendix says explicitly that this summary does not replace each
  canonical proof note.

## Failed Paths

- **Malformed LaTeX while inserting Property #2:** the first endpoint display
  lost the backslashes in `\qquad`. Source inspection caught it before the
  micro-step was accepted; it was corrected without changing the proof.
- **Rendered excerpt appeared to omit a §5 closing fence:** raw numbered
  source proved the fence was already present. The attempted insertion did
  not apply and changed nothing; future fence checks should inspect raw fence
  line numbers rather than rendered excerpts.
- **References patch skipped its visible pre-execution gate:** the patch was
  immediately stopped and audited; all ten targets exist and its content is
  correct. This was a pipeline-order failure, not a mathematical or Markdown
  failure. Every later modifying action must emit all three gates first.
- **Conclusion and ticket patches initially failed to parse:** LaTeX and
  literal Markdown bullet characters were mistaken for patch syntax. Neither
  failure changed a file; narrower correctly prefixed hunks succeeded within
  the three-attempt limit.
- **Initial whole-article validator was not portable:** the installed Ruby
  lacks `Array#tally`, and multiline Markdown links included whitespace in
  raw targets. Replacing `tally` with explicit hashes and normalizing target
  whitespace produced the valid 150/150 link result.
- **Treat the previous 14-property article matrix as complete:** failed
  because it omitted #2, #13, and the explicit #25 label despite their direct
  relevance. Retry only with a full catalog-to-article audit.
- **Add all 86 properties as full sections:** rejected because most are
  refinements or negative-route classifications and would obscure the main
  theorem spine. Retry only for an individual property shown to be a required
  dependency or reader-expected structural theorem.

## Open Concerns

- No open concern remains for this article-completion ticket. The mathematical
  relative-energy, partial-boundary, and unbounded-chain obligations remain
  open exactly as stated in the article.

## Validation

- Claim-by-claim readback passed for Properties #2, #13, #25, and #66.
- Appendix B has exactly 86 continuous unique rows; treatment counts are
  14 full here, 3 full in the almost-prime draft, 15 collectively summarized,
  and 54 canonical-note-only.
- All 150 normalized article links resolve; 172 fences are balanced; all 44
  headings are unique; no trailing whitespace or ticket references exist.
- Verification wording preserves the foundation/property distinction.
- Published `articles/chapter6/gap-dynamics.md` has a zero-byte diff.
- Markdown-only changes did not rerun Stainless; recorded baseline remains
  30 valid, 0 invalid, 0 unknown.

## Implementation Plan

1. Add Property #2 after the complete-period count/copy theorems.
2. Add Property #13 after rotation invariance.
3. Split §5 into Property #25 conservation and Property #66 terminal energy.
4. Update introduction, conclusion, references, and evidence map.
5. Add and validate the complete #1--#86 coverage appendix.

## Next Action

None for this ticket. Gap Dynamics v2 is ready for expert review; any further
work should address the explicitly open arithmetic theorem rather than article
coverage.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-03 | The catalog/article audit found three structural omissions: #2, #13, and the explicit #25 label. Related theorem chains are mostly refinements rather than literal duplicates. | Add Property #2 first, then update persistent state. |
| 2026-08-03 | Property #2 is an exact complete-period recurrence: four distinct endpoint classes destroy four of `r` copies, while positivity/evenness and filter 3 prevent new `(2,4,2)` clusters. | Added and source-validated §3.4; proceed to Property #13. |
| 2026-08-03 | Property #13 is a global one-way extinction theorem: under no-2, copied gaps are at least 4 and merged gaps at least 8; it says nothing about a selected window when the global count is positive. | Added and source-validated §3.6; proceed to the #25/#66 split. |
| 2026-08-03 | The exact conservation law (#25) and its weighted-Cauchy terminal corollary (#66) have different logical strength and open obligations. | Split §5 at the conservation identity and gave both theorems independent status/evidence blocks. |
| 2026-08-03 | Framing is only accurate when the theorem map, conclusion, references, and evidence table are all synchronized with body headings. | Updated all four; recorded and audited one skipped pre-execution gate before continuing. |
| 2026-08-03 | The canonical catalog is continuous through #86; only 14 properties are fully treated here, #84--#86 are fully treated in the almost-prime draft, and #67--#81 receive a collective capacity-audit summary. | Added Appendix B and validated 86 unique rows plus 104 resolved links. |
| 2026-08-03 | Whole-article validation must normalize multiline Markdown targets and avoid runtime-version assumptions. | Confirmed 150/150 links, balanced fences, unique headings, clean whitespace/status language, 30/30 recorded verification, and no v1 modification; marked complete. |
