# Article review comparison - 2026-06-17

## Goal

Evaluate the Markdown articles in `articles/` one by one and compare each assessment with the existing notes in `tickets/article-reviews/`.

## Current State

Baseline verification passed before this review:

- Command: `just verify`
- Result: `total: 5499 valid: 5499 (5480 from cache, 19 trivial) invalid: 0 unknown: 0`

Existing review notes are present for active articles, draft articles, and learning articles under `tickets/article-reviews/`.

## Expected State

Produce concise feedback for each active, draft, and learning article, including:

- Publication readiness
- Main strengths
- Main blockers or gaps
- Whether the existing review note is still aligned, stale, or incomplete
- Suggested next action

Deprecated articles are reviewed as archive material rather than publication candidates.

## Alternatives Considered

- Reuse the 2026-06-15 review verbatim: faster, but it would miss whether the current articles changed.
- Read only abstracts and conclusions: useful for framing checks, but not enough for proof completeness.
- Compare article headings, verification-code references, and review notes: balanced for this feedback request.

## Risks

- Some article claims may depend on source-level `.holds` functions not inspected in depth during this pass.
- Existing review notes may intentionally track future edits rather than current article defects.
- Draft and learning articles may be exploratory, so publication-readiness criteria need to be applied differently.

## Assumptions

- The user wants feedback only, not edits to the articles.
- `tickets/article-reviews/` is the authoritative existing review folder.
- Project article rules from `AGENTS.md` are the evaluation criteria.

## Hypotheses

- The finished reference articles should mostly align with the prior review notes.
- Gap-dynamics and learning articles are more likely to contain open or unverified material.
- Draft articles should be judged on clarity of scope and explicit verification status rather than immediate publication readiness.

## Validation Plan

- Inventory articles and review notes.
- Read each article's title, abstract, section structure, proof/code markers, and conclusion.
- Read the corresponding review note when one exists.
- Compare current article state with prior feedback.
- Report feedback one article at a time.

## Related Tickets

- `tickets/article-evaluation-2026-06-15.md` - prior article evaluation and source of the current review-note set.
- `tickets/article-consolidation.md` - earlier article organization and publication-readiness context.
- `tickets/gap-cycle-integration.md` - relevant to gap-cycle and gap-dynamics claims.
- `tickets/r3-r5-r12-gaps-nonempty-positive.md` - relevant historical context for unresolved gap-positivity proof work.

## Progress Log

- 2026-06-17: Created after green baseline verification and after finding the 2026-06-15 article evaluation ticket plus existing review notes.
- 2026-06-17: Compared active, draft, and learning articles against `tickets/article-reviews/`. Most June 17 review executions are reflected in current articles. Remaining notable stale items: `articles/modulo.md` still lacks the newer property-index/source-reference/verification-log style, and `articles/sieve-sequence.md` still reports the older 5303 verification-count framing instead of the current 5499 repository-wide run.
- 2026-06-17: User clarified that repository-wide verification-condition counts should not be treated as important article content because they change whenever unrelated proofs are added. Plan updated: replace brittle global-count claims with stable "described properties are verified" wording, and normalize missing proof-ending black-square markers where this matches article style.
- 2026-06-17: User identified `articles/gap-dynamics.md` as still publication-misaligned: draft properties lack complete three-form presentation, failed properties add noise, and the article organization does not match the finished articles. Plan updated: remove draft/failed properties from the main article, preserve them in learnings, and refocus the article on the open local-density boundary.
- 2026-06-17: Refocused `articles/gap-dynamics.md` on the open local-density boundary, removed the incomplete draft property sections and stale verification appendix, and added `articles/learnings/learnings-capacity-argument.md` Section 18 to preserve the removed gap-dynamics claims with their current status. Verification stayed green after each documentation change.
- 2026-06-17: User identified a missing foundational gap-dynamics property: filtering changes gaps only by merging neighboring gaps around deleted survivor points. Consequence to investigate: in post-2 layers, where gaps are positive even values, if all 2-gaps are eliminated then neighbor merges cannot recreate a 2-gap; more generally, reachable future gap values can be reasoned about by possible contiguous neighbor sums. Need search source for existing verified merge/filter lemmas before deciding article status.
- 2026-06-17: User clarified that gap dynamics should be framed as a consequence of the Sieve Sequence itself: each finite sequence state generates the next state, and the chain of states generates the primes. Updated `articles/gap-dynamics.md` to make gap dynamics the induced behavior of the `nextFiltered` to `nextGaps` transition rather than a detached boundary note.
- 2026-06-17: User requested adding the global 2-gap count-growth argument to `articles/gap-dynamics.md` because it is a key gap-dynamics property even though it is global rather than local. User also clarified that final articles should not cite learning docs or tickets; those are internal helpers only. Plan: include the global proof directly in the article, mark Stainless status honestly as pending, and remove reader-facing references to learnings/tickets from the article.
