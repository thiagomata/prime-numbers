# Article Stub Lemma Audit

## START HERE

Micro-goal: make article proof-code embedding follow the `cycle.md` pattern:
main sections keep prose, math, and source links; core proof bodies live in an
appendix only when they materially help the reader.

## Goal

Audit articles, starting with `articles/chapter4/integral-cycle.md`, for
stub-looking Stainless snippets such as:

```scala
def lemma(...): Boolean = {
  require(...)
  // theorem statement
}.holds
```

Replace them with real verified source snippets when available, or reframe the
property as pending/open when no verified proof exists.

## Current State

The integral-cycle article contains several snippets where the code block
visually looks like a verified `.holds` proof but the theorem is only a
comment. This is misleading even when the current source now contains a real
delegate or real proof elsewhere.

Related examples:

- `assertTwoGapSumEqualsDiff`
- `assertFirstSurvivorIsHead`
- `assertFilteredSumEqualsOriginalSum`

## Expected State

Published article snippets should not present commented conclusions as verified
proofs. If a property is verified, the article should show the real proof body
or link to the real source. If the article does not show code, it should avoid
claiming a stub is verification.

For readability, article sections should not inline every Scala proof body.
Use `articles/chapter4/cycle.md` as the style model: concise section-level
source links, small inline Scala only when it has a good signal/noise ratio,
plus Appendix A excerpts for longer core proof bodies worth keeping close to
the article.

## Similar Tickets

- `tickets/active/integral-cycle-dependency-map-framing-2026-07-22.md`
- `tickets/done/integral-cycle-examiner-review.md`
- `tickets/done/scientific-review-articles-2026-07-17.md`

## Risks and Assumptions

- Assumption: this is a markdown/article correction only.
- Assumption: `cycle.md` is the preferred publication style for embedding proof
  code in articles.
- Risk: replacing snippets with abbreviated prose could weaken the
  three-representation style. Prefer real source snippets when short enough;
  otherwise show a concise source-backed excerpt and link to the full proof.

## Validation

- Search articles for `.holds` snippets with commented theorem-only bodies.
- Run `git diff --check`.

## Progress Log

- Ticket created after finding commented-conclusion snippets in
  `articles/chapter4/integral-cycle.md`.
- Replaced the `assertTwoGapSumEqualsDiff` article stub with the real
  `CycleIntegralProperties.assertConsecutiveGapSumEqualsDiff` proof excerpt and
  corrected the indexed statement.
- Replaced commented-conclusion snippets in `integral-cycle.md` for modulo
  classification, modulo periodicity, rotation shift, cycle-period shifts,
  survivor exactness, first/last survivor bracketing, full-period filtered sum,
  and residue classification with source-backed proof excerpts or honest helper
  bodies.
- Clarified that `CycleCheckMod::afterMethodListAndZeroModCountAreOnSync` is a
  Boolean helper/predicate rather than a theorem-returning `.holds` wrapper.
  The audit target is fake commented conclusions, not absence of `.holds`.
- Updated `OBJECTS.md` so `GapProperties::assertTwoGapSumEqualsDiff` is
  described as a delegate to
  `CycleIntegralProperties.assertConsecutiveGapSumEqualsDiff`.
- Validation: `rg` no longer finds fake commented theorem bodies in
  `articles/chapter4/integral-cycle.md`; remaining comment hits are ordinary
  explanatory comments. `git diff --check` passed.
- Standardized the proof-code embedding rule after user clarification: small
  inline Scala blocks are allowed when they have a good signal/noise ratio;
  longer proof bodies should move to Appendix A or be replaced by source links.
- Updated `integral-cycle.md` to match the `cycle.md` pattern in Section 5:
  removed noisy inline Scala proof bodies from the main text, kept source
  references beside the math, and moved selected core proof bodies to Appendix
  A.8-A.12.
- Removed the `Prerequisite Structure` ASCII arrow diagram from
  `integral-cycle.md`; Section 2 now follows the `cycle.md` preliminaries style
  with prose and source links instead.
- Removed the standalone coding-strategy section `The .holds Caching Insight`
  from `articles/chapter5/euclid-theorem.md`, plus abstract, intro, and
  conclusion references to that tactic. The caching lesson remains appropriate
  for `LEARNINGS.md`, not the published article body.
- Replaced tutorial-style verification mechanics prose in `euclid-theorem.md`
  and `sieve-sequence.md` with proof-oriented wording that states what the
  source lemma establishes.
- Replaced inline mathematical expressions rendered as code in
  `euclid-theorem.md` with `$...$` math spans, including the sqrt-bound proof
  sentence `$d \cdot d \le d \cdot q = n$`.
- Refocusing `euclid-theorem.md` away from source walkthrough style: main
  article should present the math and source references, with Scala excerpts
  reserved for Appendix A or direct source links.
- Removed all Scala code blocks from the main body of `euclid-theorem.md`.
  The body now presents the mathematical argument and cites verified source
  functions; short Scala wrapper excerpts remain only in Appendix A.
- Filled the space left by removed code in `euclid-theorem.md` with
  mathematical proof exposition: the primorial factor argument, smallest-divisor
  case split, non-membership contradiction, and final theorem composition.
- Removed future/downstream implementation framing from `euclid-theorem.md`.
- Updated `PROOF_GUIDE.md` to match the newer article standards already added
  to `CONTRIBUTING.md` and `LEARNINGS.md`: theorem articles are math-first,
  helper lemmas are presented as named properties, properties lead methods,
  coding-strategy details stay out of articles, and inline mathematics uses
  `$...$` spans rather than code spans.
  Section 3.5 is now a self-contained corollary about complete finite prefixes,
  not a note about what sieve code later needs.
- Rebalanced `euclid-theorem.md` scope: §3 is now the theorem proof spine,
  while finite-prefix, composite-divisor, and product lemmas are grouped under
  a secondary "Supporting Verified Lemmas" section.
- Replaced the Stage 1 helper-lemma inventory bullets in `euclid-theorem.md`
  with three named mathematical properties, each with proof math and a source
  verification link.
- Rewrote `euclid-theorem.md` §4.1 so the complete-prefix corollary is the
  first-class subject; source methods now appear only as verification
  references.
- Rewrote the `euclid-theorem.md` conclusion and future-work sections from
  bullet/task lists into prose that synthesizes the theorem, verified support,
  scope, and plausible mathematical continuations.
- Added the prose-closing standard to `CONTRIBUTING.md`, `PROOF_GUIDE.md`, and
  `LEARNINGS.md` so future conclusions and future-work sections avoid simple
  bullet lists.
- Added the appendix-source-link standard to `CONTRIBUTING.md`,
  `PROOF_GUIDE.md`, and `LEARNINGS.md`: Scala excerpts kept in appendices must
  include nearby Markdown links to the repository files that own the maintained
  proofs. Updated the Euclid appendix source references accordingly.
- Audited other chapter articles for the same ending/appendix issues. Rewrote
  bullet-style future-work sections in `integral-cycle.md` and
  `sieve-sequence.md` into prose. Confirmed the main Scala appendices in
  `list.md`, `integral.md`, `cycle.md`, `integral-cycle.md`, and
  `euclid-theorem.md` already have nearby Markdown source links for their code
  excerpts.
- Expanded the `integral-cycle.md` conclusion so it recaps the core proved
  properties mathematically, matching the style of `integral.md` and
  `cycle.md`, while keeping open index-shift properties out of the proved
  summary. Updated `CONTRIBUTING.md`, `PROOF_GUIDE.md`, and `LEARNINGS.md` to
  say conclusions should include a compact mathematical recap when an article
  proves a family of properties.
- Strengthened the conclusion guideline in `CONTRIBUTING.md`, `PROOF_GUIDE.md`,
  and `LEARNINGS.md`: conclusions must always return to the core proved
  properties and proof structure in mathematical form, not only when the article
  proves a large family of properties.
- Fixed `list.md` section-summary bullets that used code ticks for
  mathematical statements. Sections 3, 5, 6, and 7 now use inline math spans for
  access, sum, product, and product-divisibility properties while keeping code
  identifiers in backticks where appropriate.
- Completed a broader `list.md` guideline pass: replaced mathematical
  singleton-list construction such as `[e]`, `[x]`, and `[L_t]` with cons form
  (`e :: suffix`, `x :: L_e`, `L_t :: L_e`) outside Scala source excerpts;
  corrected the sum definition's appendix pointer from A.1 to A.7; changed
  main-body proof snippets to "Source Verification Excerpt" blocks with nearby
  source links; and rewrote the conclusion recap into cleaner mathematical
  property blocks while preserving the article's recap role.
- Updated `CONTRIBUTING.md`, `PROOF_GUIDE.md`, and `LEARNINGS.md` with the
  missing standards from the final `list.md` pass: avoid singleton-list
  construction in article math when cons/insertion is clearer; source excerpts
  in the main body need nearby source links just like appendix excerpts; and
  appendix item references must be checked after code sections move.
