# Sieve Sequence V2 Article

**Status:** Complete - awaiting team review

## Goal

Create `articles/chapter6/sieve-sequence-v2.md` as a reviewable successor to the
current sieve-sequence article. Preserve the existing article unchanged while
improving mathematical organization, source provenance, verification-boundary
wording, citations, and coverage of the current Chapter 6 proof surface.

## Current State

- `articles/chapter6/sieve-sequence.md` is the current published draft.
- The archived evaluator considered it close to publishable but identified stale
  proof names, ambiguous repository-wide verification counts, incomplete source
  mapping, and insufficient separation between candidate generation, filtering,
  head primality, and the externalized executable `next()` boundary.
- Later editorial review found missing introductory structure and possible
  property-completeness gaps.
- The organized Chapter 60 proof tree was promoted into the final
  `src/main/scala/v1/chapter6/sieve/seq/spec` location while this article was
  being drafted. That promoted Chapter 6 tree is the sole source-provenance
  target for V2.

## Expected State

- A self-contained V2 article organized around mathematical properties rather
  than implementation pipeline narration.
- Every fully verified property has English explanation, mathematical proof, a
  current Scala `.holds` excerpt, and an exact source reference.
- Mathematical facts without a current Stainless theorem are explicitly marked
  as mathematically established but not Stainless-verified by this repository.
- The article clearly distinguishes full-period structure, transition filtering,
  next-head primality, executable implementation, and adjacent open research
  questions.
- Citations are primary or standard authoritative sources and support claims that
  actually need external provenance.

## Related Work

- `tickets/active/sieve-sequence-article-rewrite.md`
- `tickets/active/sieve-sequence-property-catalog.md`
- `tickets/active/sieve-sequence-v2-salvage-before-v1-removal.md`
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md`
- `tickets/active/chapter6b-curated-proof-spine.md`
- `tickets/trash/archived/article-reviews/sieve-sequence.md`
- `editorial-review-articles-2026-07-17.md`
- `scientific-merit-review-2026-07-17.md`

## Alternatives Considered

1. Update the current article in place. Rejected because the user requested an
   improved version suitable for team review and preserving the comparison is
   valuable.
2. Perform only editorial cleanup. Rejected because stale theorem provenance and
   proof-boundary ambiguity are substantive correctness issues.
3. Document every helper lemma. Rejected because the article should expose the
   mathematical proof spine, while implementation-only helpers remain source-level
   details.

## Risks

- Treating names in old tickets or reviews as current source truth.
- Conflating a mathematical theorem with what Stainless currently verifies.
- Presenting repository-wide verification totals as article-specific evidence.
- Allowing the gap-survival research program to make the sieve-sequence article
  overclaim what the foundational sequence construction proves.
- Adding citations as decoration rather than attaching them to precise claims.

## Assumptions And Hypotheses

- Assumption: the current Scala source and current green logs are authoritative.
  Validation: inspect theorem bodies and source paths directly.
- Assumption: Markdown-only edits do not require rerunning Stainless.
  Validation: follow `AGENTS.md` and run `git diff --check`.
- Hypothesis: the strongest article organization follows the promoted proof islands:
  representation and period, exact filtering/counting, next-head primality, then
  executable boundary. Validation: compare this structure with current property
  objects and the article rules.
- Hypothesis: classical wheel-sieve and modern sieve-method references can improve
  context without implying novelty. Validation: use primary publications or
  authoritative standard references and connect each citation to a specific claim.

## Work Plan

1. Read the current article and related tickets in full.
2. Catalog all article-worthy current `.holds` theorems and inspect their bodies.
3. Audit the old article's mathematical claims and references.
4. Research only the external citations needed for historical or limitation claims.
5. Draft `sieve-sequence-v2.md` with explicit theorem and verification boundaries.
6. Run a whole-document precision pass, source-link check, and `git diff --check`.
7. Record conclusions and remaining review questions here.

## Validation

- Every linked local source file and named function exists.
- Every quoted Scala theorem matches the current signature and postcondition.
- Every property follows the article three-representation rule.
- Abstract, introduction, body, and conclusion make the same strength of claim.
- No ticket paths, internal learning documents, VC totals, or unsupported novelty
  claims appear in the article.
- No prose-level chapter labels appear in the article. Local source links may
  include repository paths such as `src/main/scala/v1/chapter6/...`, but the
  article body must stand alone as a mathematical article and not assume the
  reader knows the repository chapter sequence.
- `git diff --check` succeeds.

## Learning Log

- 2026-07-20: Ticket created. Latest focused verification log is green at 128
  valid, 0 invalid, 0 unknown. Related article, proof-catalog, salvage, and review
  tickets were located; their claims still require comparison with current source.
- 2026-07-20: User clarified that Chapter 60 will replace Chapter 6 because its
  proof code is better organized. During validation, that tree was promoted to
  the final Chapter 6 source location. V2 now cites only those final paths;
  legacy wrappers and earlier chapter6b plans are historical comparison material.
- 2026-07-20: Source audit identified a stronger boundary than the old article
  stated. The linear spec-to-cycle theorem, repetition invariance, same-head
  count, semantic copy-or-merge transition, and next-spec assembly are verified.
  The direct bridge from the repeated cycle's filtered survivor gaps to the
  semantic merged-gap prefix remains open, as does internal derivation of the
  next canonical-period equation.
- 2026-07-20: Created `articles/chapter6/sieve-sequence-v2.md`. Added direct
  references to Pritchard's wheel-sieve survey, official Stainless verification
  documentation, System FR, and Ramanujan's proof of Bertrand's postulate, while
  retaining Hardy-Wright as the repository-standard CRT/Eratosthenes reference.
- 2026-07-20: Validation passed: every local article and Scala source link
  resolves, every cited theorem name exists in the promoted Chapter 6 source,
  code fences and inline math delimiters are balanced, the new files contain no
  non-ASCII or trailing-whitespace defects, and `git diff --check` is clean.
- 2026-07-20: Editorial isolation correction after user review: article prose
  must not refer to "Chapter 6" or internal chapter sequencing. Reworded the V2
  article around proof objects and theorem groups while retaining exact source
  paths as code provenance.
- 2026-07-20: Editorial endpoint correction after user review: the article must
  not narrate the painful development path, legacy implementation history, or
  "remaining work" as a meeting log. Rewrote the proof-boundary and future-work
  sections so they state the final theorem boundary and natural next problems.
- 2026-07-20: Moved verification provenance back to the verification article.
  `gap-dynamics-v2.md` no longer points at Scala source for math-only claims;
  `sieve-sequence-v2.md` now states the copied-gap, merged-gap, and
  square-bound successor-primality properties with math, verified code excerpts,
  and exact source references.

## Outcome

The original `articles/chapter6/sieve-sequence.md` remains unchanged. The new
V2 is ready for mathematical and editorial review. Reviewers should focus on
whether the selected headline theorems are the right public proof spine and
whether the three explicitly stated boundaries should remain in one section or
be split between proof prerequisites and future work.
