# TODO

## Article Drafts and Pending Verification

- [x] `src/main/scala/v1/chapter4/cycle/integral/classic/ClassicCycleIntegral.scala`: retired duplicate classic cycle-integral logic by delegating to canonical `CycleIntegral`; `ClassicCycleIntegralProperties` now points to `CycleIntegral`.
- [x] `articles/chapter4/integral-cycle.md`: retired the §5.1 modulo invariance draft marker by citing the verified `MemCycle` finite-period classification layer and `GapProperties.assertModIsPeriodic`.
- [ ] `articles/chapter4/integral-cycle.md`: package the §5.3 right index shift as an all-position wrapper; the stored-period `CycleIntegral` core is verified by `GapProperties.assertRotateOneCycleIntegralShiftsByOne`.
- [ ] `articles/chapter4/integral-cycle.md`: verify or retire the §5.4 left index shift draft.
- [ ] `articles/chapter6/gap-dynamics.md`: replace the draft verification target for gap-copy / gap-merge behavior with a verified `.holds` lemma or keep it explicitly marked as pending.
- [ ] `articles/chapter6/sieve-sequence-v2.md`: connect the verified same-head filter count through the next sieve spec and constructed-cycle wrappers instead of supplying the next-period boundary to the cycle-level proof.
- [ ] `articles/chapter6/sieve-sequence-v2.md`: formalize Bertrand's postulate or keep the next-head primality proof explicitly conditional on the square-bound precondition.
- [ ] `articles/chapter6/sieve-sequence.md`: review the older open claims blocked on Bertrand's postulate and Euclid's lemma; either migrate current verified results from `sieve-sequence-v2.md` or mark the article as superseded.
- [ ] `articles/draft/draft-sieve-gap-survival-math.md`: keep as mathematical exploration until the main survival claims have source-linked Stainless verification.
- [ ] `articles/draft/draft-empirical-g-local-analysis.md`: keep empirical functions labeled as `@extern` / not Stainless-verified, or add verified replacements before promoting the article.

## Active Proof Drafts

- [ ] `tickets/active/m-interval-density-and-sieve-sequence-v2.md`: resolve which proof draft, modular permutation, structural recursion, or value-domain counting, remains relevant after the current same-head filter count work.
- [ ] `tickets/active/spec-same-head-filter-density.md`: remove or update stale draft code blocks that are now superseded by verified same-head filter-count lemmas.
- [ ] `tickets/active/next-gaps-size-closed-form.md`: reconcile the old "closed form pending" notes with the current verified same-head count and remaining supplied-boundary limitation.
- [ ] `tickets/active/sieve-sequence-proof.md`: revisit the survival-walk / list-builder equality blocker after the current next-stage boundary wording is stable.
- [ ] `tickets/active/sieve-sequence-v2-gap-filter-properties.md`: draft the requested subsection only after the relevant gap-filter properties have verified source references.

## Catalog Cleanup

- [ ] `OBJECTS.md`: audit deferred chapter-6 survivor-window lemmas and decide whether they are still deferred, superseded, or replaced by current spec/cycle wrappers.
- [ ] `articles/learnings/learnings-capacity-argument.md`: keep open capacity and gap-dynamics claims out of publication articles unless they gain complete mathematical and Stainless verification.
