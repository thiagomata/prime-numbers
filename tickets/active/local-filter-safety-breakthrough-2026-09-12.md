# Local Filter Safety: Arithmetic Breakthrough Audit

**Created:** 2026-09-12
**Status:** In progress; mathematical research, no new safety theorem claimed.

## START HERE

Audit the exact local-filter safety obligation against current arithmetic definitions. Seek an argument that adds information rather than another sufficient condition containing the original unknown. First check the classification of accepted composites below the next head square and its consequences for the local-surplus candidate.

## Goal

Find and critically test a genuinely stronger arithmetic route to recurring square-safe 2-gap survival. A diagnosis or exact identity is useful progress but is not completion of the user's requested breakthrough. State plainly any remaining unproved estimate.

## Strategy

Read the strongest existing property records and source contracts, independently check load-bearing obstruction claims, then derive and review a bounded candidate. Separate one fixed transition, infinitely many transitions, and a universal eventual assertion. Search before adding any lemma. No Scala or article edits are planned during this audit.

## Current State

Initial research read TICKET_DISCIPLINE.md, LEARNINGS.md sections 1–5, the local-surplus candidate, exact accepted-strike and annular decomposition proofs, weighted deletion conservation, and the maintained real 2-gap copy-count source. Complete-period survival is already established; the local lower bound remains open. Critic and Monitor approved creation of this record. A proposed diagnostic classifies the pre-final-filter population as genuine twin pairs plus prime/semiprime pairs; its proof and novelty are under review.

Pre-existing work is present in articles/chapter6/sieve-sequence.md, articles/arxiv/sieve-sequence/references.bib, and articles/arxiv/gap-dynamics/. Preserve it.

## Expected State

An exact, critically reviewed mathematical finding with its scope, dependencies, and open boundary recorded. If a new useful result survives review, promote it to a property note without claiming Stainless verification. Do not label an identity a proof of local safety.

## Related Tickets

- [Backward head 2-gap bound](backward-head-two-gap-bound-2026-08-29.md): coherent phase and bad-separator constraints give real bounds but no head-relative abundance; its latest local-surplus analysis is the immediate starting point.
- [Algebraic conditioned survival](algebraic-conditioned-survival-2026-07-27.md): exact recurrences and energy identities can merely relocate the survivor count. Audit candidate premises for this problem.
- [Property catalog](sieve-sequence-property-catalog.md): register any new permanent mathematical record only after review.

## What is Learned

- Accepted filter-p strike values below q² are exactly p*r with r prime in [p, floor((q²-1)/p)]. Their number A is capacity, not actual pair destruction.
- The verified SpecSieveSeqTwoGapProperties.assertExactlyHeadMinusTwoCopiesSurvive concerns all p lifts; its body does not locate one in a square window.
- No new local-survival theorem has been established in this audit.

## Alternatives Considered

1. Recommended: classify the actual arithmetic population at the last filter, then inspect whether capacity slack yields a useful bound or demonstrates why prefilter abundance already contains prime-pair content.
2. Another energy/capacity inequality: defer unless it uses information absent from the existing sharp-envelope and weighted-conservation results.
3. More finite measurements: defer; the existing 186-transition record already supports the conjecture, and more examples cannot establish unbounded recurrence.

## Assumptions and Validation

- Consecutive primes p<q with p>=5; all primes below p are installed. Validate directly against SpecSieveSequence and property definitions.
- Use the strict endpoint window q<=x and x+2<q². Check boundaries explicitly, including p² and q²-2.
- Historical impossibility assessments are hypotheses to recheck, not authority. Read exact statements and proofs.
- Mathematical results require a complete argument and independent Critic review. Markdown records require structural/link checks, no runtime gates.
- If Scala work becomes concrete, establish Scala tests and applicable chapter regression baselines before source edits, then follow one-lemma-per-cycle discipline. This audit does not claim fresh verification of existing code.

## Failed Paths

- Historical full-period density transfer: it does not bound the distinguished short-window discrepancy. Reconsider only with a proved localization estimate or additional arithmetic invariant.
- Historical unsigned capacity/energy repairs: exact extremizers or terminal identities defeat the documented versions. Reconsider only if a new input excludes those extremizers for the actual arithmetic population.
- Read-only search typo: a shell glob src/main/scala/Chapter60* matched no files. Corrected using rg --files; no validation gate ran or failed.

## Open Concerns

- The new decomposition may be only an elementary sharpening of existing parity discussion; do not overclaim novelty or progress.
- A conditional survival theorem can be stronger than twin-prime infinitude; do not assert equivalence without both directions.
- Obtaining a recurring unconditional lower bound remains a major unresolved mathematical task.

## Next Action

Complete the accepted-composite classification, search for duplicate results, and have Critic test its logical consequences before proposing any permanent note.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-09-12 | Existing local-surplus and annular results isolate capacity but leave the actual prefilter population unbounded below. Initial ticket proposal omitted What is Learned; Critic caught it and the corrected proposal passed. | Created this persistent research record after Monitor PASS; investigate the arithmetic content of prefilter abundance. |
