# Local Filter Safety: Arithmetic Breakthrough Audit

**Created:** 2026-09-12
**Status:** Initial arithmetic audit complete; local-safety breakthrough remains open.

## START HERE

Audit the exact local-filter safety obligation against current arithmetic definitions. Seek an argument that adds information rather than another sufficient condition containing the original unknown. First check the classification of accepted composites below the next head square and its consequences for the local-surplus candidate.

## Goal

Find and critically test a genuinely stronger arithmetic route to recurring square-safe 2-gap survival. A diagnosis or exact identity is useful progress but is not completion of the user's requested breakthrough. State plainly any remaining unproved estimate.

## Strategy

Read the strongest existing property records and source contracts, independently check load-bearing obstruction claims, then derive and review a bounded candidate. Separate one fixed transition, infinitely many transitions, and a universal eventual assertion. Search before adding any lemma. No Scala or article edits are planned during this audit.

## Current State

Initial research read TICKET_DISCIPLINE.md, LEARNINGS.md sections 1–5, the local-surplus candidate, exact accepted-strike and annular decomposition proofs, weighted deletion conservation, and the maintained real 2-gap copy-count source. Complete-period survival is already established; the local lower bound remains open. Critic and Monitor independently confirmed the exact classification L=T+D, where T counts twin primes and D destroyed prime/semiprime pairs. The permanent note has been reviewed and registered. It supplies an arithmetic diagnostic and a benchmark calibration conditional on Hardy–Littlewood, not a local-survival proof. No independently justified next unconditional proof step emerged from this audit.

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
- Every accepted composite below q² has least prime factor p and is p*r with r prime. Both endpoints of a prefilter 2-gap cannot be composite, since p cannot divide their difference 2. Consequently L=T+D, 0<=D<=A<=3p, and L-A=T-U for unused capacity U=A-D.
- Define chi3(v)=1 for v congruent to 1 modulo 3 and -1 for v congruent to 2. The exact destruction count is the sum of prime indicators at p*r-2*chi3(p*r), over prime r in [p,K]. The other neighbor is divisible by 3. A possible neighbor at the excluded upper boundary q² has zero prime indicator.
- Conditional on the Hardy–Littlewood twin asymptotic, L/L_hat tends to exp(2*gamma)/4, about 0.793. Thus exact relative matching to the complete-period benchmark is not an appropriate conjectural target. This conditional diagnosis does not contradict the existing candidate, which only requires a positive surplus.
- A fixed positive-fraction lower bound L>=c*L_hat at infinitely many stages would still suffice, but by L=T+O(p) it already yields a substantive twin-prime lower bound.
- Quantifiers matter: positive post-filter count at infinitely many heads is equivalent to twin infinitude; positivity at every sufficiently large head is stronger. No converse from twin infinitude to the capacity-surplus condition has been established.
- Durable result: [Pre-Final Twin Decomposition](../../properties/sieve-sequence/pre-final-filter-twin-semiprime-decomposition.md), registered in the property catalog. Its finite theorem and conditional asymptotic are explicitly distinguished.

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

Surface the unresolved proof boundary. A next attempt needs a specified new arithmetic estimate with an independent reason to hold; audit its premise against L=T+D before adding another lemma. No such estimate has yet been justified. The original breakthrough objective remains open, and the existing decomposition should not be presented as its solution.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-09-12 | Existing local-surplus and annular results isolate capacity but leave the actual prefilter population unbounded below. Initial ticket proposal omitted What is Learned; Critic caught it and the corrected proposal passed. | Created this persistent research record after Monitor PASS; investigate the arithmetic content of prefilter abundance. |
| 2026-09-12 | Critic and Monitor independently confirmed the twin/semiprime decomposition. Literature cross-check of Tao's sieve notes and twin-prime heuristic confirms the two different constants; their ratio is conditional on Hardy–Littlewood. No duplicate explicit decomposition found in the searched catalog. | Record result and review one permanent note. No Scala/Python gates needed for mathematical Markdown; no safety claim made. |
| 2026-09-12 | Permanent note passed independent proof and endpoint review; all relative links exist and 13 math fences pair correctly. Registered its short name and full title. No source changes or runtime verification were needed. | Initial audit complete; retain the breakthrough goal as open and report the absence of a justified unconditional next step. |
