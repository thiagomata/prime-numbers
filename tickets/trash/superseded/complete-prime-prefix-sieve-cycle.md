# Complete Prime Prefix Sieve Cycle

## Goal

Explore a restricted sieve representation based on a complete prefix of primes:

- Valid prime lists contain at least two elements.
- Valid prime lists contain every prime up to the largest prime in the list.
- The generated sieve cycle starts at the largest prime.
- The cycle accepts exactly values that are not multiples of any previous prime in the prefix.

Examples:

- `[2, 3]` is valid.
- `[2, 3, 5, 7, 11]` is valid.
- `[2, 7]` is invalid because it skips `3` and `5`.
- `[2]` is invalid because it has only one element.

## Current State

`CycleSieveSequence` already models a current head prime with previous primes in the tail, but `next()` remains `@extern`. The hard proof obligation is connecting the constructed next cycle/gaps to the requirements expected by the next sequence.

`SpecSieveSequence` has an attractive search-style shape, but proving that an upward search terminates requires a finite witness or bound. That proof has been difficult.

## Expected State

Introduce a separate restricted object or class that describes a complete prime prefix and its sieve semantics without changing `SpecSieveSequence`, `CycleSieveSequence`, `MemCycle`, `ModCycle`, or `CycleIntegral`.

The first useful target is a small verified semantic layer:

- identify the largest prime in a nontrivial prime list;
- identify the previous primes used for the wheel;
- define acceptance as coprimality against previous primes;
- prove at least one key property about accepted values or starting value.

## Assumptions And Hypotheses

- A more restricted representation may make meaningful proofs easier because "all previous primes are known" becomes a representation invariant.
- A `List[Prime]` representation may expose existing lemmas from `PrimeUtils` and `PrimeProperties`.
- Exact completeness, "contains every prime up to max", may require new bounded predicates or next-prime machinery if none exists already.
- It may be better to keep this as a separate object until the proof shape is clear.

## Risks

- Defining complete prime prefixes as an arbitrary predicate may be too weak to help Stainless.
- Defining completeness constructively may require proving facts about every integer between two primes.
- Building a real `CycleIntegral` too early could pull the work back into the existing bottleneck.
- A recursive search upward may still need a difficult termination/witness proof.

## Validation Plan

- Run `sbt 'set stainlessEnabled := false' 'testOnly v1.seq.sieve.*'` before verification after code changes.
- Run `just verify` after every change.
- Keep each proof/code change to one requirement, assertion, or lemma.
- Treat timeout as failure.
- Compare related tickets and OBJECTS.md before selecting the first implementation step.

## Related Tickets

- `sieve-sequence-residue-representation-proof-object.md` already added
  `SieveSequenceByPrimes` as a separate semantic object over prime lists.
- `next-constructor-requirement-assertions.md` tracks the current diagnostic
  assertions around `CycleSieveSequence.next()`.
- `remove-extern-from-next.md` identifies the non-empty gap proof as the main
  blocker for removing `@extern`.
- `gap-positivity-proof.md` and `gap-positivity-proof-detailed.md` connect gap
  non-emptiness to Euclid/periodicity-style reasoning.
- `next-level-requirements.md` describes the residue representation invariant
  as the intended way to make constructor requirements available.
- `euclid-full-formalization.md` and `prime-foundations-and-gap-proof.md` cover
  the prime-generation and head-is-prime proof background.
- `sieve-properties-step5-coprime-to-modulus.md` records prior residue and
  coprimality-preservation experiments.
- `OBJECTS.md` lists the useful existing APIs:
  `PrimeUtils.biggerPrime`, `PrimeUtils.primeValues`,
  `PrimeProperties.primorialPlusOneModAny`, `PrimeProperties.newPrimeFromEuclid`,
  and `SieveUtils.isCoprime`.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-15 | Baseline verification passed at 5341 valid. | Safe to create the ticket and inspect related code. |
| 2026-06-15 | `SieveSequenceByPrimes` already exists as an untracked verified object, but it treats `primes.head` as the sequence head. The proposed prefix examples are ascending and want the largest prime as the head. | Add a separate typed prefix view rather than changing V0/V2 or the existing semantic baseline. |
| 2026-06-15 | Added `CompletePrimePrefix`, a restricted wrapper over `List[Prime]` requiring at least two primes and a bounded predicate that every prime from `2` through the largest prime appears in the value list. It exposes `head` as `PrimeUtils.biggerPrime(primes)`, `wheelPrimes` as the prime values strictly below that head, and `accepts` as coprimality against those previous primes. Sieve unit tests passed and `just verify` passed at 5360 valid. | Next proof step can target one tiny property, such as `head.value` being the start value or `wheelPrimes` containing only positive previous primes, before trying to construct gaps. |
