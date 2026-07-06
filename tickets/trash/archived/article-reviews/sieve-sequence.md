# Review: articles/sieve-sequence.md

## Source

- Article: `articles/sieve-sequence.md`
- Current role: Core sieve article

## Verdict

Close to publishable, but needs technical provenance cleanup.

## Must Fix

- Verify each cited function name against current source. During review, `assertHeadIsPrime` exists, but names like `distinctPrimesCoprime`, `filterPreservesPrimes`, and `filteredContainsAllPrimes` were not found under those exact names.
- Clarify that `5303` VCs are repository-wide for the current verification run, not necessarily only this article's functions.
- Update source references to the exact files and function names in `PrimeProperties.scala`, `FilterPreservesPrimesProperties.scala`, and `SieveSequenceProperties.scala`.
- Confirm that "complete sieve correctness proof" is framed as foundation, not a fully verified `next()` pipeline proof.

## Proof Reference Corrections

The review did not find evidence that the article's sieve lemmas are missing entirely; most issues appear to be stale or simplified names. Recommended replacements:

- Replace `CycleIntegralOnesProperties::assertCycleIntegralOfOnesStrictMonotonic` with `CycleIntegralOnesProperties::assertCycleIntegralOfOnesStrictlyIncreasing`.
- Replace `PrimeProperties::distinctPrimesCoprime` with `FilterPreservesPrimesProperties::assertPrimeNotDivisibleByDistinctPrime`.
- Replace `PrimeProperties::filterPreservesPrimes` with `FilterPreservesPrimesProperties::assertFilterPreservesAllPrimes`.
- Replace `PrimeProperties::filteredContainsAllPrimes` with `FilterPreservesPrimesProperties::assertFilteredContainsAllPrimes`.
- Keep `SieveSequenceProperties::assertHeadIsPrime`, but update the article snippet/signature to match the current source shape, where the sequence-level proof delegates to `PrimeProperties.assertHeadIsPrime(seq.head, seq.primes.tail)`.

Recommended fix: add a source-map table with article property, current source function, source file, and status. This will prevent the article from looking like it has missing proofs when the problem is actually name drift.

## Should Fix

- Add a small table mapping article sections to source functions.
- Strengthen the distinction between candidate generation, filter preservation, and head primality.
- Mention known open or externalized pieces, especially where `next()` still depends on `@extern` or unverified bottlenecks.

## Validation

- Search all cited names in `src/main/scala`.
- Compare against the Sieve and Prime sections of `OBJECTS.md`.
- Confirm latest `verify.log` reports `5303 valid`, `0 invalid`, `0 unknown`.
- Check that the article does not imply the entire `next()` pipeline is fully verified if remaining gap-cycle or `@extern` boundaries still exist.

## Additional Suggestions: ConsecutiveIntegers.scala

The file `src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala` contains 14 lemmas that are fundamental to sieve theory but are currently NOT in the sieve-sequence article. These lemmas prove:

- At most one value divisible by p in any p consecutive integers
- Exactly one zero per p-sized block  
- Density preservation after filtering (critical for sieve correctness)
- Count formulas for multiples

**Recommendation**: Consider integrating these lemmas as foundational sieve lemmas:

| Lemma | Property | Suggested Section |
|-------|----------|------------------|
| `atMostOneZero` | At most one multiple in p consecutive integers | Candidate Generation |
| `exactlyOneZeroInConsecutive` | Exactly one per p block | Candidate Generation |
| `densityPreservedAfterFiltering` | Density after filtering is preserved | Filter Preservation |
| `countModZeroEqualsM` | Count formula for multiples | Candidate Generation |
| `twoPrimesDensity` | Density with two primes | Filter Preservation |
| `densityForPrimeList` | Extended density for prime list | Filter Preservation |

These are the mathematical backbone lemmas for the sieve algorithm and should either be:
1. Integrated into sieve-sequence.md with proper source references, or
2. Documented as a dedicated "Foundational Sieve Lemmas" section in OBJECTS.md
