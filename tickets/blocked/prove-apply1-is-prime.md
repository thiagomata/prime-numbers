# Prove that `apply(1)` (first value after head) is prime in V0

**Created:** 2026-06-18
**Status:** Open
**Related tickets:**
- `sieve-properties-step4-assertHeadIsPrime.md` — proves head is prime for V2 (similar goal, different target)
- `prime-foundations-and-gap-proof.md` — foundation for prime properties used in `assertHeadIsPrime`
- `sieve-foundation-cycle-integral-ones-and-filter-preserves-primes.md` — filter preserves primes

---

## Goal

Prove that `SpecSieveSequence.apply(1)` — the first value generated after `head` — is always prime. Currently the postcondition of `apply(k)` only guarantees `accepts(res)` (coprime with filter primes), which is weaker than primality.

Concretely: add a lemma `assertApplyOneIsPrime` to V0 (or a properties file) that proves `Prime.isPrime(apply(1))`.

## Current State

- `SpecSieveSequence` is verified (580 lines, all `.holds` pass)
- `apply(1)`'s postcondition: `res >= head.value && res <= searchBound(1) && accepts(res)`
- `accepts(value)` = `passesFilter(value)` = `isCoprime(value, filterValues)` — no primality check
- `filterPrimes = primes.tail` (head is NOT a filter)
- Head is prime and coprime with all filter primes (constructor invariant)
- `searchBound(1) = head.value + filterModulus` (can be huge, much larger than `head²`)

Already verified:
- `SieveSequenceProperties.assertHeadIsPrime` — only proves current head is prime (V2)
- `PrimeProperties.assertHeadIsPrime(head, primesTail)` — existence proof via `assertAllNotCoprimeInRange`
- `FilterPreservesPrimesProperties.assertPrimeNotDivisibleByDistinctPrime` — distinct primes don't divide each other

## Expected State

A verified lemma `assertApplyOneIsPrime` with no `.holds` timeout.

## Mathematical Background

**Theorem:** If `n > p` is a natural number, `p` is prime, and no prime less than `p` divides `n`, then either:
1. `n` is prime, or
2. `n >= p²`

**Proof:** If `n` is composite, it has a prime factor `q`. Since no prime `< p` divides `n`, we have `q >= p`. So `n >= q * q >= p * p = p²`. (contrapositive: if `n < p²` and `n` has no prime factors `< p`, then `n` must be prime).

**Corollary:** If `apply(1) < head²`, then `apply(1)` is prime (since it passes all filters, meaning no prime `< head` divides it).

## The Core Challenge

`apply(1)` searches from `head + 1` up to `searchBound(1)`. Finding the first accepted value requires proving it stops BEFORE `head²`. This means: **there is always a number in `(head, head²)` that is coprime with all primes less than head.**

This is equivalent to: **there is always a prime between `head` and `head²`**.

For `head >= 2`:
- **True** by Bertrand's postulate (Chebyshev's theorem): for all `n > 1`, there exists a prime in `(n, 2n)`. Since `head² >= 2*head` for `head >= 2`, there is a prime in `(head, 2*head] ⊆ (head, head²]`.
- **But**: Bertrand's postulate is a deep theorem not provable in SMT.

## Alternatives Considered

### A1. Accept Bertrand's postulate as an axiom
- **Pro:** Simple; add `@extern` lemma or `require` that is never discharged
- **Con:** Violates the project's verification philosophy; makes one-up-the-ladder argument non-constructive

### A2. Structural proof using the sieve's own construction (V2 approach)
- **Pro:** The V2 pipeline generates `apply(1)` as the first gap-step from head; the gap cycle is built from residues, and the next-level construction ensures the new head is coprime with all previous primes plus the current head. This might enable a direct proof that the next head emerges as a prime from the filter/expand/sort pipeline.
- **Con:** Only works for V2, not V0. Requires understanding the full residue generation pipeline.

### A3. Direct bound: prove `apply(1) < head²` without Bertrand
- **Hypothesis:** Maybe the sieve's own structure guarantees the first survivor is small. For example, `head + 1` might pass the filter unless it has a small divisor. The worst case is `head + 1` is even, `head + 2` divisible by 3, etc. This resembles the prime gap problem.
- **Risk:** Prime gaps are unbounded in general (Westzynthius proved arbitrarily large gaps). However, for a fixed head, the gap to the next accepted number is bounded by `filterModulus`, and the bound `head + filterModulus` could be used. But we need `apply(1) < head²`, not just `apply(1) <= head + filterModulus`.
- **Counterexample in general:** For `head = 7`, `filterModulus = 2*3*5 = 30`, `searchBound(1) = 37`, which is < 49. For `head = 5`, `filterModulus = 2*3 = 6`, `searchBound(1) = 11 < 25`. But is this always true?

### A4. Case analysis on `head`
- For an arbitrary prime head, is there always a number `< head²` that is coprime with all smaller primes? This is equivalent to the primorial `P(head-1)` being > `head² /`... No, that's not right.
- **Concrete check:** For `head = 3`, `filterModulus = 2`, `searchBound = 5 < 9`. Yes.
- For `head = 5`, `filterModulus = 6`, `searchBound = 11 < 25`. Yes.
- For `head = 7`, `filterModulus = 30`, `searchBound = 37 < 49`. Yes.
- For `head = 11`, `filterModulus = 2*3*5*7 = 210`, `searchBound = 221 > 121`!!!
- So `searchBound(1)` can exceed `head²`. The search might step past `head²` and find a composite like `head² = 121` before the next prime.

### A5. Prove `apply(1)` is prime using the known prime list directly
- We know all primes < head. If `apply(1) < head²`, it's prime. So we need a lemma that `apply(1) < head²` always holds.
- **Observation:** The first accepted value in `(head, head²)` is specifically looking for the smallest number > head coprime with all smaller primes. This is the **prime gap** problem.
- **Key insight:** We may not need to prove this unconditionally. Instead, we could prove that `SpecSieveSequence` **iterates through all natural numbers** and that the accepted values are exactly the primes. This is the full correctness statement of the sieve.

### A6. Prove the full correctness of V0: every generated value is prime
- If we can prove `apply(k)` is prime for ALL `k`, then `apply(1)` is trivially prime
- This is equivalent to proving that the sieve generates exactly the primes (no composites)
- This is a known theorem: the Sieve of Eratosthenes, when implemented as a simple generator starting at `p_n` and filtering by all smaller primes, generates exactly the primes starting from `p_n`, with no gaps
- **Risk:** This is the full soundness proof and could be very complex

## Recommendation

Start with A5/A6: prove that `SpecSieveSequence.apply(k)` is prime for all `k`. The key lemma needed:

1. If `n` has no prime factor `< head.value`, then either `n` is prime or `n >= head.value²`
2. `apply(k) < head.value²` for `k >= 1` (or more generally, `apply(k) < head.value * head.value` for `k = 1`)

For (2), we need the bound. The first accepted value after head is exactly `apply(1)`. Since the search scans linearly from `head + 1`, and `head` itself is coprime with all filter primes, the gap between `head` and `apply(1)` is bounded by the longest run of consecutive integers each divisible by some filter prime. The maximum possible gap could be as large as the Jacobsthal function `j(primorial(filterPrimes))`.

For the V0 construction, we don't have a Jacobsthal bound either. This makes a fully constructive SMT proof extremely difficult.

## Validation Plan

1. **Phase 1: Prove the lemma**. Write a mathematical proof that `apply(1)` is prime for V0, possibly requiring new number-theoretic lemmas
2. **Phase 2: Implement in Stainless**. Add `assertApplyOneIsPrime` to `SpecSieveSequence` or a new `SpecSieveSequenceProperties` object
3. **Phase 3: Verify**. Run `just verify`; must complete without timeout

## Assumptions

- The V0 constructor's `isCoprime(head, filterValues)` ensures head itself passes the filter
- All filter primes are strictly less than head (by construction)
- `head` > 1 (it's a Prime, so `value > 1`)

## Risks

- Bertrand's postulate or Jacobsthal function may need to be assumed as axioms
- Stainless SMT solver may time out on the required induction
- The proof may require deep number theory (prime gaps) beyond what SMT can handle

## Attempted Code (archived from `SpecSieveSequence.scala`)

The following code was attempted in `SpecSieveSequence` but never verified due to the
`apply(1) < head.value * head.value` precondition not being universally dischargeable.
It is preserved here as a starting point:

```scala
//  /**
//   * Proves that `apply(1)` is prime when it lies below `head * head`.
//   *
//   * If `apply(1)` were composite its smallest prime divisor `d` would satisfy
//   * `d*d <= apply(1) < head*head`, so `d < head`. By the prime list completeness
//   * `d` is in `filterValues`, and `Calc.mod(apply(1), d) == 0` contradicts
//   * `accepts(apply(1))`. Therefore `apply(1)` must be prime.
//   */
//  def assertApplyOneIsPrimeIfBelowHeadSq(): Boolean = {
//    require(apply(BigInt(1)) < head.value * head.value)
//
//    // TODO: apply(1) < head² needs to be proved or discharged by a stronger lemma.
//    // apply(1) transits through searchBound(1) = head + filterModulus.
//    // Currently no lemma proves this is always < head².
//
//    val n = apply(BigInt(1))
//
//    // n is accepted — coprime with all filter primes
//    assert(accepts(n))
//
//    // By the filter completeness property, every prime < head is in filterValues
//    // (requires explicit enumeration lemma proving the prime list is complete).
//    // If n is composite, its smallest prime factor d divides n and d < n < head²,
//    // so d < head. Therefore d is in filterValues, and since accepts(n) gives
//    // mod(n, d) != 0, this is a contradiction.
//
//    PrimeUtils.isPrime(n)
//  }.holds
```

The two assistants `assertFilterValuesContains` and `assertFilterValuesContainsInTail`
still exist in `SpecSieveSequence.scala` as private lemmas supporting the completeness
enumeration. They may be reusable when the precondition is discharged.
