# Prime Number Foundations & Gap Proof

**Created:** 2026-06-09
**Status:** Planning
**Depends on:** `walk-based-pipeline.md` (Complete), `gap-positivity-proof.md` (Stalled)

---

## Goal

Remove `@extern` from `SieveSequenceV2.next()` by proving classic prime number properties
from first principles, then using them to verify gap positivity and non-emptiness.

---

## Current State

- **Verification:** 4415 valid, 0 invalid, 0 unknown ✅
- **Tests:** 26/26 pass ✅
- **`next()` status:** `@extern`
- **`assertCollectGapsV2AllPositive`:** Commented out (was failing with UNKNOWN/CANCELLED)
- **Phase 1 (`%`→`Calc.mod`):** Complete ✅
- **Phase 2 (postconditions):** Complete ✅
- **Phase 3a (`assertNoDivisorByFactorList`):** Complete ✅ (4415 valid)
- **Phase 3b (`assertHeadIsPrime`):** In progress — helper functions added but not yet verified
- **New ticket:** `assert-no-divisor-by-factor-list.md` details the solver block and resolution

---

## Why Previous Approach Failed

The `assertCollectGapsV2AllPositive` lemma tried to prove **operational** properties
(gap > 0) without **semantic** foundations (what is a prime, why is the sieve correct).

**Specific failure:** Stainless can't connect `lastSurvivor: BigInt` back to
`seq.apply(lastPos + 1)` across recursive calls. The indirection through raw
`BigInt` values loses the type-level connection to the integral.

**Root cause:** We're proving gaps are positive without proving *why* they should be —
because the sequence produces primes, and primes in order are strictly increasing.

---

## Hypotheses

1. **H1:** Defining `isPrime` and proving basic properties is LOW difficulty.
2. **H2:** Euclid's Lemma (prime divides product → divides factor) is HIGH difficulty
   in Stainless but may be provable with existing DivMod infrastructure.
3. **H3:** Rewriting `assertCollectGapsV2AllPositive` to track positions instead of
   values may work with existing `assertCycleIntegralIncreasing` lemma.
4. **H4:** `head ∤ modulus` follows from Euclid's Lemma + `head ∈ primes` + `head ∉ primes.tail`.
5. **H5:** Non-emptiness follows from `head ∤ modulus` + residue cycling.

---

## Assumptions

1. The existing DivMod infrastructure (ModIdentity, ModIdempotence, AdditionAndMultiplication)
   provides sufficient primitives for proving divisibility properties.
2. Stainless's Z3 solver can handle inductive proofs over natural numbers when
   set up with the right lemmas.
3. The `SieveSequenceV2` invariants (`checkAllBiggerThanValue(primes, 1)`,
   `assertProductEqualOrBiggerThanElements(primes.tail)`) are sufficient
   to derive prime properties.
4. The `assertCycleIntegralIncreasing` lemma (already verified) is correct
   and can be used to prove gap positivity.

---

## Plan

### Phase 1: Prime Definition (`v1/prime/Prime.scala`)

**New file** with:
- `isPrime(p: BigInt): Boolean` — p > 1 AND no divisor in [2, p)
- `noDivisorInRange(n, from, to)` — helper predicate

**Properties to prove:**
- `isPrime(2)` — base case
- `isPrime(p) => p > 1`
- `isPrime(p) => p % d != 0` for `2 <= d < p`
- `isPrime(p) && d | p => d == 1 || d == p`

**Difficulty:** LOW

### Phase 2: Euclid's Lemma (`v1/prime/EuclidLemma.scala`)

**Statement:** If `isPrime(p)` and `p | a*b`, then `p | a` or `p | b`.

**Approach:**
- Start with `assume(...)` or `@extern` to unblock pipeline
- Prove in follow-up session
- Use existing DivMod infrastructure

**Key corollary:** `head ∤ modulus`

**Difficulty:** HIGH

### Phase 3: Sieve Correctness

**3a. Head is Prime:**
- Add `isPrime(head)` as invariant or derive from construction

**3b. Filtering Correctness:**
- If `gcd(x, M) = 1` and `x % p ≠ 0`, then `gcd(x, M·p) = 1`

**3c. Next Head is Prime:**
- First survivor after filtering is prime
- Needs: at least one survivor exists

**Difficulty:** MEDIUM

### Phase 4: Gap Positivity + Non-emptiness

**4a. Non-emptiness (`gaps.nonEmpty`):**
- From `head ∤ modulus` (Euclid's Lemma)
- Residues modulo `head` cycle through all non-zero values
- `(head-1) · gapCycle.size > 0` survivors

**4b. Gap Positivity (`allGreaterThan(gaps, 0)`):**
- Rewrite `assertCollectGapsV2AllPositive` to track **positions** not values
- Use `assertCycleIntegralIncreasing(ci, lastPos, pos)` directly
- Prove `allGreaterThan` preservation inductively

**Difficulty:** MEDIUM

### Phase 5: Remove `@extern`

- Wire Phase 4 results into `nextGapCycleV2`
- Remove `@extern` from `next()`
- Run full verification

**Difficulty:** LOW (mechanical)

---

## Risks

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Euclid's Lemma unprovable in Stainless | HIGH | MEDIUM | Use axiom initially, prove later |
| Position-tracking rewrite still fails | MEDIUM | LOW | Fall back to stronger invariants |
| Sieve correctness needs more lemmas | MEDIUM | MEDIUM | Add intermediate lemmas as needed |
| Verification timeout on new lemmas | LOW | LOW | Split into smaller lemmas |

---

## Related Tickets

- `walk-based-pipeline.md` — Complete, walk-based gap computation
- `gap-positivity-proof.md` — Stalled, the current blocker
- `gap-positivity-proof-detailed.md` — Detailed analysis of the failure
- `next-level-requirements.md` — Requirements for next sieve level

---

## Validation

### Progress Validation

After each phase:
1. Run `just verify` — must remain 0 invalid
2. Run `sbt 'set stainlessEnabled := false' 'testOnly v1.seq.sieve.*'` — tests must pass
3. Update this ticket with results

### Final State Validation

1. `just verify` shows 0 invalid, 0 unknown
2. All 26+ tests pass
3. `@extern` removed from `next()`
4. `assertCollectGapsV2AllPositive` re-enabled and verified
5. New prime properties documented in OBJECTS.md

---

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-09 | `assertCollectGapsV2AllPositive` fails because `lastSurvivor` loses connection to integral | Plan position-tracking rewrite |
| 2026-06-09 | SMT solver can't connect `findPrimeFactorInList` return value to list membership | Use direct structural recursion over list elements |
| 2026-06-09 | `assertDivTransitive` internal complexity causes timeout in certain contexts | Inline transitivity with explicit `assert(nd*dp >= 0)` before `assertMultipleModZero` |
| 2026-06-09 | `assertNoDivisorByFactorList` (core lemma) now verified at 4415 total | Proceed to `assertHeadIsPrime` |
| 2026-06-09 | Need formal prime definition and Euclid's Lemma for non-emptiness | Plan foundation-first approach |
| 2026-06-09 | **New approach**: Avoid Euclid's Lemma entirely. Use strong induction: `primes.tail` contains ALL primes < `head`. Then `head` composite ⇒ prime factor q < head ⇒ q ∈ primes.tail ⇒ q\|head ⇒ contradicts isCoprime. Only needs: fix `%`, add postconditions, prove `primes.tail` completeness via pipeline structure. | Update Phase 1-3 plan |

## Updated Plan (2026-06-09)

The direct proof avoids Euclid's Lemma by using the strong induction hypothesis:

**Lemma**: `SieveSequenceV2.head` is prime.

*Proof*:
1. `primes.tail` contains every prime < `head` (induction hypothesis)
2. `head` is coprime to all `primes.tail` (by construction: must be proven as `isCoprime(head, primes.tail)`)
3. Suppose `head` is composite. Then `head = a*b` with `2 ≤ a, b < head`.
4. Let `q` be any prime divisor of `a`. Then `q ≤ a < head`, so `q ∈ primes.tail`.
5. `q | a | head`, so `q | head`. But `q ∈ primes.tail` contradicts step 2.
6. Therefore `head` has no divisor in `[2, head)` → `Prime.isPrime(head)`.

### Phase 1: Fix `%` → `Calc.mod`
- [x] SieveUtils.isCoprime
- [x] SieveUtils.filterList
- [x] SieveSequenceNextLevel.nextHeadResidueIndexV2
- [x] SieveSequenceNextLevel.collectGapsV2

### Phase 2: Add divisibility lemmas
- [x] `assertIsCoprimeSound` — `isCoprime(v, P)` ⇒ `Calc.mod(v, p) != 0` for all p in P
- [x] `assertIsCoprimeForAll` — stronger version
- [x] `assertModZero` — `Calc.mod(0, n) == 0`
- [x] `assertModZeroImpliesDivTimesBEqualsA` — `Calc.mod(a,b)==0 ⇒ Calc.div(a,b)*b == a`
- [x] `assertMultipleModZero` — `Calc.mod(k*n, n) == 0`
- [x] `assertDivTransitive` — if `b|c` and `a|b` then `a|c`
- [x] `findPrimeFactorInList` — finds p in primes where `Calc.mod(n, p) == 0`
- [x] `assertPrimeFactorDivides` — proves the found p divides n

### Phase 3: Prove head is prime
- [x] Lemma: `assertNoDivisorByFactorList(n, d, primes)` — core lemma: given `isCoprime(n,primes)` and `!isCoprime(d,primes)`, prove `Calc.mod(n,d) != 0`
- [ ] Lemma: `assertAllNotCoprimeInRange(limit, d, primes)` — completeness check (plain function, no .holds)
- [ ] Lemma: `assertNoDivisorInRangeHelper(n, primes, d, limit)` — iterates d from 2 to head, uses completeness + assertNoDivisorByFactorList
- [ ] Main lemma: `assertHeadIsPrime(head, primesTail)` — `Prime.isPrime(head)`

**Key learning:** SMT solver can't connect `findPrimeFactorInList` return value to list membership.
Solution: direct structural recursion over list elements instead of opaque selector functions.
See `assert-no-divisor-by-factor-list.md` for the full debugging history.

---

## Open Questions

1. Can Stainless prove Euclid's Lemma with existing infrastructure?
2. Is `isPrime` as defined sufficient, or do we need a stronger definition?
3. Should we add `isPrime(head)` as an invariant to `SieveSequenceV2`?
4. How many intermediate lemmas will sieve correctness require?