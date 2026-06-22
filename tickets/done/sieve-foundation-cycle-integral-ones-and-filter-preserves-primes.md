# Sieve Foundation: CycleIntegral of [1] and Filter Preserves Primes

**Created:** 2026-06-13
**Updated:** 2026-06-13
**Status:** Completed ✅
**Depends on:** `prime-foundations-and-gap-proof.md`, `assert-no-divisor-by-factor-list.md`

---

## Goal

Prove two foundational properties for the sieve:

1. **CycleIntegral with cycle `[1]` produces natural numbers:** `CI(init, [1]).apply(n) = init + n + 1`
2. **Filtering out multiples of a prime preserves all primes:** If a list contains all primes, filtering by prime `p` keeps all primes

These are the base case and inductive step of the sieve's correctness proof.

---

## Current State

- **Verification:** 4837 valid, 0 invalid, 0 unknown ✅
- **Tests:** All 9 sieve tests passing ✅
- **`next()` status:** `@extern` (not in scope for this ticket)

---

## Scope

**Abstract proofs only** — no `CycleSieveSequence` references. The sieve will compose these later.

### Files to Create

| File | Purpose |
|------|---------|
| `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala` | Lemmas 1-2 |
| `src/main/scala/v1/chapter5/prime/properties/FilterPreservesPrimesProperties.scala` | Lemmas 3-5 |
| `articles/sieve-foundation.md` | New article documenting the proofs |

### Files to Update

| File | Change |
|------|--------|
| `articles/integral-cycle.md` | Add cross-reference to `sieve-foundation.md` in Future Work section |

---

## Lemmas

### Lemma 1: `assertCycleIntegralOfOnes(init, pos)`

**Statement:** For cycle = `MemCycle(List(1))`:
```
CI(init, cycle).apply(pos) == init + pos + 1
```

**Proof:** By induction on `pos`.
- Base: `CI(0) = cycle(0) + init = 1 + init`
- Step: `CI(n) = CI(n-1) + cycle(n) = CI(n-1) + 1`
- By induction: `CI(n) = init + 1 + n`

**Uses:** `assertDiffEqualsCycleValue`, `MemCycleProperties`

### Lemma 2: `assertCycleIntegralOfOnesStrictlyIncreasing(init, a, b)`

**Statement:** For cycle = `MemCycle(List(1))`, `b > a`:
```
CI(init, cycle).apply(b) > CI(init, cycle).apply(a)
```

**Uses:** Lemma 1

### Lemma 3: `assertPrimeNotDivisibleByDistinctPrime(q, p)`

**Statement:** If `q` and `p` are distinct primes:
```
isPrime(q) ∧ isPrime(p) ∧ q ≠ p ⟹ mod(q, p) ≠ 0
```

**Proof:** Case analysis:
- Case 1: `q > p` → `p ∈ [2, q)`, so `noDivisorInRange(q, 2, q)` implies `mod(q, p) ≠ 0`
- Case 2: `q < p` → `ModSmallDividend.modSmallDividend(q, p)` proves `mod(q, p) = q ≠ 0`

**Uses:** `Prime.isPrime`, `Calc.mod`, `ModSmallDividend.modSmallDividend`

### Lemma 4: `assertFilterPreservesAllPrimes(q, filterPrime)`

**Statement:** For any prime `q` that is not the filter prime:
```
isPrime(q) ∧ q ≠ filterPrime ⟹ mod(q, filterPrime) ≠ 0
```

**Uses:** Lemma 3

### Lemma 5: `assertFilteredContainsAllPrimes(originalPrimes, filteredPrimes, filterPrime)`

**Statement:** If a list contains all primes, and we filter out multiples of a prime `p` (keeping `p` itself), the filtered list still contains all primes.

**Uses:** Lemma 4, `SieveUtils.filterList`

---

## Lessons Learned from Related Tickets

| Lesson | Source | Application |
|--------|--------|-------------|
| Avoid `forall` over `BigInt` | next-level-requirements.md:646 | Lemma 5 uses `decreases(list.size)` |
| Compose lemmas, don't inline | next-level-requirements.md:663 | Call `.holds` lemmas via `assert()` |
| Prove each require in isolation | next-level-requirements.md:664 | One lemma per requirement |
| Direct structural recursion over lists | assert-no-divisor-by-factor-list.md:88 | Lemma 5 iterates through `list.head` |
| Inline transitivity with explicit `assert(nd*dp >= 0)` | assert-no-divisor-by-factor-list.md:89 | Lemma 3 if needed |

---

## Validation Plan

1. Run `just verify` after each lemma
2. Each lemma must pass before proceeding to next
3. No `CycleSieveSequence` references in code
4. No tickets mentioned in code or articles
5. No `@extern` or `@inline` — if needed, STOP and ASK FOR HELP

---

## Execution Order

1. ~~Create ticket~~ ✅
2. ~~Prove Lemma 1 → `just verify`~~ ✅
3. ~~Prove Lemma 2 → `just verify`~~ ✅
4. ~~Create `articles/sieve-foundation.md` with Lemma 1-2 proofs~~ ✅
5. ~~Add cross-reference in `articles/integral-cycle.md`~~ ✅
6. ~~Prove Lemma 3 → `just verify`~~ ✅
7. ~~Prove Lemma 4 → `just verify`~~ ✅
8. ~~Prove Lemma 5 → `just verify`~~ ✅
9. ~~Update `articles/sieve-foundation.md` with Lemma 3-5 proofs~~ ✅
10. ~~Update `OBJECTS.md` with new properties~~ ✅

---

## Progress Log

| Date | Action | Result |
|------|--------|--------|
| 2026-06-13 | Created ticket | Status: In Progress |
| 2026-06-13 | Lemma 1: `assertCycleIntegralOfOnes` | Verified ✅ (4760 valid, 0 invalid) |
| 2026-06-13 | Lemma 2: `assertCycleIntegralOfOnesStrictlyIncreasing` | Verified ✅ (4771 valid, 0 invalid) |
| 2026-06-13 | Lemma 3: `assertPrimeNotDivisibleByDistinctPrime` | Verified ✅ (4804 valid, 0 invalid) — used helper lemma `noDivisorInRangeImpliesModNonZero` |
| 2026-06-13 | Lemma 4: `assertFilterPreservesAllPrimes` | Verified ✅ (4814 valid, 0 invalid) — direct application of Lemma 3 |
| 2026-06-13 | Lemma 5: `assertFilteredContainsAllPrimes` | Verified ✅ (4837 valid, 0 invalid) — induction on list structure |
| 2026-06-13 | Created `articles/sieve-foundation.md` | Documented all 5 lemmas with formal statements and proofs |
| 2026-06-13 | Updated `articles/integral-cycle.md` | Added cross-reference to sieve-foundation.md in Future Work and References |
| 2026-06-13 | Ran tests | All 9 sieve tests passing ✅ |
| 2026-06-13 | Updated OBJECTS.md | Added new properties and lemmas |
