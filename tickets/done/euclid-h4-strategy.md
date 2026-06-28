# Euclid H4 — `euclidTheorem` Strategy

**Created:** 2026-06-11
**Updated:** 2026-06-12
**Status:** In Progress
**Depends on:** `euclid-full-formalization.md` (H1-H3 done)

---

## Goal

Verify `euclidTheorem(primes): Boolean` — prove that `newPrimeFromEuclid(primes)` produces a prime NOT in `primes`.

Current state: H1-H3 verified (~4984 valid). H4 is the only remaining blocker.

---

## The Problem

`primorialPlusOneModAny(primes)` is a `.holds` lemma — its postcondition is `res => res` (returns true), so the solver can't extract individual `Calc.mod(n, p) != 0` facts for each `p` in `primes`. The solver sees `true`, not the conjunction of modular facts.

---

## What We Tried

### Attempt 1: `checkAllNotV` with `numberIsMultipleOfAll`
- `numberIsMultipleOfAll(primes, m)` = structural check that `m` is divisible by every prime in `primes`
- `checkAllNotV` requires this, plus `n == m + 1` and `Calc.mod(n, v) == 0`
- **Timed out**: solver can't prove `numberIsMultipleOfAll(primes, primorial(primes))` — can't inline `primorial` deeply enough

### Attempt 2: `assert(checkPrimorialModZeroTailLoop(...))` before calling `checkAllNotV`
- Pre-prove the divisibility facts
- **Still timed out**: solver treats the assert and the require as separate VCs

### Attempt 3: Remove `.holds` from `checkPrimorialModZeroTailLoop`
- Changed it to return the raw conjunction
- **Wrong direction** — the inequality `primorialAll == primorial(primes)` is not explicit enough

---

## Current Approach (Option C variant): `euclidTailLoop`

Write a self-contained recursive function that:
1. Takes `primes`, `v` (divisor), `n` (primorial+1), `primorialSoFar` (accumulator)
2. Requires: `n == primorialSoFar * primorial(primes) + 1`, `Calc.mod(n, v) == 0`, `v > 1`
3. At each step: proves `Calc.mod(n, p) != 0` (same modular arithmetic as `primorialPlusOneTailLoop`)
4. Then deduces `p != v` from `Calc.mod(n, v) == 0` contradiction
5. Returns `p != v && recurse`
6. `.ensuring(res => !res || valueNotMatchesAny(primes, v))`

The function is NOT `.holds` — it returns the raw conjunction, so the solver inlines it and gets all the `p != v` facts. The `.ensuring` bridges from the conjunction to `valueNotMatchesAny`.

Call from `euclidTheorem`:
- `d != n` branch: `findSmallestDivisorResultModZero(n, d)` gives `Calc.mod(n, d) == 0` → call `euclidTailLoop(primes, d, n, 1)`
- `d == n` branch: `modSmallDividend(0, n) + ATimesBSameMod(0, n, 1)` gives `Calc.mod(n, n) == 0` → call `euclidTailLoop(primes, n, n, 1)`

---

## Key Observations

- `findSmallestDivisor(n, 2)` ensures `res >= 2` (from postcondition), so `v > 1` is guaranteed
- `Calc.mod` postcondition gives `0 <= mod < b` when `b > 0` and `mod == DivMod(a,b,0,a).solve.mod`
- `Prime.value > 1` (from `Prime.isPrime` require), so `p > 1` for `modSmallDividend(1, p)`
- `primorial` is NOT `.holds` — solver inlines it and can reason about its value

---

## Validation Plan

1. Comment out failing `euclidTheorem` → `just verify` should pass (~4984 valid)
2. Add `euclidTailLoop` → `just verify` (expect pass)
3. Uncomment new `euclidTheorem` → `just verify` (target: +1 valid)
4. Update ticket with results

---

## Risks

- `primorialUnfold` is `.holds` — need to verify the equality is usable by the solver
- Recursive requires for `primorialSoFar * p` may need explicit equality assertions
- Modular arithmetic proof duplicates `primorialPlusOneTailLoop` — but this is intentional to bypass `.holds` opacity
