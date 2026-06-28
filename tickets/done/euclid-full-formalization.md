# Euclid Full Formalization — Existence of a New Prime

**Created:** 2026-06-10
**Updated:** 2026-06-11
**Status:** In Progress — H1, H2 verified
**Depends on:** `prime-foundations-and-gap-proof.md` (completed), `assert-no-divisor-by-factor-list.md` (completed)

---

## Goal

Prove Euclid's theorem: given a non-empty list of primes `primes`, there exists a prime that is NOT in `primes`. More specifically:

> **Euclid's Theorem:** Let `primes = [p1, p2, ..., pn]` (all > 1). Then `primorial(primes) + 1` has a prime divisor that is not in `primes`. Therefore there are infinitely many primes.

Formally: construct a `Prime` object whose `value` is not in `primes`.

---

## Already Proven ✓

### `primorialPlusOneModAny(primes): Boolean` (PrimeProperties.scala:113)

Proves: for every prime `p` in `primes`, `Calc.mod(primorial(primes) + 1, p) != 0`.

Equivalently: no prime in `primes` divides `primorial(primes) + 1`. This establishes that any prime divisor of `primorial + 1` is **new** (not in `primes`).

---

## Still Needed

### H1: Every `n > 1` has a prime divisor

**Definition:** `findSmallestDivisor(n, from)` — finds the smallest integer `d` in `[from, n)` such that `Calc.mod(n, d) == 0`, or returns `n` if none found (meaning `n` is prime).

```scala
def findSmallestDivisor(n: BigInt, from: BigInt): BigInt = {
  require(n > 1 && from >= 2 && from <= n)
  decreases(n - from)
  if (from >= n) BigInt(0)  // signal: no divisor found, n is prime
  else if (Calc.mod(n, from) == BigInt(0)) from
  else findSmallestDivisor(n, from + 1)
}
```

Returns:
- `0` if `n` is prime (no divisor in `[2, n)` — matches `noDivisorInRange(n, 2, n)`)
- `d` where `2 <= d < n` and `Calc.mod(n, d) == 0` (the smallest divisor)

**Required lemmas:**
- `foundDivisorIsMinimal(n, d)` — proven by structural induction on `from`, ensures the first `d` found is indeed minimal
- `foundDivisorDivides(n, d)` — `Calc.mod(n, d) == 0` (from the condition that triggered return)
- `noDivisorFoundImpliesIsPrime(n)` — `findSmallestDivisor(n, 2) == 0` ⇒ `noDivisorInRange(n, 2, n)` (by induction)

**Estimated:** 30-40 lines across `findSmallestDivisor` + lemmas.

### H2: Smallest divisor is prime

**Lemma** `foundDivisorIsPrime(n, d)` (where `d = findSmallestDivisor(n, 2)`, `d != 0`):

Need to prove: `Prime.isPrime(d)`, i.e., `d > 1 && noDivisorInRange(d, 2, d)`.

**Proof by contradiction:** If `d` had a divisor `e` in `[2, d)`, then:
- `Calc.mod(d, e) == 0` and `Calc.mod(n, d) == 0` (from H1)
- By transitivity of divisibility: `Calc.mod(n, e) == 0` (uses `assertDivTransitive` from `SieveUtils.scala:58` or inline the transitivity as `assertNoDivisorByFactorList` does)
- Since `e < d` and `e` divides `n`, `findSmallestDivisor(n, 2)` would have returned `e` or a smaller divisor — contradiction with minimality.

**Risk:** The `assertDivTransitive` call may cause solver timeout (as seen in `assert-no-divisor-by-factor-list.md`). If so, inline the transitivity proof as in `assertNoDivisorByFactorList` (SieveUtils.scala:149-158).

**Estimated:** 20-30 lines (or more if transitivity needs inlining).

### H3: Construct the new `Prime`

**Function** `newPrimeFromEuclid(primes): Prime`:

```scala
def newPrimeFromEuclid(primes: List[Prime]): Prime = {
  require(primes.nonEmpty)
  require(primorialPlusOneModAny(primes))
  
  val n = PrimeUtils.primorial(primes) + 1
  val d = findSmallestDivisor(n, 2)
  
  if (d == BigInt(0)) {
    // n itself is prime
    assert(isPrime(n))  // from H1 lemma: noDivisorFoundImpliesIsPrime
    Prime(n)
  } else {
    // d is the smallest divisor, and it's prime (from H2)
    assert(isPrime(d))  // from H2
    Prime(d)
  }
}
```

**Additional proof needed:** The returned `Prime` is NOT in `primes`:
- If `d == 0` (n itself is prime): suppose `n` is in `primes`, then `Calc.mod(n, p) == 0` for `p = n`, contradicting `primorialPlusOneModAny(primes)` (proves `Calc.mod(primorial + 1, p) != 0` for all `p` in `primes`).
- If `d > 0`: suppose `d` is in `primes`, then `Calc.mod(primorial + 1, d) == 0` (since `d` divides `n = primorial + 1`), again contradicting `primorialPlusOneModAny(primes)`.

**Estimated:** 15-20 lines.

### H4: `euclidInfinitePrimes(primes)` wrapper

The final theorem: "there exists a prime not in `primes`." This is an existence statement. In Stainless, we witness it by constructing the prime:

```scala
def euclidInfinitePrimes(primes: List[Prime]): Prime = {
  // Ensures: result is a prime, and result is not in primes
  primorialPlusOneModAny(primes)
  newPrimeFromEuclid(primes)
}.ensuring(result => !primes.contains(result))
```

Or similarly, prove a property about it:

```scala
def euclidTheorem(primes: List[Prime]): Boolean = {
  require(primes.nonEmpty)
  primorialPlusOneModAny(primes)
  val newPrime = newPrimeFromEuclid(primes)
  !primes.contains(newPrime)
}.holds
```

**Estimated:** 5-10 lines.

---

## Total Estimated Complexity

| Component | Lines | Dependencies |
|---|---|---|
| `findSmallestDivisor` | 15 | — |
| H1 lemmas (minimality, implies prime) | 20-25 | `findSmallestDivisor` |
| H2 lemma (found divisor is prime) | 20-30 | H1 + `assertDivTransitive` |
| H3 `newPrimeFromEuclid` | 15-20 | H1 + H2 + `primorialPlusOneModAny` |
| H4 `euclidTheorem` | 5-10 | H3 |
| **Total** | **75-100** | |

---

## Alternatives Considered

### A1: Redefine `Prime` to use `findSmallestDivisor`

**Proposal:** Change `Prime.isPrime(n)` to `findSmallestDivisor(n, 2) == n` instead of `noDivisorInRange(n, 2, n)`.

| Pro | Con |
|---|---|
| Direct match for Euclid proof | Breaks ALL existing proof cache (4641 VCs) |
| Potential reuse in sieve | Requires re-verification of entire project |
| The equivalence proof would be done once as a `holds` lemma, not per-usage | High risk of new verification failures in unrelated code |

**Decision:** Rejected. The refactoring risk outweighs the benefit. Keep `Prime` as-is and prove equivalence via a bridge lemma.

### A2: Prove `findSmallestDivisor` ↔ `noDivisorInRange` equivalence only

Rather than using `findSmallestDivisor` for the proof, we could extend `noDivisorInRange` to find the first divisor and prove it's prime directly.

**Pro:** Reuses existing `noDivisorInRange` structure. No new functions needed.
**Con:** `noDivisorInRange` is a `Boolean` predicate; extending it to RETURN a divisor requires refactoring or a second function anyway. The `findSmallestDivisor` function is the natural choice.

**Decision:** Use `findSmallestDivisor` + equivalence lemma to bridge.

### A3: Use `@extern` for solver blockers

If the transitivity chain in H2 times out (as with `assertDivTransitive` in `assert-no-divisor-by-factor-list.md`), mark the transitivity lemma as `@extern` to make it an axiom.

**Risk:** `@extern` bypasses verification; the lemma must be trivially true by inspection. Use only as last resort.

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| `assertDivTransitive` times out in H2 | Blocks H2-H4 | Inline transitivity proof (pattern from `assertNoDivisorByFactorList` in SieveUtils) |
| `k >= 0` precondition on `assertMultipleModZero` | Blocks inlined transitivity | `Calc.div(n, d) * Calc.div(d, p) >= 0` — need `assert(nd * dp >= 0)` (both non-negative since `n, d > 0`) |
| `isPrime` requirement for `Prime` constructor | Block to construct new Prime | Must prove `noDivisorInRange(d, 2, d)` from the smallest divisor lemma |
| `!primes.contains(result)` proving | Block H4 | If structural containment check fails, use a custom `notInList` lemma with structural recursion |
| `findSmallestDivisor` recursion fails termination check | Block H1 | `decreases(n - from)` — always positive since `from <= n` |
| `primorial + 1` can overflow `BigInt` in Stainless | No theoretical risk | `BigInt` is unbounded in Stainless |

---

## Validation Plan

1. **H1 validation:** `just verify` after `findSmallestDivisor` + minimality lemma
2. **H1 → H2 validation:** Add `foundDivisorIsPrime` lemma, verify in isolation with concrete test case (e.g., `primes = [2, 3, 5, 7, 11, 13]`)
3. **H2 → H3 validation:** Verify `newPrimeFromEuclid` constructs a valid `Prime`
4. **H4 validation:** Verify `euclidTheorem` with `primes.contains(result)` check
5. **Full regression:** Run `just verify` to ensure no regressions in the 4600+ existing VCs

---

## Key Classes and Methods

| Class/Method | Location | Role |
|---|---|---|
| `Prime.isPrime(n)` | `Prime.scala:30` | Current primality test: `n > 1 && noDivisorInRange(n, 2, n)` |
| `Prime.noDivisorInRange(n, from, to)` | `Prime.scala:18` | Tail-recursive divisor search (Boolean) |
| `Prime(value)` | `Prime.scala:8` | Requires `isPrime(value)` at construction |
| `PrimeUtils.primorial(primes)` | `PrimeUtils.scala:55` | Product of all primes in list |
| `PrimeUtils.primorialUnfold(primes)` | `PrimeUtils.scala:77` | Lemma: `primorial = head * primorial(tail)` |
| `PrimProperties.primorialPlusOneModAny(primes)` | `PrimeProperties.scala:113` | Proves `mod(p + 1, p_i) != 0` for all p_i |
| `SieveUtils.assertDivTransitive(c, b, a)` | `SieveUtils.scala:58` | If `b|c` and `a|b` then `a|c` (may need inlining) |
| `SieveUtils.assertModZeroImpliesDivTimesBEqualsA(a, b)` | `SieveUtils.scala:39` | If `mod(a, b) == 0` then `div(a, b) * b == a` |
| `SieveUtils.assertMultipleModZero(k, n)` | `SieveUtils.scala:50` | Proves `mod(k * n, n) == 0` |
| `SieveUtils.assertNoDivisorByFactorList(n, d, primes)` | `SieveUtils.scala:136` | Key reference: inline transitivity pattern to avoid solver timeout |
| `ModOperations.modZeroPlusC(a, b, c)` | `ModOperations.scala:115` | If `mod(a, b) == 0` then `mod(a + c, b) == mod(c, b)` |
| `ModSmallDividend.modSmallDividend(a, b)` | `ModSmallDividend.scala` | If `b > a >= 0` then `mod(a, b) == a` |

---

## Hypothesis: Solver Behavior with `assertDivTransitive`

Based on the `assert-no-divisor-by-factor-list.md` experience:

1. **H1 (smallest divisor) should be fast** — pure structural recursion on `from`, simple conditions
2. **H2 (found divisor is prime) may timeout** — the transitivity chain `n/d=0 ∧ d/e=0 ⇒ n/e=0` requires the same reasoning that blocked `assertNoDivisorByFactorList`
3. **Mitigation confirmed:** If H2 times out, follow the same pattern as `assertNoDivisorByFactorList` — inline the transitivity proof directly, do NOT call `assertDivTransitive`
4. **Key requirement for inlining:** `assert(nd * dp >= 0)` where `nd = Calc.div(n, d)`, `dp = Calc.div(d, p)` — non-trivial but provable since all values are positive

---

## Open Questions

1. **Should `findSmallestDivisor` return `n` (meaning "prime") or 0?** Both work. Return `n` simplifies the `Prime(n)` construction since we already have `isPrime(n)` proven. Return 0 is the traditional sentinel. **Preference:** return `n` for `n` prime (avoids sentinel, cleaner construction).

2. **Where should new code live?** `PrimeProperties.scala` extends naturally (adds Euclid lemmas). `PrimeUtils.scala` for `findSmallestDivisor`. Both are already in the `v1.prime` package.

3. **Should we prove `!primes.contains(result)` or a weaker statement?** The weaker "there exists some prime not in `primes`" is the classical theorem. But constructing it and proving it's not in the list is more satisfying and directly supports the sieve's claim of generating new primes.
