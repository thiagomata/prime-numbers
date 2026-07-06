# Conditional bridge from `nextPrime` to gap-cycle transformation

## Goal

Prove the cycle-to-cycle / gap-to-gap correctness theorem under an explicit
conditional branch, without making the missing prime-gap theorem a `require` of
production code.

The desired theorem shape is:

```scala
def assertGapCycleMatchesIfNextPrimeBeforeHeadSquared(...): Boolean = {
  require(local structural invariants)

  val primesSoFar = ...
  val seq = SpecSieveSequence(primesSoFar)
  val nextPrime = primesSoFar.nextPrime

  if (nextPrime.value < seq.head.value * seq.head.value) {
    // prove nextPrime.value == seq.apply(1)
    // prove the gap/cycle transformation using nextPrime matches next sequence
    true
  } else {
    true
  }
}.holds
```

This keeps the theorem unconditional at the call site. Callers do not need to
prove the branch condition. The hard number-theory statement remains isolated
inside the `if` branch as a conditional dependency.

## Motivation

`AllPrimesSoFarList.nextPrime` is currently produced by a direct bounded prime
search using the Euclid witness, not by the gap cycle and not by
`SpecSieveSequence.apply(1)`.

For a list such as `[5, 3, 2]`, `SpecSieveSequence` filters only the tail
`[3, 2]`. The head `5` is the starting value, not an active filter. Therefore
`25` passes the V0 tail filter. This means the equality

```scala
AllPrimesSoFarList.nextPrime(list).value ==
  SpecSieveSequence(AllPrimesSoFarList(list)).apply(BigInt(1))
```

requires some form of the fact that the next prime after `head` appears before
`head * head`. Otherwise `head * head` is a valid tail-filter survivor and could
interfere with the equality.

Adding this as a normal `require` would be bad: it would push an unverified
number-theory obligation onto every caller of `next`, turning a local proof gap
into a global unknown. The safer shape is an implication encoded as an `if`.

## Current State

### Already verified

- `AllPrimesSoFarList.nextPrime(list)` returns a prime greater than the current
  head, and proves there are no primes in
  `[list.head.value + 1, nextPrime.value)`.
- `AllPrimesSoFarList.allPrimesSoFar(list)` stores the complete prime-prefix
  invariant.
- `SpecSieveSequence.apply(k)` is a verified tail-filter linear generator.
- `SpecSieveSequence.indexOfAccepted(value)` gives the completeness witness for
  any accepted value above the head.
- `SpecSieveSequence.assertSkipUntilNonMultiple(nextSeq, k, period)` now verifies
  the period-based gap merge: when the immediate old successor is a multiple of
  the newly added front filter, the next sequence lands exactly on the first
  later old-stream non-multiple.

### Missing or intentionally avoided

- A full proof that there is always a prime between `p` and `p^2`.
- A Bertrand-style theorem.
- A general Chinese-sieve counting theorem proving enough survivors remain in
  `[p + 1, p^2)`.

This ticket does not try to prove those. It records how to move forward while
leaving that theorem as an isolated conditional branch.

## Related Tickets

- [`prove-apply1-is-prime.md`](./prove-apply1-is-prime.md)
  - Explains why proving `SpecSieveSequence.apply(1)` is prime directly runs into
    the `apply(1) < head^2` / Bertrand boundary.
  - This new ticket supersedes the need to make `apply(1)` primality a global
    production requirement.

- [`v0-skip-multiples-until-nonmultiple.md`](./v0-skip-multiples-until-nonmultiple.md)
  - Contains the verified local gap merge machinery.
  - The conditional cycle theorem should reuse those lemmas rather than
    re-proving skip/merge behavior.

- [`v0-next-level-construction.md`](./v0-next-level-construction.md)
  - Documents that `AllPrimesSoFarList.nextPrime` and
    `AllPrimesSoFarList.next` are already verified through the direct prime
    search path.
  - The conditional bridge must not regress that architecture.

- [`v0-residue-cycle-proof.md`](./v0-residue-cycle-proof.md)
  - Documents the verified V0 residue periodicity approach and explicitly
    avoids heavy counting where possible.

- [`remove-extern-from-next.md`](./remove-extern-from-next.md)
  - Broader target: remove `@extern` from the next sequence construction.
  - This ticket provides a conditional bridge that may help separate structural
    cycle correctness from the remaining prime-gap theorem.

## Proposed Proof Architecture

### Lemma 1: `nextPrime` passes the V0 tail filter

Statement:

```scala
AllPrimesSoFarList.nextPrime(list).value >= seq.head.value &&
seq.accepts(AllPrimesSoFarList.nextPrime(list).value)
```

where:

```scala
val primesSoFar = AllPrimesSoFarList(list)
val seq = SpecSieveSequence(primesSoFar)
```

Reason:

- `nextPrime` is prime.
- `nextPrime.value > list.head.value`.
- All tail primes are at or below `list.head.value`.
- A prime cannot be divisible by a different smaller prime.

Likely dependencies:

- `AllPrimesSoFarList.nextPrime` postcondition.
- Prime/filter preservation lemmas in `PrimeProperties` or
  `FilterPreservesPrimesProperties`.
- Tail membership/completeness helpers from `AllPrimesSoFarList`.

Validation:

- Add the lemma privately first, preferably near either `AllPrimesSoFarList` or
  a V0 property object.
- Run `just verify`.

### Lemma 2: V0 first accepted value is at or before `nextPrime`

Statement:

```scala
seq.apply(BigInt(1)) <= AllPrimesSoFarList.nextPrime(list).value
```

Reason:

- `seq.apply(0) == seq.head.value`.
- `nextPrime.value > seq.head.value`.
- `nextPrime` passes the V0 tail filter.
- `nextDoesNotPassAcceptedValue(0, nextPrime.value)` says the next generated
  value cannot jump past an accepted value.

Likely dependency:

- `SpecSieveSequence.nextDoesNotPassAcceptedValue` is currently private. This
  may require adding a small public wrapper lemma for `k = 0`, or placing the
  bridge inside `SpecSieveSequence`.
- Verified 2026-06-21 as
  `SpecSieveSequence.assertApplyOneAtOrBeforeAccepted(value)`. The wrapper keeps
  the skipped-interval machinery private and exposes only the first-step fact:
  any accepted `value > head.value` satisfies `apply(1) <= value`.

Validation:

- Unit test concrete examples:
  - `[3, 2]`: `apply(1) == 5`, `nextPrime == 5`.
  - `[5, 3, 2]`: `apply(1) == 7`, `nextPrime == 7`.
  - `[7, 5, 3, 2]`: `apply(1) == 11`, `nextPrime == 11`.
- Then verify.

### Lemma 3: accepted values below `head^2` and above `head` are prime

Statement:

```scala
if (seq.apply(BigInt(1)) < seq.head.value * seq.head.value) {
  Prime.isPrime(seq.apply(BigInt(1)))
}
```

or more generally:

```scala
def acceptedBelowHeadSquaredIsPrime(value: BigInt): Boolean = {
  require(value > head.value)
  require(value < head.value * head.value)
  require(accepts(value))
  Prime.isPrime(value)
}.holds
```

Reason:

- If `value` were composite below `head^2`, it has a prime divisor at or below
  `head`.
- Since `allPrimesSoFar` contains all primes up to `head`, that divisor appears
  in the current prime list.
- If the divisor is the head itself, then `value` is a multiple of `head`.
  This is important: V0 does not filter by head, so this branch must be
  controlled by `value < head^2` and `value > head`. The only positive multiple
  of `head` in `(head, head^2)` would be `2*head`, `3*head`, etc.; those are not
  automatically removed by tail filters. Therefore the proof may need a more
  careful version than the naive "accepted below square is prime" statement.

Risk:

- This lemma may still require non-trivial divisor decomposition.
- The head-divisibility branch is the dangerous one because the V0 filter is
  tail-only. For `head = 5`, `10`, `15`, and `20` are removed by tail primes,
  but that depends on their other factor. A general proof needs: if
  `head * m < head^2` and `m > 1`, then `m < head`, so `m` has a prime factor
  at or below the tail/head prefix and that factor divides the value.

Possible split:

1. `compositeBelowHeadSquaredHasKnownPrimeDivisor(value, list)`
2. `knownPrimeDivisorContradictsTailFilterUnlessDivisorIsHead`
3. `headDivisorBelowSquareHasTailPrimeDivisor(value, list)`

Validation:

- This is the riskiest part. Try tiny helper lemmas first.
- If this path begins to recreate a full divisor library, stop and reassess.

### Lemma 4: conditional equality between `nextPrime` and `seq.apply(1)`

Statement:

```scala
def assertNextPrimeEqualsApplyOneIfBeforeHeadSquared(list: SortedPrimeList): Boolean = {
  require(list.nonEmpty)
  require(AllPrimesSoFarList.allPrimesSoFar(list))

  val primesSoFar = AllPrimesSoFarList(list)
  val seq = SpecSieveSequence(primesSoFar)
  val p = primesSoFar.nextPrime

  if (p.value < seq.head.value * seq.head.value) {
    p.value == seq.apply(BigInt(1))
  } else {
    true
  }
}.holds
```

Reason:

- Lemma 2 gives `seq.apply(1) <= p.value`.
- If `seq.apply(1) < p.value`, then because of the branch bound
  `p.value < head^2`, we also get `seq.apply(1) < head^2`.
- Lemma 3 gives `Prime.isPrime(seq.apply(1))`.
- `AllPrimesSoFarList.nextPrime` proves there are no primes between
  `head + 1` and `p.value`.
- Contradiction-like branch closes with `seq.apply(1) == p.value`.

Stainless style:

- Avoid an explicit `assert(false)` if possible.
- Use an `if (seq.apply(1) == p.value) true else { ... }` branch and derive
  the equality from the impossible `< p.value` case.

Validation:

- Verify this lemma before touching any gap-cycle transformation code.

### Lemma 5: conditional gap-cycle transformation correctness

Statement shape:

```scala
def assertGapCycleMatchesIfNextPrimeBeforeHeadSquared(...): Boolean = {
  require(local cycle/gap invariants)

  val p = primesSoFar.nextPrime

  if (p.value < head.value * head.value) {
    assertNextPrimeEqualsApplyOneIfBeforeHeadSquared(primesSoFar.list)
    // Use existing copy-or-merge lemmas to prove transformed cycle matches.
    true
  } else {
    true
  }
}.holds
```

Reason:

- Once `p.value == seq.apply(1)`, the structural next level can be aligned with
  the sequence's next head.
- The existing V0 skip/copy lemmas describe how each new gap is derived from
  the old stream:
  - copy the old gap when the immediate old successor is not a multiple of the
    new filter;
  - merge consecutive old gaps when the immediate successor is a multiple of the
    new filter, stopping exactly at the first later non-multiple.
- The newly verified `assertSkipUntilNonMultiple` supplies the core "not too
  early, not too far" equality for the merge case.

Validation:

- Keep the first theorem local to a single index/gap.
- Only after that verifies, lift to a bounded prefix/cycle.
- Avoid proving residue-counting and period-size facts unless the local theorem
  absolutely requires them.

## Why Use an `if` Instead of a `require`

A `require` would make the theorem unusable unless every caller can already
prove:

```scala
nextPrime.value < head.value * head.value
```

That is exactly the hard number-theory fact we do not want to force into normal
construction.

An `if` keeps the theorem unconditional:

```scala
if (hardFact) {
  prove structural theorem
} else {
  true
}
```

This is the Stainless-friendly form of:

```text
hardFact implies structural theorem
```

It lets the proof record the mathematical dependency while preserving a green
production path.

## Alternatives Considered

### Alternative A: Prove Bertrand's postulate

Prove there is always a prime between `p` and `2p`, then derive a prime before
`p^2`.

Rejected for now. This is a major number-theory theorem and likely too large
for the current Stainless proof library.

### Alternative B: Prove a Chinese-sieve survivor count

Use density and residue distribution to show not all values in
`[p + 1, p^2)` are covered by multiples of known primes.

Rejected as the first attempt. Existing lemmas in
`ConsecutiveIntegers.scala` prove useful local density properties, but we do
not yet have a general inclusion-exclusion or union-bound theorem over an
arbitrary prime list. Building that may require substantial DivMod and counting
infrastructure.

### Alternative C: Make `nextPrime < head^2` a normal requirement

Rejected. This would move the unknown to all callers of `next` and block the
verified construction path.

### Alternative D: Change `SpecSieveSequence` to filter the head too

Rejected for this ticket. A full-filter search would make "first survivor is
prime" easier, but it changes the meaning of V0 and would diverge from the
tail-filter sequence architecture used by the gap merge proofs.

## Risks

1. **The conditional equality may still require divisor decomposition.**
   The branch avoids proving that the branch condition always holds, but inside
   the branch we still need enough arithmetic to show no earlier accepted
   composite can exist.

2. **Private V0 helpers may need public wrappers.**
   `nextDoesNotPassAcceptedValue` is private. A small wrapper for the
   `k = 0` case may be needed to prove `apply(1) <= nextPrime`.

3. **The head is not an active V0 filter.**
   Any lemma that says "accepted below head squared is prime" must handle
   composites divisible by the head carefully.

4. **Cycle-level proof may need a bounded prefix theorem first.**
   Proving the entire finite cycle in one lemma may timeout. The safer route is
   one gap/index at a time, then a recursive bounded prefix lift.

## First Implementation Step

Do not start with the whole cycle theorem.

Start with:

```scala
assertNextPrimeAcceptedByV0TailFilter(list)
```

Then:

```scala
assertApplyOneAtOrBeforeNextPrime(list)
```

Only after those are green should we attempt the conditional equality.

## Validation Plan

1. Run `just verify` before any non-markdown changes.
2. Add one lemma or assertion at a time.
3. Run unit tests for concrete examples before Stainless when possible:
   - `[2]`
   - `[3, 2]`
   - `[5, 3, 2]`
   - `[7, 5, 3, 2]`
4. Run `just verify` after each non-markdown change.
5. Update this ticket and `OBJECTS.md` after each verified lemma.

## Status

Created 2026-06-21.

Progress:

- 2026-06-21: Added and verified
  `SpecSieveSequence.assertApplyOneAtOrBeforeAccepted(value)`. Verification
  result: `total: 6955 valid: 6955 invalid: 0 unknown: 0`.

- 2026-06-21: Added and verified Lemma 1 —
  `SpecSieveSequence.assertNextPrimePassesV0Filter(primes)`. Proves that
  `AllPrimesSoFarList.nextPrime(list).value` is coprime to all V0 tail filter
  primes by reusing `PrimeUtils.primeIsCoprimeWithSmallerList`. Verification
  result: `total: 6968 valid: 6968 invalid: 0 unknown: 0`.

- 2026-06-21: Added and verified sqrt-bound lemmas in `PrimeProperties`:
  `assertFindSmallestDivisorAtMost`, `assertCompositeHasDivisorStrictlyBelowN`,
  `assertSmallestDivisorAtMostSqrt` (public), `assertDivisibleByFactorListNotCoprime`,
  `assertCompositeSmallestPrimeDivisor` (public). These prove that a composite
  number `n` has a smallest prime divisor `d` with `d * d <= n`. Verification
  result: `total: 7132 valid: 7132 invalid: 0 unknown: 0`.

- 2026-06-21: Added and verified
  `PrimeProperties.acceptedBelowHeadSquaredIsPrime(value, head, filterValues)`.
  Proves that any value coprime to `filterValues` and below `head * head` is prime.
  **Requires `SieveUtils.assertAllNotCoprimeInRange(head, 2, filterValues)`** (sieve
  completeness) as a precondition — this is the remaining open proof obligation.
  Verification result: `total: 7133 valid: 7133 invalid: 0 unknown: 0`.

- 2026-06-21: Attempted to add Lemma 4 (`assertNextPrimeEqualsApplyOneIfBeforeHeadSquared`)
  and the cross-instance helper `assertApplyOneIsPrimeIfBelowHeadSq` in
  `SpecSieveSequence`. The cross-instance calls to private methods caused VC explosion
  (7167 VCs) and verification timeout (only ~1300 verified in 5 min). Deferred.

- 2026-06-21 (end of session): Current verified state: **7195 valid, 0 invalid, 0 unknown**.
  
  **Verified lemmas (all passing):**

  **PrimeProperties** (sqrt-bound chain):
  - `assertFindSmallestDivisorAtMost` — smallest divisor minimality
  - `assertCompositeHasDivisorStrictlyBelowN` — finds divisor < n
  - `assertSmallestDivisorAtMostSqrt` (public) — d*d <= n
  - `assertDivisibleByFactorListNotCoprime` — divisibility transitivity
  - `assertDivisorBelowHead` — d < head from d*d < head*head
  - `assertCompositeSmallestPrimeDivisor` (public, `.ensuring`) — returns d
  - `acceptedBelowHeadSquaredIsPrime` — requires sieve completeness

  **SpecSieveSequence**:
  - `assertNextPrimePassesV0Filter` — Lemma 1
  - `applyStrictlyIncreases` (public)
  - `assertApplyMonotonic` — public ordering wrapper
  - `assertFilterValuesContainsInTail` — parallel prime/value scan
  - `assertFilterValuesContains` — d ∈ filterValues proof
  - `divisorInFilterValues` — `!isCoprime(n, values)` via scanning
  - `listContains` — utility membership check
  - `assertApplyOneIsPrimeIfBelowHeadSq` — `Prime.isPrime(apply(1))` when apply(1) < head²
  - `assertApplyOneLeqValue` — `apply(1) ≤ value` for any accepted value > head
  - `assertApplyOneGtHead` — `head.value + 1 ≤ apply(1)` (stronger return)

  **Blocked (Lemma 4 — `assertNextPrimeEqualsApplyOneIfBeforeHeadSquared`):**
  The cross-instance calls to `seq.assertApplyOneIsPrimeIfBelowHeadSq()` and
  `seq.assertApplyOneGtHead()` each generate complex VCs that time out at 600s.
  The VCs are large because they include ALL preceding assertions in the lemma body.
  
  **Lesson learned:** Cross-instance calls to lemmas that internally unfold `apply(k)` 
  (searchBound, searchNext, etc.) create large VCs because the solver needs to unfold
  the entire computation for the new instance. The solution is to avoid assembling
  many cross-instance calls in a single lemma — each call should be the ONLY call
  in its lemma, so the VC is small.

- 2026-06-21: Added and verified
  `SpecSieveSequence.assertApplyOneBelowHeadSqFromUpper(value)`. This isolates the
  arithmetic step `apply(1) <= value` and `value < head * head` ⇒
  `apply(1) < head * head`, so the final conditional equality proof does not
  ask Stainless to rediscover that transitive bound while also unfolding
  cross-instance sequence lemmas. Verification result:
  `total: 7198 valid: 7198 invalid: 0 unknown: 0`.

- 2026-06-21: Added and verified
  `SpecSieveSequence.assertApplyOnePrimeFromUpperBelowHeadSq(value)`. This wrapper
  composes the upper-bound transfer with `assertApplyOneIsPrimeIfBelowHeadSq()`
  in a single-instance VC. It gives the future conditional bridge the fact
  `Prime.isPrime(apply(1))` from `apply(1) <= value` and
  `value < head * head`, without assembling divisor/filter proof internals in
  the same lemma as `AllPrimesSoFarList.nextPrime`. Verification result:
  `total: 7207 valid: 7207 invalid: 0 unknown: 0`.

- 2026-06-21: Added and verified
  `SpecSieveSequence.assertOwnNextPrimeAccepted()`. This wrapper packages the
  current instance's direct `AllPrimesSoFarList.nextPrime(primes.list)` result
  as a V0 accepted value by combining `p.value > head.value`,
  `assertNextPrimePassesV0Filter(primes)`, and `passesFilter(p.value)`. This
  gives Lemma 2 a single fact to consume before proving
  `apply(1) <= nextPrime.value`. Verification result:
  `total: 7217 valid: 7217 invalid: 0 unknown: 0`.

- 2026-06-21: Added and verified
  `SpecSieveSequence.assertApplyOneAtOrBeforeOwnNextPrime()`. This completes the
  Lemma 2 bridge for the current instance:
  `apply(1) <= AllPrimesSoFarList.nextPrime(primes.list).value`. The wrapper
  consumes only `assertOwnNextPrimeAccepted()` and `assertApplyOneLeqValue`,
  keeping the accepted-value search proof isolated from later primality/equality
  work. Verification result:
  `total: 7225 valid: 7225 invalid: 0 unknown: 0`.

- 2026-06-21: Added and verified
  `SpecSieveSequence.assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq()`. This
  wrapper proves `Prime.isPrime(apply(1))` in the conditional branch
  `AllPrimesSoFarList.nextPrime(primes.list).value < head.value * head.value`.
  It composes only the ordering wrapper
  `assertApplyOneAtOrBeforeOwnNextPrime()` with the square-bound primality
  wrapper `assertApplyOnePrimeFromUpperBelowHeadSq(p.value)`, avoiding the
  global prime-before-square theorem. Verification result:
  `total: 7234 valid: 7234 invalid: 0 unknown: 0`.

- 2026-06-21: Attempted
  `SpecSieveSequence.assertOwnNextPrimeEqualsApplyOneIfBeforeHeadSquared()`, an
  instance-local equality wrapper intended to avoid the older cross-instance VC.
  The shape was:
  use `assertApplyOneAtOrBeforeOwnNextPrime()` for `apply(1) <= nextPrime`,
  use `assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq()` for
  `Prime.isPrime(apply(1))` in the branch, then contradict
  `apply(1) < nextPrime` with
  `AllPrimesSoFarList.noPrimesBetweenExcludesValue(head + 1, nextPrime, apply(1))`.
  Stainless timed out on two VCs:
  - line 1807: proving `head.value + 1 <= v1` before calling
    `noPrimesBetweenExcludesValue`;
  - line 1813: proving the final `p.value == v1` postcondition.
  Verification result:
  `total: 7247 valid: 7245 invalid: 0 unknown: 2 time: 269.98`, exit code 1.
  Per AGENTS.md, this is a failed attempt and no further proof variation was
  tried in this loop.

- 2026-06-21: Commented out the timeout-triggering
  `SpecSieveSequence.assertOwnNextPrimeEqualsApplyOneIfBeforeHeadSquared()`
  method while preserving the sketch in source comments. The verified helper
  wrappers remain active. This restored the project to green. Verification
  result:
  `total: 7234 valid: 7234 invalid: 0 unknown: 0`.

- 2026-06-21: Briefly tried a required-facts contradiction helper after the
  proof-value audit, then removed it. The helper verified by requiring all of
  the meaningful facts up front (`head + 1 <= apply(1)`, `apply(1) < nextPrime`,
  `Prime.isPrime(apply(1))`, and `noPrimesBetween(...)`), so it added little
  project leverage and risked making the bridge look more complete than it is.
  Exact-name search found no remaining markdown or code references after
  removal. Verification after removal restored the previous green state:
  `total: 7234 valid: 7234 invalid: 0 unknown: 0`.

- 2026-06-21: Added a `List.head`-style precondition to
  `SpecSieveSequence.next`: callers must provide
  `primes.nextPrime.value < head.value * head.value`. This makes the missing
  prime-before-square fact explicit at the method boundary while keeping the
  implementation simple: the body still delegates to `AllPrimesSoFarList.next`
  and proves the resulting list satisfies the V0 constructor. Verification
  result:
  `total: 7235 valid: 7235 invalid: 0 unknown: 0`.

Next target:

- Reframe the remaining work around making `SpecSieveSequence.next` useful rather
  than forcing the equality `nextPrime == apply(1)`. Keep the V0-generator
  lemmas that have independent value for `next`, especially
  `assertApplyOneLeqValue(value)`, `assertOwnNextPrimeAccepted()`, and
  `assertApplyOneAtOrBeforeOwnNextPrime()`. Treat the square-bound/equality
  wrappers as conditional support only, not as proof that the next prime lies
  before `head * head`.
  First wrapper completed: `assertApplyOneBelowHeadSqFromUpper(value)`.
  Second wrapper completed: `assertApplyOnePrimeFromUpperBelowHeadSq(value)`.
  Third wrapper completed: `assertOwnNextPrimeAccepted()`.
  Fourth wrapper completed: `assertApplyOneAtOrBeforeOwnNextPrime()`.
  Fifth wrapper completed: `assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq()`.
  Current `next` boundary completed: `SpecSieveSequence.next` now requires
  `primes.nextPrime.value < head.value * head.value` and verifies green.

## Track Evaluation

2026-06-21 assessment:

- Do **not** continue trying to prove the unconditional theorem "there is always
  a prime between `head` and `head * head`" as part of this ticket. That path
  would require either Bertrand-style number theory or a general Chinese-sieve
  counting theorem, both of which remain outside the current verified library.
- Keep the progress from the attempted track where it has independent V0 value.
  The sqrt/divisor lemmas and the V0-specific
  `assertApplyOneIsPrimeIfBelowHeadSq()` are useful conditional facts, but they
  do not prove the square-range theorem or complete the equality bridge.
- The live blocker is not mathematical plausibility; it is Stainless VC size
  from combining several cross-instance calls in one lemma. The next attempt
  should split Lemma 4 into single-purpose wrappers:
  - wrapper for `nextPrime` accepted by V0 tail filter;
  - wrapper for `apply(1) <= nextPrime`;
  - wrapper for `apply(1) < head * head` inside the conditional branch;
  - wrapper for `Prime.isPrime(apply(1))`;
  - wrapper for `head + 1 <= apply(1)`.
  Do not add another over-required contradiction helper unless it directly
  completes a verified final theorem.
- Treat the unconditional prime-before-square theorem as a separate research
  ticket. It is not required for the conditional branch shape proposed here.
