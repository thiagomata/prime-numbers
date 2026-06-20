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
  val seq = SieveSequenceV0(primesSoFar)
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
`SieveSequenceV0.apply(1)`.

For a list such as `[5, 3, 2]`, `SieveSequenceV0` filters only the tail
`[3, 2]`. The head `5` is the starting value, not an active filter. Therefore
`25` passes the V0 tail filter. This means the equality

```scala
AllPrimesSoFarList.nextPrime(list).value ==
  SieveSequenceV0(AllPrimesSoFarList(list)).apply(BigInt(1))
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
- `SieveSequenceV0.apply(k)` is a verified tail-filter linear generator.
- `SieveSequenceV0.indexOfAccepted(value)` gives the completeness witness for
  any accepted value above the head.
- `SieveSequenceV0.assertSkipUntilNonMultiple(nextSeq, k, period)` now verifies
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
  - Explains why proving `SieveSequenceV0.apply(1)` is prime directly runs into
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
val seq = SieveSequenceV0(primesSoFar)
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

- `SieveSequenceV0.nextDoesNotPassAcceptedValue` is currently private. This
  may require adding a small public wrapper lemma for `k = 0`, or placing the
  bridge inside `SieveSequenceV0`.
- Verified 2026-06-21 as
  `SieveSequenceV0.assertApplyOneAtOrBeforeAccepted(value)`. The wrapper keeps
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
  val seq = SieveSequenceV0(primesSoFar)
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

### Alternative D: Change `SieveSequenceV0` to filter the head too

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
  `SieveSequenceV0.assertApplyOneAtOrBeforeAccepted(value)`. Verification
  result: `total: 6955 valid: 6955 invalid: 0 unknown: 0`.

Next target:

- Prove `AllPrimesSoFarList.nextPrime(list).value` passes the V0 tail filter,
  probably by reusing `PrimeUtils.primeIsCoprimeWithSmallerList` on the old
  complete prime list.
