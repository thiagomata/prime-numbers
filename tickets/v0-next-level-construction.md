# Use SieveSequenceV0 to Build the Next-Level Sequence

**Created:** 2026-06-18
**Updated:** 2026-06-19
**Status:** Verified backbone helpers are landing. `nextPrime` is paused as a documented draft.
**Related tickets:**
- `prove-apply1-is-prime.md` — failed attempt to prove `apply(1)` is prime directly
- `check-project-guidance-docs-2026-06-17.md` — primary V0 implementation
- `next-constructor-requirement-assertions.md` — V2 next-level helpers
- `walk-based-pipeline.md` — V2 walk-based gap collection

---

## Goal

Given `SieveSequenceV0(primes)` where `primes = [p_n, p_{n-1}, ..., 2]`, produce `SieveSequenceV0(newPrimes)` where `newPrimes = [p_{n+1}, p_n, ..., 2]`.

---

## Phase 1: `nextPrime` Ownership — PAUSED

The live `SieveSequenceV0` implementation does not currently define a
`nextPrime` method. The correct ownership boundary is still the prime-prefix
domain: `AllPrimesSoFarList` stores the complete discovered prime prefix in
descending order, so it is the right class to eventually expose `nextPrime`.

Important correction: `nextPrime` is not `head`. For `[5, 3, 2]`, the current
head is `5`, and the next prime is `7`.

The attempted implementation shape was conceptually correct but not yet
Stainless-verifiable:

```scala
def nextPrime: Prime = {
  require(list.nonEmpty)

  PrimeProperties.primorialPlusOneModAny(list.list)
  val upperPrime = PrimeProperties.newPrimeFromEuclid(list.list)
  assert(upperPrime.value > head.value)

  searchNextPrimeUpTo(head.value + BigInt(1), upperPrime)
}.ensuring(res => res.value > head.value && Prime.isPrime(res.value))
```

This should remain a simple bounded linear search: use Euclid to obtain a finite
prime upper witness, then scan consecutive natural numbers from `head + 1` to
that witness and return the first `Prime.isPrime` candidate.

**Why paused:** `just verify` reached `5768 valid`, `0 invalid`, `1 unknown`,
timing out at:

```scala
assert(upperPrime.value > head.value)
```

We then tried a direct projection lemma from `allPrimesSoFar(list)`:

```scala
primeAtOrBelowHeadIsContained(value, list)
```

That exposed two smaller missing facts:

- `value >= 0` must be required before calling `Prime.isPrime(value)`.
- We need a helper that turns `noPrimesBetween(from, to)` plus
  `from <= value < to` into `!Prime.isPrime(value)`.

Both smaller facts have since been promoted into the live verified API. See
the Phase 2 backbone notes below.

**Fast tests after pausing:** `sbt 'set stainlessEnabled := false' 'testOnly v1.prime.* v1.seq.sieve.*'`
passes with 35 tests.

**Verification after pausing:** `just verify` passes with `5744 valid`,
`0 invalid`, `0 unknown`.

---

## Phase 2: `next` method — 3 PROOFS NEEDED

The draft `next()` method constructs a new V0 from `nextPrime()`:
```scala
def next: SieveSequenceV0 = {
  val newPrimeValue = nextPrime()
  val newPrime = Prime(newPrimeValue)
  val newSortedList = SortedPrimeList(newPrime :: primes.list.list)
  val newPrimes = AllPrimesSoFarList(newSortedList)
  SieveSequenceV0(newPrimes)
}
```

Three class invariants time out. Each needs a proof:

### Proof 1: `SortedPrimeList.isDescending(newPrime :: primes.list.list)`

Requires `newPrimeValue > head.value` (new head is larger than old head).

Already true: `searchNextPrime` starts at `head.value + 1` and returns a value ≥ that. But `nextPrime().ensuring` only says `acceptsPrime(res)`, not `res > head.value`. Need to strengthen `searchNextPrime`'s postcondition or `nextPrime()`'s ensuring to include `res > head.value`.

### Proof 2: `AllPrimesSoFarList.allPrimesSoFar(newSortedList)`

Requires:
- `Prime.isPrime(newPrimeValue)` — not yet proven (deferred to deep number theory: "there is always a prime between p and p²")
- `noPrimesBetween(head.value + 1, newPrimeValue)` — same deferred proof

This is the core of the Phase 2 deferral. It requires proving that `nextPrime()` returns the ACTUAL next prime (no primes skipped), which needs the prime-in-(p, p²) theorem.

### Proof 3: V0 constructor requirements for new instance

- `isCoprime(newPrimeValue, filterValues.tail)` — follows from `acceptsPrime(newPrimeValue)` ✓ (already verified)
- `mod(product(tail), newPrimeValue) ≠ 0` — needs "prime doesn't divide product of smaller primes" (Euclid's lemma for lists)

---

## New Lemma Needed

| Lemma | Proves | Needed for |
|-------|--------|------------|
| `res > head.value` in `searchNextPrime`/`nextPrime` postcondition | `nextPrime() > head.value` | Proof 1 |
| `isCoprime(newPrime, tail)` from `acceptsPrime(newPrime)` | V0 constructor require 3 | Automatic via acceptsPrime |
| `mod(product(tail), newPrime) ≠ 0` from `newPrime > tail` elements | V0 constructor require 4 | Proof 3 (Euclid's lemma for lists) |
| `Prime.isPrime(nextPrime())` | AllPrimesSoFarList invariant | Proof 2 (deferred) |

---

## Design Principle

Properties about primes (positivity, distinct primes are coprime, etc.) go in the `Prime` class, not scattered across the codebase.

---

## Phase 2 Backbone Lemmas Added

We moved two helper facts from draft direction into verified code in
`AllPrimesSoFarList.scala`.

### Verified: pointwise exclusion from a prime-free interval

`noPrimesBetweenExcludesValue(from, to, value)` proves that if
`noPrimesBetween(from, to)` holds and `value` is inside the half-open interval
`[from, to)`, then `value` is not prime.

This is the small induction Stainless needs when a later proof knows a
candidate value is inside a gap between two adjacent stored primes.

Validation:
- `just verify`
- Result: `5815 valid`, `0 invalid`, `0 unknown`

### Verified: complete prefix gives membership

`primeAtOrBelowHeadIsContained(value, list)` proves that if
`allPrimesSoFar(list)` holds, then every prime value at or below the current
head is already contained in the descending prime list.

This is the caller-facing version of the recursive `allPrimesSoFar` invariant:
the head is prime, the tail is complete, and there are no missing primes in the
gap between the tail head and the current head.

Validation:
- `just verify`
- Result: `5815 valid`, `0 invalid`, `0 unknown`

### Attempted and backed out: prime-not-contained implies above head

We tried the direct bridge:

```scala
primeNotContainedIsAboveHead(value, list)
```

Intended result: if `value` is prime and is not contained in a complete
`AllPrimesSoFarList`, then `value > list.head.value`.

The mathematical shape is right, but the standalone lemma timed out on its
postcondition:

```scala
value > list.head.value
```

Observed result:
- `5826 valid`, `0 invalid`, `1 unknown`
- Timed out at roughly 140 seconds

The lemma was removed to restore green. The likely next move is to avoid this
as a broad standalone bridge for now and instead prove the exact fact needed by
the future `nextPrime` construction at the call site, or expose a smaller
Euclid-result lemma from `PrimeProperties` that connects the constructed prime
to non-membership in the current list.

### Verified: bounded prime search carries skipped-prime range

`searchNextPrimeUpTo(current, upper)` is now a verified bounded loop that moves
only the natural-number counter. The prime list is not consumed or reduced by
the loop. The caller supplies `upper: Prime` as the finite witness, and the loop
checks:

```scala
if (Prime.isPrime(current)) result
else searchNextPrimeUpTo(current + 1, upper)
```

Its postcondition proves:

```scala
res.value >= current
res.value <= upper.value
Prime.isPrime(res.value)
noPrimesBetween(current, res.value)
```

This is the direct loop invariant we wanted: every counter value before the
result was tested and shown not to be prime, so the loop did not let any prime
pass.

Validation:
- `just verify`
- Result: `5843 valid`, `0 invalid`, `0 unknown`
