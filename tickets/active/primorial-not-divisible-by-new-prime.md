# Lemma: primorial not divisible by new prime

**Created:** 2026-06-19
**Status:** Draft lemma added, Stainless verification pending
**Depends on:** v0-next-level-construction.md (completed, 6006 valid)

## Goal

Prove `Calc.mod(PrimeUtils.primorial(primes), p.value) != BigInt(0)` — the product of existing primes is not divisible by a new prime `p` where:
- `primes` is a descending list of `Prime` objects
- `p` is a prime not in `primes`
- Every element of `primes` has value `< p.value`

## Current State

- Verification at 6006 valid
- `primeIsCoprimeWithSmallerList` proves `isCoprime(v, primeValues(primes))` — the converse direction (v not divisible by any list prime)
- `newPrimeNotInList` proves the new prime is not in the list
- `euclidPrimeGreaterThanHead` proves the new prime > head
- **Draft lemma added:** `PrimeUtils.primorialNotDivisibleByPrime` added WITHOUT `.holds` (Stainless verification pending)
- **Missing:** Verified lemma: `Calc.mod(product(primes), newPrime) != 0`

## Why Required

V2's constructor requires `Calc.mod(SieveUtils.product(primes.tail), primes.head) != BigInt(0)`. Without this lemma, that precondition is unverified. With the lemma, it follows from the `allPrimesSoFar` invariant and `newPrimeNotInList`.

## Approach

### Attempt 1: Direct induction (FAILED — Euclid's lemma requirement)

Proof by structural induction on `primes`:

1. Base case (`primes.tail.isEmpty`): `primorial = head.value`. Since `head.value < p.value`, `Calc.mod(head.value, p.value) = head.value != 0` by `ModSmallDividend`. **Proved.**

2. Inductive step: `Calc.mod(primorial(tail), p.value) != 0` (IH), and `Calc.mod(head.value, p.value) = head.value != 0`. 
   Need: `Calc.mod(head.value * primorial(tail), p.value) != 0`. This is the key sub-lemma: a prime `p` doesn't divide a product of two numbers if it doesn't divide either factor — i.e., Euclid's lemma.

The SMT solver (Z3) handles SPECIFIC small multiplications (e.g., `Calc.mod(7*30, 11)`) but times out on the ABSTRACT case `Calc.mod(h * tailPrim, p)` where `h` and `tailPrim` are variables.

### Attempt 2: Induction on `a` in `Calc.mod(a * b, p)` (FAILED — same wall)

Used `ModOperations.modAdd` to reduce `a*b` to `prev + b` where `prev = Calc.mod((a-1)*b, p)`. The `sum == p` case (where `prev + b = p`) requires Euclid's lemma — proving this case impossible IS the lemma itself.

### Attempt 3: Reduce modulo p first (requires Euclid's lemma)

Using `r = Calc.mod(tailPrim, p)` and proving `Calc.mod(h * tailPrim, p) == Calc.mod(h * r, p)` is doable with `assertMultipleModZero` and `ModAdd`. But the step `Calc.mod(h * r, p) != 0` still requires Euclid's lemma.

### Root Cause

Proving `Calc.mod(a * b, p) != 0` for prime `p` and `0 < a,b < p` requires Euclid's lemma:
> If `p` is prime and `p | a*b`, then `p | a` or `p | b`.

Z3's non-linear arithmetic handles concrete values but not the abstract case. Implementing Euclid's lemma in Stainless requires either:
- The extended Euclidean algorithm (Bezout's identity) — significant code but sound
- The minimal-counterexample proof using `Calc.mod(p, a)` — cleaner, uses well-founded induction

## Euclid's Lemma Proof Strategy (Future Work)

```scala
def euclidLemmaPrime(a: BigInt, b: BigInt, p: BigInt): Boolean = {
  require(p > 1)
  require(Prime.isPrime(p))
  require(a > 0)
  require(b >= 0)
  require(Calc.mod(a * b, p) == BigInt(0))  // p | a*b
  decreases(a)
  
  if (Calc.mod(a, p) == BigInt(0)) true     // p | a, trivial
  else {
    // p ∤ a. Let d = Calc.mod(p, a), then 0 < d < a.
    // Prove p | d*b (using p = q*a + d and p | a*b).
    // By induction on decreasing a, this gives p | b.
    val d = Calc.mod(p, a)
    assert(d > 0 && d < a)
    assert(Calc.mod(d * b, p) == BigInt(0))  // p | d*b — requires proof
    assert(euclidLemmaPrime(d, b, p))         // IH: p | b (since d < a)
    Calc.mod(b, p) == BigInt(0)
  }
}.holds
```

The step `Calc.mod(d * b, p) == BigInt(0)` requires algebraic proof:
- `d = p - Calc.div(p, a) * a`
- `d * b = (p - q*a)*b = p*b - q*(a*b) = p*b - q*(k*p) = p*(b - q*k)`
- Therefore `Calc.mod(d * b, p) == 0`

This algebraic manipulation of `Calc.mod` equations is the main implementation challenge.

## Validation

- After adding draft lemma (no `.holds`): 6006 valid, 0 invalid, 0 unknown.
- Full verification of the lemma will require a proof of Euclid's lemma.
- See also: `assert-no-divisor-by-factor-list.md` (related but different direction).
