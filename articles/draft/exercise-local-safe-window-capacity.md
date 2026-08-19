# Exercise: Local Strike Capacity for 2-Gaps in a Sieve Sequence

**Status:** Draft exercise for mathematical verification.
**Author:** Mata, T. H., Independent Researcher
**Date:** 2026-08-15
**License:** [CC BY 4.0](../LICENSE)

This exercise is meant to be read after:

- [Formal Verification of the Sieve Sequence](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md)
- [Sieve Gap Survival: A Math-Only Follow-Up to Sieve Sequences](https://github.com/thiagomata/prime-numbers/blob/master/articles/draft/draft-sieve-gap-survival-math.md)

The goal is to prove a local capacity bound. The exercise does not ask you to
prove that many 2-gaps exist in the local window. Instead, it asks you to prove
that once enough local 2-gaps exist, the next filter does not have enough local
strikes to destroy all of them.

## 1. Background

A sieve sequence stage has a current head prime, a list of previous prime
filters, and a finite period. Let the current stage be `S`.

Use the following notation:

```text
p = current head prime of S
q = next prime after p
M = product of all primes smaller than p
```

The next stage adds `p` as a new filter. Values accepted by the previous
filters are expanded across a larger window. Then the new filter removes exactly
the values divisible by `p`.

The filter rule is the same everywhere:

```text
keep v if v is not divisible by p
remove v if v is divisible by p
```

The distinction between a global argument and a local argument is not the rule.
The distinction is the interval being counted.

In a complete global expanded block, one can count full lifted orbits. For each
old accepted value `r`, the values

```text
r, r + M, r + 2M, ..., r + (p - 1)M
```

cover all residue classes modulo `p`, because `M` is coprime to `p`. Therefore
exactly one of those `p` values is removed by the `p`-filter.

For 2-gaps, the same global orbit idea says that a current 2-gap

```text
(r, r + 2)
```

has `p` lifted copies, and exactly two of those lifted copies are destroyed:
one copy has its left endpoint divisible by `p`, and one copy has its right
endpoint divisible by `p`.

This exercise studies the local next safe window:

```text
[q, q^2)
```

This interval is the part of the next stage where accepted values are certified
prime by the usual square-bound argument. Unlike the complete global expanded
block, this local window is usually only a partial interval. It need not contain
complete lifted orbits. So instead of using full-orbit uniformity, we will use a
capacity bound: count how many local strikes the `p`-filter can possibly make.

## 2. Definitions

A local 2-gap before the `p`-filter is a pair

```text
(x, x + 2)
```

such that:

```text
q <= x
x + 2 < q^2
```

and both endpoints are consecutive accepted values before applying the
`p`-filter.

The `p`-filter destroys this 2-gap if it removes at least one endpoint:

```text
p divides x
```

or

```text
p divides x + 2
```

Let:

```text
W = [q, q^2)
```

and let:

```text
R(p, q) = number of multiples of p inside W.
```

## 3. Main Claim

Prove that:

```text
R(p, q) = floor((q^2 - 1) / p) - floor((q - 1) / p)
```

Then prove that the number of local 2-gaps destroyed by the `p`-filter is at
most:

```text
2 * R(p, q)
```

Therefore, if the number of local 2-gaps before filtering is `G_local`, and

```text
G_local > 2 * R(p, q),
```

then at least one local 2-gap survives the `p`-filter.

## 4. Tasks

### Task 1: Count Multiples in a Half-Open Interval

Prove the following elementary counting lemma.

For positive integers `a`, `A`, and `B`, with `A < B`, the number of multiples
of `a` in the half-open interval `[A, B)` is:

```text
floor((B - 1) / a) - floor((A - 1) / a)
```

Apply this lemma with:

```text
a = p
A = q
B = q^2
```

to obtain:

```text
R(p, q) = floor((q^2 - 1) / p) - floor((q - 1) / p).
```

### Task 2: Relate Filter Strikes to Removed Values

Show that the `p`-filter removes a value `v` from the local window only if `v`
is one of the `R(p, q)` multiples counted above.

Conclude that the number of removed local values is at most:

```text
R(p, q).
```

This is an upper bound. Some multiples of `p` might not be present among the
accepted values before filtering, so the actual number removed can be smaller.

### Task 3: Bound How Many 2-Gaps One Removed Value Can Destroy

Let `v` be a value removed by the `p`-filter.

A local 2-gap destroyed by removing `v` must have `v` as one of its endpoints.
There are only two possible local 2-gaps with endpoint `v`:

```text
(v - 2, v)
```

and

```text
(v, v + 2).
```

Therefore one removed value can destroy at most two local 2-gaps.

Conclude that the total number of destroyed local 2-gaps is at most:

```text
2 * R(p, q).
```

### Task 4: Prove the Survival Condition

Let `G_local` be the number of local 2-gaps before applying the `p`-filter.

Using Task 3, prove:

```text
if G_local > 2 * R(p, q),
then at least one local 2-gap survives the p-filter.
```

This is a pigeonhole argument. If there are more local 2-gaps than the maximum
number that can be destroyed, at least one local 2-gap remains.

## 5. Optional Stronger Variant

Suppose the local 2-gaps are endpoint-disjoint: no accepted value is the
endpoint of two different local 2-gaps.

Under this additional assumption, one removed value can destroy at most one
local 2-gap. Prove the sharper bound:

```text
destroyed local 2-gaps <= R(p, q).
```

Then prove the sharper survival condition:

```text
if G_local > R(p, q),
then at least one local 2-gap survives the p-filter.
```

This stronger statement requires the endpoint-disjointness assumption. Without
that assumption, the safe general bound is `2 * R(p, q)`.

## 6. What This Exercise Proves

This exercise proves a local capacity theorem:

```text
local survival follows if local 2-gaps outnumber local filter capacity.
```

It does not prove that the local window always contains that many 2-gaps. That
is a separate abundance question.

The exact result established here is:

```text
G_local > 2 * (floor((q^2 - 1) / p) - floor((q - 1) / p))
```

implies that at least one local 2-gap survives the transition from the current
stage to the next stage.

The exercise is deliberately local. It uses the same filtering rule as the
global sieve-sequence construction, but it avoids assuming that the local safe
window contains complete lifted residue orbits.

## 7. Suggested Final Write-Up

A complete student solution should contain:

1. A proof of the half-open interval multiple-counting formula.
2. A clear explanation that every removed local value must be a multiple of
   `p`.
3. A proof that one removed value can destroy at most two local 2-gaps.
4. The final pigeonhole argument proving survival.
5. A short note explaining why this is a capacity theorem, not a proof of local
   2-gap abundance.

## Appendix: Solution Sketches

**Task 1.** The multiples of `a` in `[A, B)` are exactly the numbers `ak`
with `ceil(A/a) <= k < ceil(B/a)`. The count of such integers `k` is
`ceil(B/a) - ceil(A/a)`, and the identity
`ceil(n/a) - 1 = floor((n - 1)/a)` converts this to
`floor((B - 1)/a) - floor((A - 1)/a)`.

**Task 2.** The `p`-filter removes `v` only when `p` divides `v`; inside the
window `W = [q, q^2)`, every such `v` is one of the `R(p, q)` multiples
counted in Task 1. Since some multiples of `p` may not be accepted values,
the number actually removed is at most `R(p, q)`.

**Task 3.** A destroyed local 2-gap must have a removed endpoint `v`, and the
only possible 2-gaps with endpoint `v` are `(v - 2, v)` and `(v, v + 2)`. So
one removed value is credited with at most two destroyed 2-gaps. If both
endpoints of one gap are removed, that gap is counted twice in this bookkeeping,
which only keeps the total an upper bound. Hence at most `2 * R(p, q)` local
2-gaps are destroyed.

**Task 4.** If `G_local > 2 * R(p, q)`, more local 2-gaps exist than the
maximum number the filter can destroy, so at least one survives.

**Variant (endpoint-disjoint 2-gaps).** Endpoint-disjointness means no two
local 2-gaps share an endpoint, so a removed value `v` can be the endpoint of
at most one local 2-gap. The same counting then gives at most `R(p, q)`
destroyed 2-gaps, and survival follows whenever `G_local > R(p, q)`.
