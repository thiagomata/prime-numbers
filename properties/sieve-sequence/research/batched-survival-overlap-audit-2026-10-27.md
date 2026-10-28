# Batched Survival: Low-Order Overlap Certificates

**Status:** Exact finite audit, 2026-10-27. The inequalities and copy-index
formulas below are mathematical consequences of classical inclusion-exclusion
and the Chinese remainder theorem. No generic positive lower bound, Stainless
verification, or historical novelty is claimed.

**Current progress:** Subsequent analytical work proves that the combined
possible loss budget satisfies B/F->0 for actual square transitions.
Sustaining an actual positive margin remains open. See the
[current research summary](batched-survival-progress.md); the finite audit
and measurements below retain their original scope.

## Question and Main Finite Finding

Can one combined filter certify survivors in a destination safe window using
a few overlap counts, even when a simple shot sum cannot?

The declared audit used nine starting heads and four destination rules: 36
cases in total. The pair-hit first-order bound was positive in 27 cases; the
third-order bound was positive in all 36. All nine square-jump cases had a
negative first-order bound but a positive third-order bound. The raw distinct
removed-value certificate was positive in 21 cases; it is a different bound.

This is a finite improvement in certificates, not a proof that the third-order
bound stays positive. The diagnostic computes exact hit multiplicities; it does
not establish an independent uniform estimate for the moments.

## Fixed Window and Batch

Let p>=5 and q>p be prime heads. Old filters are exactly the primes below p.
Write M for their product and B for the primes r with p<=r<q. The endpoint
window is [q,q squared), with both endpoints of a pair inside it. Define

```math
\begin{aligned}
\mathcal A&=\{a\in\mathbb Z:q\le a,\ a+2<q^2,\ \gcd(a(a+2),M)=1\},\\
C&=|\mathcal A|,\\
h(a)&=|\{r\in\mathcal B:r\mid a(a+2)\}|,\\
N_j&=|\{a\in\mathcal A:h(a)=j\}|,\\
S&=N_0.
\end{aligned}
```

The number h counts distinct prime filters hitting the pair, regardless of
which endpoint is hit. Since r>=5, one r cannot divide both endpoints.
All filters act on the same original candidates; no intermediate rotation or
recursive update is needed. Deletion is an order-independent union.

A surviving endpoint below q squared must be prime: a composite one would
have a prime divisor below q. Thus S is the number of twin-prime pairs in
this destination window.

The [exact batch property](../exact-batched-two-gap-survival.md) gives the
complete-period count. This note concerns a local portion of that period.

## Classical Overlap Certificate

For k>=0 let

```math
I_k=\sum_{a\in\mathcal A}\binom{h(a)}k,
\qquad I_0=C,
\qquad \binom hk=0\text{ when }k>h.
```

I_1 counts pair/prime incidences; I_2 counts pair/two-prime intersections;
I_3 counts pair/three-prime intersections. These are not counts of distinct
removed values.

Odd inclusion-exclusion truncations give lower bounds:

```math
\begin{aligned}
L_1&=C-I_1\le S,\\
L_3&=C-I_1+I_2-I_3\le S,\\
L_5&=C-I_1+I_2-I_3+I_4-I_5\le S.
\end{aligned}
```

Here the full formula is finite, and gives exactly S. The odd lower-bound
statement is the classical Bonferroni inequality, not a new sieve theorem.
See Paul Pollack, [*Not Always Buried Deep*, Theorem 6.8, printed p.177](https://www.pollack-math.net/NABDofficial.pdf#page=190).
The preceding identity (6.26) also gives a direct proof of the remainder used
here.

For h>0 the alternating binomial sum satisfies

```math
\sum_{k=0}^{m}(-1)^k\binom hk=(-1)^m\binom{h-1}m.
```

For h=0 the sum is 1. In particular, each candidate hit by one, two, or three
primes contributes zero to L_3; an unhit candidate contributes one; a candidate
hit by at least four contributes a nonpositive penalty. Summing yields

```math
\boxed{S-L_3=\sum_{j\ge4}\binom{j-1}3N_j\ge0.}
```

Consequently,

```math
\boxed{I_1-I_2+I_3<C\quad\Longrightarrow\quad S\ge L_3>0.}
```

This condition is sufficient, not necessary. If no pair receives four hits,
L_3 is exact. It may remain positive when higher intersections exist.

## Nonrecursive Analytical Expressions for the Moments

The moments can be written without first identifying the surviving pairs:

```math
I_k=\sum_{\substack{\mathcal R\subseteq\mathcal B\\|\mathcal R|=k}}
\left|\{a\in\mathcal A:\forall r\in\mathcal R,\ r\mid a(a+2)\}\right|.
```

Take one canonical old cyclic pair start a_0 in [0,M), including cyclic
boundary pairs represented by endpoints a_0 and a_0+2. Its translated starts
are a_0+jM. The eligible copy indices form the integer interval

```math
u=\left\lceil\frac{q-a_0}{M}\right\rceil,
\qquad
v=\left\lfloor\frac{q^2-3-a_0}{M}\right\rfloor.
```

For r in R, a hit means one of the two distinct classes

```math
j\equiv-a_0M^{-1}\pmod r
\quad\text{or}\quad
j\equiv-(a_0+2)M^{-1}\pmod r.
```

The inverse is taken modulo r. The Chinese remainder theorem combines these
choices into exactly 2^k distinct classes modulo d_R=product of primes in R.
A class c contributes

```math
\left\lfloor\frac{v-c}{d_{\mathcal R}}\right\rfloor
-
\left\lfloor\frac{u-1-c}{d_{\mathcal R}}\right\rfloor
```

copies when u<=v, and zero when the interval is empty. Sum over these classes,
old pair starts, and k-subsets R to obtain I_k. For k=0, the empty product is 1
and there is one class, recovering C.

This is a direct finite arithmetic description using the old cycle. It does
not require simulating intermediate sieve sequences. However, exact floor
sums are not automatically useful lower bounds: accumulating separate floor
errors over all classes, subsets, and old starts can swamp the desired margin.

## Finite Degree from the Endpoint Size

If p^d>=q squared for an integer d>=1, no endpoint below q squared can contain
d distinct batch-prime factors: their product would be at least p^d.
Therefore

```math
h(a)\le\min(|\mathcal B|,2(d-1)).
```

This bounds the degree of exact inclusion-exclusion for a given batch. It is
usually not sharp. It does not alone force a positive odd truncation.

## Declared Audit and Results

Starting heads were 5,7,11,13,17,19,23,29,31. For each p, four q rules were used:

| Rule | Definition |
|---|---|
| next | First prime greater than p |
| double | First prime at least 2p |
| power1.5 | First prime with q>p and q squared>p cubed |
| square | First prime greater than p squared |

No floating-point power calculation was used. The maximum destination was
967, and all endpoints were below 935089. For large old periods, the program
uses exact local gcd predicates rather than materializing the whole cycle;
G_p is obtained from its established product formula.

| Certificate | Positive cases out of 36 |
|---|---:|
| Raw distinct-value budget C-T | 21 |
| Pair-incidence bound L_1 | 27 |
| Cubic overlap bound L_3 | 36 |
| Fifth-order bound L_5 | 36 |

T counts distinct old accepted values rejected by the batch, including values
that do not belong to an initial pair. Since pair endpoints are disjoint after
filters 2 and 3, C-T is a valid lower bound. Neither T nor I_1 uniformly
dominates the other; the two bounds must not be conflated.

The complete square-jump subset is:

| p | q | Initial C | Distinct value removals T | L_1 | L_3 | Actual S |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 29 | 135 | 134 | -43 | 24 | 29 |
| 7 | 53 | 275 | 341 | -65 | 64 | 74 |
| 11 | 127 | 1142 | 1811 | -386 | 215 | 276 |
| 13 | 173 | 1738 | 2980 | -497 | 357 | 455 |
| 17 | 293 | 4228 | 8116 | -1379 | 760 | 1056 |
| 19 | 367 | 5862 | 11766 | -1623 | 1177 | 1539 |
| 23 | 541 | 11394 | 24619 | -3308 | 2216 | 2917 |
| 29 | 853 | 25902 | 60423 | -8955 | 4289 | 6224 |
| 31 | 967 | 31005 | 73853 | -9598 | 5591 | 7688 |

For p=31, q=967, the moments are I_1=40603, I_2=24732, I_3=9543,
giving L_3=5591. The hit histogram is

| Hits j | Number N_j |
|---:|---:|
| 0 | 7688 |
| 1 | 11634 |
| 2 | 7708 |
| 3 | 2523 |
| 4 | 1315 |
| 5 | 98 |
| 6 | 39 |

The cubic penalty is 1315+4*98+10*39=2097; hence
7688-2097=5591. The fifth-order bound loses only 39, giving 7649.
These equalities explain the finite certificate rather than invoking an
assumed uniform placement.

## What This Advances and What Remains Open

This audit identifies an overlap-corrected certificate that succeeds on
batches where the uncorrected pair-hit sum fails. It also supplies an exact
old-cycle/CRT expression for its inputs. Both use classical arithmetic.

The diagnostic obtains the moments by testing all batch primes on every old
candidate. The independent prime sieve is only a validation oracle. The audit
does not demonstrate that moment estimates are easier to prove uniformly than
direct survivor estimates.

The next mathematical obligation is specific: obtain bounds on C,I_1,I_2,I_3
for actual sieve cycles and a chosen destination rule that imply L_3>0 at
unboundedly many heads. The sample does not prove that cubic order always
suffices; a later negative L_3 would invalidate that stronger claim, not
survival or the exact batch construction.

The [batch-window candidate](../../../candidates/batched-window-survival.md)
remains open. The earlier [fixed-window budgets](fixed-window-shot-budget-2026-10-26.md)
use different windows and do not supply evidence for its universal threshold.

## Exact Reproduction

Run the following with python3 -B. It uses only the standard library and writes
no files. Its independent Eratosthenes oracle checks exact survivor sets;
algebraic controls check odd truncations, the full expansion, the degree bound,
and the cubic remainder. The full output includes every declared case.

```python
from math import gcd, isqrt, comb, prod
from collections import Counter

heads = [5, 7, 11, 13, 17, 19, 23, 29, 31]

def trial_prime(n):
    return n >= 2 and all((n // d) * d != n
                         for d in range(2, isqrt(n) + 1))

primes = [n for n in range(2, 1100) if trial_prime(n)]
cases = []
for p in heads:
    choices = [
        ("next", next(r for r in primes if r > p)),
        ("double", next(r for r in primes if r >= 2 * p)),
        ("power1.5", next(r for r in primes if r > p and r*r > p*p*p)),
        ("square", next(r for r in primes if r > p*p)),
    ]
    cases.extend((p, label, q) for label, q in choices)

limit = max(q*q for _, _, q in cases)
oracle = bytearray([1]) * limit
oracle[0:2] = bytes(2)
for d in range(2, isqrt(limit - 1) + 1):
    if oracle[d]:
        count = (limit - 1 - d*d) // d + 1
        oracle[d*d:limit:d] = bytes(count)

rows = []
for p, label, q in cases:
    modulus = prod(r for r in primes if r < p)
    global_pairs = prod(r - 2 for r in primes if 3 <= r < p)
    batch = [r for r in primes if p <= r < q]
    starts = [a for a in range(q, q*q - 2)
              if gcd(a*(a+2), modulus) == 1]
    histogram = Counter()
    survivors = set()
    for a in starts:
        h = sum((a // r)*r == a or ((a+2) // r)*r == a+2
                for r in batch)
        histogram[h] += 1
        if h == 0:
            survivors.add(a)
    exact_oracle = {a for a in range(q, q*q - 2)
                    if oracle[a] and oracle[a+2]}
    assert survivors == exact_oracle
    degree = 0
    while p**degree < q*q:
        degree += 1
    cap = min(len(batch), 2*(degree - 1))
    assert max(histogram, default=0) <= cap
    moments = [sum(count * comb(h, k) for h, count in histogram.items()
                   if h >= k) for k in range(cap + 1)]
    def lower(order):
        return sum((-1)**k * moments[k]
                   for k in range(min(order, cap) + 1))
    exact = sum((-1)**k * value for k, value in enumerate(moments))
    assert exact == len(survivors)
    bounds = [lower(k) for k in (1, 3, 5)]
    assert all(bound <= exact for bound in bounds)
    assert bounds[0] <= bounds[1] <= bounds[2]
    assert lower(3) == exact - sum(count * comb(h-1, 3)
                                 for h, count in histogram.items() if h >= 4)
    accepted = [n for n in range(q, q*q) if gcd(n, modulus) == 1]
    shots = sum(any((n // r)*r == n for r in batch) for n in accepted)
    assert exact >= len(starts) - shots
    rows.append((p, label, q, global_pairs, len(starts), shots,
                 *bounds, exact, max(histogram, default=0), cap,
                 dict(sorted(histogram.items()))))
    print(p, label, q, "G", global_pairs, "C", len(starts),
          "T", shots, "L1,L3,L5", bounds, "S", exact,
          "hmax/cap", max(histogram, default=0), cap,
          "hist", dict(sorted(histogram.items())))

print("SUMMARY", "cases", len(rows),
      "raw-positive", sum(row[4] > row[5] for row in rows),
      "L1-positive", sum(row[6] > 0 for row in rows),
      "L3-positive", sum(row[7] > 0 for row in rows),
      "L5-positive", sum(row[8] > 0 for row in rows),
      "rescued-by-L3", sum(row[6] <= 0 < row[7] for row in rows))
print("ALL CHECKS PASS")
```
