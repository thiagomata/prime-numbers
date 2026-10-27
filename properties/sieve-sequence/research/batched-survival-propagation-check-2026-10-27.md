# Signed Error and One-Step Propagation of the Cubic Certificate

**Status:** Proved finite transport identities and conditional implications,
plus a bounded empirical check on 2026-10-27. No uniform induction closure,
generic local-survival theorem, historical novelty, or Stainless verification
is claimed.

**Current progress:** Subsequent component proofs establish a nonnegative
actual loss budget B with B/F->0 under the square rule. The positive-margin
premise and its renewal remain open. See the
[current research summary](batched-survival-progress.md). The original
finite observations and executable diagnostic below are unchanged.

## Question and Scope

Can the signed-error condition be checked at early sieve heads, and can a
good current stage force a good following stage under identifiable features?

The first question has a finite affirmative answer in the declared sample.
The second splits into a proved fixed-destination preservation law and an
open moving-window balance. Stating the latter condition is not proving
that every real transition satisfies it.

The framework of a seed plus a preserved structural condition already appears
in the [self-propagating invariant candidate](../../../candidates/dream-sequence-self-propagating-invariant.md).
This note supplies transport formulas for the present cubic certificate.

## Notation

Let p>=5 and s be the next prime. For a prime destination q>p, let

```math
\begin{aligned}
W_q&=\{a\in\mathbb Z:q\le a\le q^2-3\},\\
\mathcal A_{p,q}
 &=\{a\in W_q:\gcd(a(a+2),M_p)=1\},\\
h_{p,q}(a)
 &=|\{r:r\text{ prime},\ p\le r<q,\ r\mid a(a+2)\}|,\\
w(h)&=1-h+\binom h2-\binom h3,\\
L(p,q)&=\sum_{a\in\mathcal A_{p,q}}w(h_{p,q}(a)).
\end{aligned}
```

The same definitions apply when the destination equals the starting head;
the batch is then empty.

Here M_p is the product of primes below p, and binomial terms vanish when
their lower index exceeds their nonnegative upper index. For h>=1,

```math
w(0)=1,\qquad w(h)=-\binom{h-1}3\le0.
```

Thus w is nonincreasing at nonnegative integer inputs. Classical Bonferroni
gives S(p,q)>=L(p,q), where S counts actual surviving pairs. The
[overlap audit](batched-survival-overlap-audit-2026-10-27.md) derives this
certificate and cites Pollack's exposition of the classical inequality.

For the density main term use the definitions in the
[analytical main/error study](batched-survival-analytic-main-and-error.md):

```math
L(p,q)=F(p,q)+\mathcal E(p,q),
\qquad
F(p,q)=H_q\delta_p B_3(p,q),
\qquad
H_q=q^2-q-2.
```

Checking E>-F is exactly checking L>0. It is not independent evidence for
an error estimate.

## 1. Proved Preservation When the Destination Is Fixed

Keep q fixed with s<=q. Advancing the old head from p to s installs filter
p and removes p from the remaining batch. A retained candidate is not hit
by p, so its remaining hit count is unchanged. A rejected candidate was
hit by p, and therefore had nonpositive weight.

Let

```math
\begin{aligned}
\mathcal K&=\{a\in\mathcal A_{p,q}:p\mid a(a+2)\},\\
A&=\sum_{a\in\mathcal K}\binom{h_{p,q}(a)-1}3\ge0.
\end{aligned}
```

The exact update is

```math
\begin{aligned}
L(s,q)
 &=L(p,q)-\sum_{a\in\mathcal K}w(h_{p,q}(a))\\
 &=L(p,q)+A\\
 &\ge L(p,q).
\end{aligned}
```

Consequently L(p,q)>0 implies L(s,q)>0. Actual final survivors are unchanged:
both constructions install all primes below the same destination q.

This is genuine finite preservation. By itself it repeatedly certifies the
same finite window, so it does not prove infinitely many twins.

### Exact Density and Error Updates

Put x=2/p and let e_3(s,q) be the third elementary symmetric sum of 2/r over
s<=r<q. Removing p from the batch gives

```math
\begin{aligned}
\delta_s&=(1-x)\delta_p,\\
B_3(p,q)&=(1-x)B_3(s,q)-x e_3(s,q),\\
F(s,q)-F(p,q)&=H_q\delta_p x e_3(s,q)\ge0,\\
\mathcal E(s,q)
 &=\mathcal E(p,q)+A-H_q\delta_p x e_3(s,q).
\end{aligned}
```

For a candidate hit by p, binomial(h-1,3) counts the triples of other filters
hitting it. Thus A is exactly a four-filter intersection count anchored at p;
the subtracted expression is its full-period density main term.

The sign of their difference is not controlled here. Fixed-target positivity
of L propagates, but neither monotonicity of E nor a fixed relative-error
bound follows from these identities.

### Purification Repays Exactly the Fixed-Target Penalty

The classical Bonferroni remainder in the
[overlap audit](batched-survival-overlap-audit-2026-10-27.md) gives the
nonnegative cubic penalty mass

```math
P(p,q):=S(p,q)-L(p,q)
 =\sum_{\substack{a\in\mathcal A_{p,q}\\h_{p,q}(a)\ge4}}
           \binom{h_{p,q}(a)-1}3\ge0.
```

Here S counts actual final twin pairs in the fixed destination window.
Installing the next old filter changes the certificate, but not that final
survivor set. Consequently

```math
\begin{aligned}
S(s,q)&=S(p,q),\\
P(s,q)&=S(p,q)-(L(p,q)+A)=P(p,q)-A.
\end{aligned}
```

Continue through consecutive starting heads p=p_0<...<p_k=q with the
destination q fixed. At the terminal head the remaining batch is empty, so
every accepted start has h=0 and P(q,q)=0. Telescoping proves

```math
\boxed{\sum_{i<k}A_i=P(p,q).}
```

Thus all fixed-target purification gain repays exactly the certificate's
original penalty. It does not increase the actual twin count. This sharpens
the interpretation of A>=0 without supplying a fresh source of twins or a
moving-window reserve-renewal theorem. In particular, a hypothetical last
twin pair cannot be contradicted merely by summing these repayments.

## 2. Exact Transport When the Destination Also Moves

Now let t>=q be a later prime destination. Use the intermediate starting
head s for both windows and put

```math
\begin{aligned}
\mathcal O&=\mathcal A_{s,q},&
\mathcal V&=\mathcal A_{s,t},&
\mathcal H&=\mathcal O\cap\mathcal V.
\end{aligned}
```

Old admissibility below s is the same on both sides; membership differences
come from the pair-start windows. Define

```math
\begin{aligned}
N&=\sum_{a\in\mathcal V\setminus\mathcal O}w(h_{s,t}(a)),\\
R&=\sum_{a\in\mathcal O\setminus\mathcal V}w(h_{s,q}(a)),\\
J&=\sum_{a\in\mathcal H}
       \bigl[w(h_{s,q}(a))-w(h_{s,t}(a))\bigr]\ge0.
\end{aligned}
```

N is the new-region weighted contribution, R the lost-region weighted
contribution, and J the extra penalty on the shared region. N and R can have
either sign. Because t>=q, the new batch only adds filters and w is
nonincreasing, proving J>=0.

Partitioning the two sums over their common and exclusive regions yields

```math
\boxed{L(s,t)=L(p,q)+A+N-R-J.}
```

This identity uses fixed values and simultaneous divisibility conditions;
it does not require replaying intermediate rotations.

## 3. A Bound on the Shared-Region Cost

For a shared start, both endpoints are below q squared. New filter primes
are at least q. An endpoint cannot have two distinct new prime divisors:
their product would be at least q squared. Hence

```math
j(a)=h_{s,t}(a)-h_{s,q}(a)\in\{0,1,2\}.
```

If h_{s,q}(a)=0, both endpoints are actual primes. A shared start is at least
t, so no prime below t divides either endpoint. Such a pair receives no new
hit and contributes zero to J.

For h=h_{s,q}(a)>=1, the binomial identity gives

```math
\begin{aligned}
w(h)-w(h+j)
 &=\binom{h+j-1}3-\binom{h-1}3\\
 &=j\binom{h-1}2+\binom j2(h-1)\\
 &\le(h-1)^2.
\end{aligned}
```

The middle equality uses j<=2, so the cubic term in j vanishes. Therefore

```math
0\le J\le
\sum_{\substack{a\in\mathcal H\\h_{s,q}(a)\ge1}}
           (h_{s,q}(a)-1)^2.
```

J measures increased negative weights of already blocked candidates, not the
loss of certified twin pairs in the shared safe region. The upper bound is
proved but may be too loose for a useful uniform propagation theorem.

### Fifth-Order Weights Eliminate the Shared Penalty

For odd d, define the classical Bonferroni weight and certificate

```math
\begin{aligned}
w_d(h)&=\sum_{k=0}^d(-1)^k\binom hk,\\
w_d(0)&=1,\qquad
w_d(h)=-\binom{h-1}d\quad(h\ge1),\\
L_d(p,q)&=\sum_{a\in\mathcal A_{p,q}}w_d(h_{p,q}(a))\le S(p,q).
\end{aligned}
```

These are the classical truncation identity and lower Bonferroni inequality,
not new inequalities; see Pollack,
[equation (6.26) and Theorem 6.8](https://www.pollack-math.net/NABDofficial.pdf#page=190).
In particular w_5(h)=0 for 1<=h<=5. Define A_d,N_d,R_d,J_d by replacing
w with w_d in the earlier transport definitions. The same partition of
candidate starts gives

```math
L_d(s,t)=L_d(p,q)+A_d+N_d-R_d-J_d,
\qquad A_d\ge0.
```

Now specialize to q first above p squared and t first above s squared.
If t=q there are no new hits. Otherwise the
[filtered-shot proof](batched-survival-filtered-shot-bound.md) gives q<s
squared and shows that a newly hit shared endpoint has the form r*ell,
where q<=r<t and s<=ell<q are primes.

For exactly one new prime hit, that endpoint has one old batch factor;
the opposite endpoint is below q squared<s to the fourth power and has at
most three old batch factors. Thus the old hit count is at most4 and the
new count at most5. For two new hits, they strike opposite endpoints with
distinct old prime cofactors, giving old count2 and new count4. Certified
pairs receive no new hits; candidates without new hits do not change weight.
Every affected blocked candidate therefore has zero fifth-order weight both
before and after the new filters. Hence

```math
\boxed{J_5=0,\qquad
L_5(s,t)=L_5(p,q)+A_5+N_5-R_5.}
```

This exact elimination holds at every square-rule p>=5. The same argument
gives J_d=0 for every odd d>=5. It removes an actual transition term rather
than estimating it, but does not prove the remaining signed balance positive.
The subscripts matter: these are higher-order certificates, not a claim that
the original cubic J vanishes.

### Seventh-Order Penalty Is Small Relative to the Cubic Benchmark

At a square destination, Bertrand gives q<2p squared. Every accepted
endpoint n therefore satisfies

```math
n<q^2<4p^4<p^5\qquad(p\ge5).
```

Old acceptance excludes factors below p. Thus each endpoint has at most
four prime factors counted with multiplicity, and the pair hit count is at
most8. The seventh-order weight is zero for blocked counts1 through7 and
equals -1 at count8. Write H_8(p,q) for the number of old-accepted starts
with exactly eight distinct batch hits. The classical remainder is then

```math
\boxed{L_7(p,q)=S(p,q)-H_8(p,q).}
```

Such a pair has four distinct prime factors at each endpoint: a prime at
least p cannot divide both endpoints, and neither endpoint can have five
factors. No factor repeats, since a repetition in addition to four distinct
factors would make the endpoint at least p to the fifth power. Each endpoint
is consequently a product of exactly four distinct primes. Every such factor
r satisfies r*p cubed<=n<4p to the fourth power, hence p<=r<4p.

Let k(p) count primes in [p,4p). The four-prime factor set uniquely determines
the lower endpoint a. Distinct starts give distinct four-prime subsets, so

```math
H_8(p,q)\le\binom{k(p)}4.
```

Chebyshev's prime-count upper bound gives k(p)<=pi(4p)=O(p/log p).
See Pollack, [Theorem 3.5, printed p.89](https://www.pollack-math.net/NABDofficial.pdf#page=102).
It follows that

```math
\begin{aligned}
0\le S(p,q)-L_7(p,q)
 &=H_8(p,q)=O\!\left(\frac{p^4}{(\log p)^4}\right),\\
\frac{S(p,q)-L_7(p,q)}{F(p,q)}
 &=O\!\left(\frac1{(\log p)^2}\right)\longrightarrow0.
\end{aligned}
```

The last line uses the proved eventual lower bound F(p,q)>=c p^4/log squared p
from the [component scale calculation](batched-survival-component-bounds.md).
F here remains the positive CUBIC density benchmark; it has not been
redefined as a seventh-order main term.

This is an unconditional approximation to the actual count at that scale,
using Bertrand and Chebyshev for the remainder estimate. It gives the actual
lower floor L_7>=-O(p^4/log^4 p), but not L_7>0 or S>0. If the true count
were zero, a small nonpositive seventh-order score would be fully compatible
with the bound. No new empirical run, positive-margin premise, or reserve
renewal theorem is hidden in this estimate.

This near-exactness must not be confused with small individual CRT density
errors. The [moment calibration](batched-survival-analytic-main-and-error.md#6-high-order-moments-require-nonnegligible-density-corrections)
proves nonzero negative limits for E_7/(H*delta) and E_8/(H*delta), while
leaving the combined signed certificate error open.

### Conditional Retention Through a Fixed-Factor Head Interval

Fix a real C>1 before letting the starting prime p tend to infinity. For
each prime r in [p,Cp], write q_r for the first prime greater than r squared,
q_0=q_p, and F_0=F(p,q_0). An initial actual twin pair whose start is at
least q_r is still in the new destination window: its upper boundary has
expanded, and genuine primes survive all filters below q_r. Only starts
below the new lower boundary can leave. Since twin starts here are5 modulo6,

```math
S(r,q_r)\ge S(p,q_0)
       -\left\lceil\frac{q_r-q_0}{6}\right\rceil.
```

This counts retained old twins; it assumes nothing about new ones. Bertrand
gives q_r<2r squared<=2C squared p squared. The preceding remainder bound
also holds uniformly over these heads. Consequently

```math
\begin{aligned}
L_7(r,q_r)
&=S(r,q_r)-H_8(r,q_r)\\
&\ge L_7(p,q_0)+H_8(p,q_0)
  -\left\lceil\frac{q_r-q_0}{6}\right\rceil-H_8(r,q_r)\\
&\ge L_7(p,q_0)-O_C(p^2)
                     -O_C\!\left(\frac{p^4}{(\log p)^4}\right)\\
&\ge L_7(p,q_0)-O_C\!\left(\frac{F_0}{(\log p)^2}\right).
\end{aligned}
```

The last comparison uses F_0>=c p^4/log squared p, and the constants are
uniform in r. For every fixed eta>0, all sufficiently late starting primes
therefore satisfy

```math
\boxed{L_7(p,q_0)\ge\eta F_0
\quad\Longrightarrow\quad
L_7(r,q_r)\ge\frac\eta2 F_0>0
\quad\text{for every prime }r\in[p,Cp].}
```

A cubic seed L_3(p,q_0)>=eta F_0 also suffices. At the proved hit counts
0<=h<=8, the seventh weight is at least the cubic weight: both are1 at0,
the seventh weight is0 at1 through7, and at8 its value -1 exceeds -35.
This is a comparison on that bounded range, not a general assertion that
higher odd truncations always improve.

This extends conditional certificate retention from the earlier shrinking
relative block to any FIXED multiplicative interval, for example [p,2p].
It exploits existing twins and the smaller seventh-order penalty. The
starting premise remains unproved at unbounded heads; the same pairs may
be certified repeatedly. Thresholds and constants depend on C and eta, so
one cannot let C grow without bound at one fixed seed. This corollary is
not an independent source of new twins or a reserve-renewal theorem.

## 4. What the Two Key Features Would Need to Establish

A seed plus a preserved positive bound would suffice. In terms of the actual
transport quantities, a sufficient condition is

```math
A+N-R-J\ge0.
```

Together with L(p,q)>0 it preserves the positive margin. A weaker sufficient
condition for the next margin merely to remain positive is

```math
A+N-R-J>-L(p,q).
```

For an analytical induction, replace the exact next-stage quantities by two
independently proved estimates:

1. a lower bound N>=n for the new-region weighted contribution;
2. an upper bound R+J<=b for the combined lost-region and shared-region cost.

Then

```math
L(s,t)\ge L(p,q)+A+n-b.
```

For example, b<=A+n preserves the margin. A known lower bound on A, including
the universal A>=0, can replace its exact value.

These estimates must follow from specified current structural information and
the transition arithmetic. Merely defining n=N and b=R+J restates the identity.
This transport identity alone does not supply those estimates. Subsequent
loss bounds are linked in the [research summary](batched-survival-progress.md);
a nontrivial closed positive-margin structural class remains unproved.
For an infinite argument, the chosen destination rule must also give unbounded
window starts; fixed q preservation alone does not do this.

## 5. Declared Early-Sequence Check

The first nine heads after installing filters 2 and 3 were used:
p=5,7,11,13,17,19,23,29,31. Let s be the next prime, q the first prime above
p squared, and t the first prime above s squared. The largest t was 1373.
The old cycles were accessed by exact gcd predicates, not fully materialized.

Main terms and errors were computed with exact rational arithmetic. The table
displays rounded decimals; all assertions use exact values.

| p | q | L(p,q) | Main F | Signed error E | L/F |
|---:|---:|---:|---:|---:|---:|
| 5 | 29 | 24 | 24.701233 | -0.701233 | 0.971611 |
| 7 | 53 | 64 | 58.926564 | 5.073436 | 1.086098 |
| 11 | 127 | 215 | 192.368151 | 22.631849 | 1.117649 |
| 13 | 173 | 357 | 338.047301 | 18.952699 | 1.056065 |
| 17 | 293 | 760 | 722.969464 | 37.030536 | 1.051220 |
| 19 | 367 | 1177 | 1145.914751 | 31.085249 | 1.027127 |
| 23 | 541 | 2216 | 2112.477430 | 103.522570 | 1.049005 |
| 29 | 853 | 4289 | 4048.756704 | 240.243296 | 1.059338 |
| 31 | 967 | 5591 | 5383.302352 | 207.697648 | 1.038582 |

Thus E>-F held in all nine cases. This says the cubic lower bounds are
positive in those cases; it does not establish an independent uniform theorem
for E. In particular E>=0 already fails at p=5, so that stronger all-stage
statement cannot be used without a later threshold or other hypothesis.

The transport check gave:

| p | s | q | t | A | N | R | J | Net A+N-R-J | Next L |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 7 | 29 | 53 | 5 | 38 | 2 | 1 | 40 | 64 |
| 7 | 11 | 53 | 127 | 10 | 155 | 4 | 10 | 151 | 215 |
| 11 | 13 | 127 | 173 | 38 | 137 | 2 | 31 | 142 | 357 |
| 13 | 17 | 173 | 293 | 57 | 401 | 7 | 48 | 403 | 760 |
| 17 | 19 | 293 | 367 | 111 | 356 | 2 | 48 | 417 | 1177 |
| 19 | 23 | 367 | 541 | 147 | 1003 | 4 | 107 | 1039 | 2216 |
| 23 | 29 | 541 | 853 | 265 | 2106 | 8 | 290 | 2073 | 4289 |
| 29 | 31 | 853 | 967 | 566 | 926 | 2 | 188 | 1302 | 5591 |
| 31 | 37 | 967 | 1373 | 566 | 4023 | 11 | 596 | 3982 | 9573 |

All nine moving balances were positive. That finite observation does not
prove a nonnegative balance for every later stage. N and R happened to be
positive here; their definitions do not make their signs universally positive.

## 6. Exact Reproduction and Evidence Limits

Run the following with python3 -B. It writes no files and needs only the
standard library. A separate Eratosthenes oracle verifies exact surviving
sets. The checks cover the exact rational decomposition, fixed-target
monotonicity, the moving-window partition, and preservation of certified pairs
in the shared region. The additional symbolic refinements above have
mathematical proofs; they are not asserted to be extra code tests.

No observed ratio, positive balance, or later-threshold conjecture is promoted
to a general preservation result.

```python
from math import gcd, isqrt, comb, prod
from fractions import Fraction
from functools import lru_cache

heads = [5, 7, 11, 13, 17, 19, 23, 29, 31]

def trial_prime(n):
    return n >= 2 and all((n // d)*d != n
                         for d in range(2, isqrt(n) + 1))

primes = [n for n in range(2, 1500) if trial_prime(n)]
def following(p):
    return next(r for r in primes if r > p)
def destination(p):
    return next(r for r in primes if r > p*p)
def weight(h):
    return 1 if h == 0 else (-comb(h-1, 3) if h >= 4 else 0)

limit = max(destination(following(p))**2 for p in heads)
oracle = bytearray([1]) * limit
oracle[0:2] = bytes(2)
for d in range(2, isqrt(limit-1) + 1):
    if oracle[d]:
        count = (limit-1-d*d)//d + 1
        oracle[d*d:limit:d] = bytes(count)

@lru_cache(None)
def stage(p, q):
    modulus = prod(r for r in primes if r < p)
    global_pairs = prod(r-2 for r in primes if 3 <= r < p)
    batch = [r for r in primes if p <= r < q]
    hits = {}
    for a in range(q, q*q-2):
        if gcd(a*(a+2), modulus) == 1:
            hits[a] = sum((a//r)*r == a or ((a+2)//r)*r == a+2
                          for r in batch)
    survivors = {a for a, h in hits.items() if h == 0}
    oracle_pairs = {a for a in range(q, q*q-2)
                    if oracle[a] and oracle[a+2]}
    assert survivors == oracle_pairs
    moments = [sum(comb(h, k) for h in hits.values() if h >= k)
               for k in range(4)]
    lower = moments[0]-moments[1]+moments[2]-moments[3]
    assert lower == sum(weight(h) for h in hits.values())
    assert lower <= len(survivors)
    elementary = [Fraction(1), Fraction(0), Fraction(0), Fraction(0)]
    for r in batch:
        for k in (3, 2, 1):
            elementary[k] += Fraction(2, r)*elementary[k-1]
    b3 = elementary[0]-elementary[1]+elementary[2]-elementary[3]
    length = q*q-q-2
    density = Fraction(global_pairs, modulus)
    errors = [Fraction(moments[k])-length*density*elementary[k]
              for k in range(4)]
    main = length*density*b3
    error = errors[0]-errors[1]+errors[2]-errors[3]
    assert main+error == lower
    assert (error > -main) == (lower > 0)
    return hits, lower, main, error, len(survivors), b3

rows = []
for p in heads:
    s = following(p)
    q, t = destination(p), destination(s)
    assert t >= q
    old, lower, main, error, survivors, b3 = stage(p, q)
    middle, middle_lower, _, _, middle_survivors, _ = stage(s, q)
    new, new_lower, _, _, _, _ = stage(s, t)
    assert set(middle) <= set(old)
    rejected = set(old)-set(middle)
    assert all((a//p)*p == a or ((a+2)//p)*p == a+2
               for a in rejected)
    assert all(middle[a] == old[a] for a in middle)
    assert middle_survivors == survivors
    purification = sum(comb(old[a]-1, 3)
                       for a in rejected if old[a] >= 4)
    assert middle_lower == lower+purification
    assert purification >= 0

    shared = set(middle) & set(new)
    gain = sum(weight(new[a]) for a in set(new)-set(middle))
    loss = sum(weight(middle[a]) for a in set(middle)-set(new))
    penalty = sum(weight(middle[a])-weight(new[a]) for a in shared)
    assert penalty >= 0
    assert all((middle[a] == 0) == (new[a] == 0) for a in shared)
    balance = purification+gain-loss-penalty
    assert new_lower == lower+balance
    ratio = lower/main if main != 0 else None
    rows.append((p, s, q, t, lower, main, error, ratio,
                 purification, gain, loss, penalty, balance, new_lower))
    print("p,s,q,t", p, s, q, t,
          "L3", lower, "main", round(float(main), 6),
          "E", round(float(error), 6),
          "L3/main", None if ratio is None else round(float(ratio), 6),
          "A,N,R,J", purification, gain, loss, penalty,
          "balance", balance, "nextL3", new_lower)

positive = sum(row[4] > 0 for row in rows)
monotone = sum(row[12] >= 0 for row in rows)
positive_gains = sum(row[9] > 0 for row in rows)
print("SUMMARY", "stages", len(rows), "error-condition", positive,
      "nonnegative-moving-balance", monotone,
      "positive-new-region-weight", positive_gains,
      "min-L3/main", round(float(min(row[7] for row in rows)), 6))
print("ALL CHECKS PASS")
```
