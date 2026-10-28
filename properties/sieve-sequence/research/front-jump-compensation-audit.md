# Bounded audit of first-candidate jump compensation

**Status:** Exact finite arithmetic diagnostic. No compensation theorem,
asymptotic evidence, Stainless verification or novelty is claimed.

## Question and coordinate choice

Does a large advance of the first surviving candidate force smaller advances
at following prime filters? The [Distinguished Head Spacer candidate](
../../../candidates/distinguished-head-spacer.md) already identifies the
moving-head placement problem, while the [Dream Sequence candidate](
../../../candidates/dream-sequence-self-propagating-invariant.md) distinguishes
absolute deletion from recovery through a growing threshold.

To isolate filter deletion, fix an absolute anchor X above every tested head.
Define

```math
A_p(X)=\min\{a\ge X:\ s\nmid a(a+2)
\text{ for every prime }s<p\}.
```

For consecutive prime heads p<q<r, let

```math
\begin{aligned}
J_p(X)&=A_q(X)-A_p(X),\\
J_q(X)&=A_r(X)-A_q(X),\\
F_p&=q^2-p^2,\qquad F_q=r^2-q^2.
\end{aligned}
```

This fixed-anchor observable is different from the first candidate above the
moving head. It avoids advances caused merely by passing a genuine twin pair.
These numerical anchors are not assumed to lie beyond an actual last twin.

## Primary test: two consecutive square-frontier excesses

The predeclared bounded falsifier was

```math
J_p(X)>F_p\quad\text{and}\quad J_q(X)>F_q.
```

Search incoming primes7..47, with candidate starts at least100 and both
endpoints at most200000. Every prime below the relevant head is installed.
Each old candidate start a is used once as a representative anchor X=a;
anchors between old starts have the same three minima as the next old start.
All anchors exceed the largest tested head59.

Only cases where the first jump is positive need checking. Missing later
minima at the finite cap are censored, not treated as infinite jumps.

| Incoming p | Completed positive-first cases | Both jumps positive | First jump > F_p | Both jumps > respective F | Censored |
|---|---:|---:|---:|---:|---:|
| 7 | 5710 | 1035 | 0 | 0 | 1 |
| 11 | 2596 | 399 | 0 | 0 | 1 |
| 13 | 1798 | 216 | 0 | 0 | 1 |
| 17 | 1166 | 115 | 9 | 0 | 0 |
| 19 | 921 | 79 | 0 | 0 | 0 |
| 23 | 674 | 45 | 0 | 0 | 0 |
| 29 | 490 | 40 | 2 | 0 | 0 |
| 31 | 426 | 16 | 0 | 0 | 0 |
| 37 | 328 | 17 | 0 | 0 | 0 |
| 41 | 272 | 18 | 2 | 0 | 0 |
| 43 | 259 | 10 | 0 | 0 | 0 |
| 47 | 217 | 5 | 0 | 0 | 0 |

No primary falsifier was found. But only13 representative first-start cases
crossed the first threshold. They are not independent statistical observations;
no probability interpretation is assigned. Each tested (p,a) is distinct by
enumeration, rather than counting every integer anchor separately.

For example, at p=29,q=31,r=37, one such chain is

```math
A_{29}(36161)=36161,\quad
A_{31}(36161)=36299,\quad
A_{37}(36161)=36341.
```

Its jumps138,42 compare with frontier increments120,408. This is a bounded
example of the comparison, not a proof of forced compensation. The domain and
prime range are small, and at most3 boundary cases lack full observations.

## Secondary exploratory test: must the next jump be strictly smaller?

After the primary run, a weaker notion of a large jump was checked separately:
both jumps exceed their incoming prime and the second is not smaller.
This exploratory threshold is not substituted for the primary criterion.

At the fixed anchor X=1097,

```math
A_7(X)=1097,\qquad A_{11}(X)=1109,\qquad A_{13}(X)=1121.
```

The first two pairs are destroyed through their upper endpoints:

```math
1099=7\cdot157,\qquad1111=11\cdot101.
```

Consequently

```math
J_7(X)=12,\qquad J_{11}(X)=12.
```

All earlier filters are respected and each reported minimum is checked below
by an independent forward scan using separate endpoint gcd tests. No new
prime factors are inferred from a fitted model.

This is a counterexample to mandatory strict decrease of successive positive
jumps, even when both exceed their incoming prime. It does not refute
nonincrease, nor does it satisfy the primary frontier thresholds72 and48.
The anchor is1090 above head7; this is not an example at the moving head.

## Exact reproduction

Run the following read-only stdlib snippet with python3 -B. It writes no files
and imports no project modules. The cap includes endpoints, not just starts.
It prints the primary table and verifies the two illustrative chains using a
different forward-search predicate from the stage-list lookup.

```python
from bisect import bisect_left
from math import gcd

cap = 200000
primes = [n for n in range(2, 60)
          if all((n // d) * d != n for d in range(2, n))]
stages = {}
old = []
for p in primes:
    stages[p] = [a for a in range(100, cap - 1)
                 if all(gcd(a * (a + 2), s) == 1 for s in old)]
    old.append(p)

total_triggers = set()
total_censored = 0
for i, p in enumerate(primes):
    if not 7 <= p <= 47:
        continue
    q, r = primes[i + 1:i + 3]
    positive = double = excess = censored = 0
    triggers = set()
    for a in stages[p]:
        if gcd(a * (a + 2), p) == 1:
            continue
        ib = bisect_left(stages[q], a)
        ic = bisect_left(stages[r], a)
        if ib == len(stages[q]) or ic == len(stages[r]):
            censored += 1
            continue
        b, c = stages[q][ib], stages[r][ic]
        j1, j2 = b - a, c - b
        positive += 1
        double += int(j2 > 0)
        if j1 > q * q - p * p:
            triggers.add((p, a, b, c))
            excess += int(j2 > r * r - q * q)
    total_triggers.update(triggers)
    total_censored += censored
    print(p, positive, double, len(triggers), excess, censored)

assert len(total_triggers) == 13
assert total_censored == 3
for anchor, heads, expected in [
    (1097, (7, 11, 13), (1097, 1109, 1121)),
    (36161, (29, 31, 37), (36161, 36299, 36341)),
]:
    actual = []
    for head in heads:
        value = next(x for x in range(anchor, cap - 1)
                     if all(gcd(x, s) == 1 and gcd(x + 2, s) == 1
                            for s in primes if s < head))
        actual.append(value)
        assert stages[head][bisect_left(stages[head], anchor)] == value
    assert tuple(actual) == expected
    print("Independent minima PASS", anchor, actual)
assert 1099 == 7 * 157 and 1111 == 11 * 101
```

## Outcome and remaining question

Immediate strict decrease is false. The bounded primary test did not find
consecutive frontier-scale excesses; its small trigger set is too weak to
establish a law. No long-horizon or last-pair-specific compensation theorem
has been proved.

In the hypothetical last-pair universe, the staircase would have to stay
beyond the square frontier. Even ruling out consecutive excess jumps would
not alone force a crossing: a large reserve or later occasional jumps could
sustain the lead. A useful theorem would need a cumulative arithmetic bound
on the relevant front advances, with an initial condition and explicit horizon.
The telescoping formula for the total advance is not itself such a bound.

This audit does not introduce another candidate. It records the tested
statement, its limited evidence, and the exact shortcut that fails.
