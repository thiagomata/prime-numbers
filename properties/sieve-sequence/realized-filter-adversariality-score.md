# Realized Filter Adversariality Score

**Status:** Mathematically proved algebraic diagnostic. This note does not
claim Stainless verification, filter intent, or deterministic randomness.

## Purpose and Setup

The raw fraction of locally destroyed 2-gaps does not place a random filter at
the fixed midpoint `1/2`: its natural benchmark depends on the filter prime.
This note declares a continuous piecewise-linear normalization with the
requested anchors:

- `0`: no gap in the typed local population is destroyed;
- `1/2`: destruction matches the random-residue/complete-copy benchmark;
- `1`: every gap in the typed local population is destroyed.

This normalization is useful but not unique. It measures a realized outcome,
not friendly or adversarial intent.

Let `p>2` be prime. For one explicitly chosen local pre-filter population, let

```math
L>0,
\qquad
0\le K\le L
```

be respectively the number of 2-gaps before filter `p` and the number destroyed
by that filter. Define

```math
f=\frac KL,
\qquad
d_p=\frac2p.
```

The score is undefined when `L=0`. An empty population is neither assigned a
friendly score nor an adversarial score.

## Why the Benchmark Is `2/p`

The benchmark has two compatible meanings.

First, choose one forbidden residue class uniformly modulo `p`. The two
endpoints of a 2-gap occupy distinct residue classes because `p>2`. The chosen
class hits one endpoint with probability

```math
d_p=\frac2p.
```

Second, follow one inherited 2-gap through its `p` translated copies in a
complete copy block. One copy places its left endpoint in the forbidden class
and a different copy places its right endpoint there. Exactly two of the `p`
copies are destroyed, again giving `2/p`.

The second statement is an exact complete-copy/global proportion. It does not
assert that a shorter deterministic local window has the same proportion.

## Definition

Define the realized filter adversariality score by

```math
C_p(f)=
\begin{cases}
\dfrac{f}{2d_p},&0\le f\le d_p,\\[6pt]
\dfrac12+\dfrac{f-d_p}{2(1-d_p)},&d_p\le f\le1.
\end{cases}
```

The first branch stretches destruction below the benchmark across `[0,1/2]`.
The second branch stretches destruction above the benchmark across `[1/2,1]`.

## Anchors, Continuity, and Monotonicity

The three anchors follow directly:

```math
\begin{aligned}
C_p(0)&=0,\\
C_p(d_p)&=\frac12,\\
C_p(1)&=
\frac12+\frac{1-d_p}{2(1-d_p)}
=1.
\end{aligned}
```

Both branches equal `1/2` at `f=d_p`, so the score is continuous. Their slopes
are

```math
\frac1{2d_p}>0,
\qquad
\frac1{2(1-d_p)}>0,
```

because `0<d_p<1`. Therefore `C_p` is strictly increasing on `[0,1]`.

For a finite integer population, the value `K/L=d_p` may be unattainable.
Score `1/2` remains the declared benchmark anchor even when no integer `K`
lands exactly on it.

The score regions mean only

```math
\begin{aligned}
C_p(f)<\frac12&\iff f<d_p,\\
C_p(f)=\frac12&\iff f=d_p,\\
C_p(f)>\frac12&\iff f>d_p.
\end{aligned}
```

They mean below, equal to, or above the benchmark destruction rate. They do not
prove friendly intent, random behavior, or extinction.

## Exact Survival Limit

Strict monotonicity and the endpoint anchor give

```math
\begin{aligned}
L-K>0
&\iff K<L,\\
&\iff \frac KL<1,\\
&\iff C_p(K/L)<1.
\end{aligned}
```

Thus the exact limit is

```math
C_p<1.
```

Score `1` is local extinction. Every realized score strictly below `1` leaves
at least one member of the chosen population alive. This is an outcome
equivalence, not a recurrence theorem.

## Exact Excess-Removal Allowance

Suppose an integer `x` appears in the one-sided bound

```math
K\le d_pL+x.
```

This bound alone forces survival exactly while its right side remains below
`L`:

```math
d_pL+x<L
\iff
x<(1-d_p)L.
```

The largest integer satisfying that strict inequality is

```math
x_{max}
=
\left\lceil(1-d_p)L\right\rceil-1
=
\left\lceil\left(1-\frac2p\right)L\right\rceil-1.
```

This threshold is necessary and sufficient relative to only the assumptions
`0<=K<=L` and `K<=d_pL+x`. At the next integer value, the bound no longer
excludes `K=L`. A larger allowance does not claim that the actual sieve causes
extinction; it means this bound alone no longer guarantees survival.

## Turning a Capacity Theorem into a Score Bound

Let `H>=0` be a proved upper bound on destruction for the same typed population
counted by `L`:

```math
K\le H.
```

Then

```math
\frac KL
\le
\min\!\left(1,\frac HL\right).
```

Monotonicity gives the rigorous adversariality bound

```math
C_p(K/L)
\le
C_p\!\left(
\min\!\left(1,\frac HL\right)
\right).
```

The right side is a proved upper bound on the realized score. It is not an
observed score or an estimate of typical behavior. If `H<L`, this upper bound
is strictly below `1`, so survival is guaranteed even under worst-case use of
the proved capacity.

## Full-Window and Annular Instances

For consecutive primes `p<q` with `p>=5`, use the actual full square-safe
pre-filter counts `L(p,q),K(p,q)`. Because filter `3` is already installed,
endpoint isolation and the exact accepted-strike count give

```math
K(p,q)\le A(p,q).
```

Therefore

```math
C_p(K(p,q)/L(p,q))
\le
C_p\!\left(
\min\!\left(1,\frac{A(p,q)}{L(p,q)}\right)
\right).
```

For consecutive primes `p<q` with `p>=5`, the refined annular population
inherits the preconditions of the Danger-Annulus Decomposition property. Require `L_D(p,q)>0` so that its
score is defined. The Danger-Annulus Decomposition property gives

```math
K_D(p,q)
\le A(p,q)-1
\le R_V(p,q)-1.
```

Hence

```math
C_p(K_D(p,q)/L_D(p,q))
\le
C_p\!\left(
\min\!\left(1,\frac{A(p,q)-1}{L_D(p,q)}\right)
\right).
```

The exact annular survival condition remains `K_D(p,q)<L_D(p,q)`. The
exact-accepted-capacity sufficient condition is

```math
L_D(p,q)>A(p,q)-1,
```

with the weaker raw sufficient condition

```math
L_D(p,q)>R_V(p,q)-1.
```

Without a positive lower bound for `L_D`, these formulas do not prove an
annular score below `1`.

## Observed, Benchmark, and Proved Quantities

These three uses must remain separate:

- observed `K,L` determine the realized fraction `K/L` and score `C_p(K/L)`;
- `d_p=2/p` is exact over complete copies and is the random-residue model
  expectation, but need not equal a local observed fraction;
- a capacity `H` supplies a rigorous upper bound on the score, but does not
  predict the realized score.

The score cannot manufacture a missing population lower bound. It also does
not prove deterministic random-like transference, annular abundance,
recurrence, or infinitely many surviving heads.

## Finite Full-Window Evidence

**Evidence status:** The numbers in this section are finite observations from
measured full square-safe windows. They are not annular results, asymptotic or
recurrence theorems, or evidence that the deterministic filters are random.

The source files are
[the dense measurements](../../data/candidates/window-measurements.csv) and
[the sparse measurements](../../data/candidates/window-measurements-sparse.csv).
Together they contain 192 data rows. After excluding the two `p=3` rows, 190
clean rows remain. Merging by unique `(p,q)` finds four duplicate keys:
`(5,7)`, `(7,11)`, `(11,13)`, and `(557,563)`. The duplicates agree in
`G_local`, `destroyed`, `destruction_rate`, and `A_worst`, leaving 186 unique
clean transitions.

For these `p>=5` transitions, the CSV column `A_worst` equals the exact accepted
strike count `A(p,q)`. Define the observed score and the proved capacity ceiling
by

```math
C_{obs}
=
C_p\!\left(\frac{\mathtt{destroyed}}{\mathtt{G\_local}}\right),
\qquad
C_{cap}
=
C_p\!\left(
\min\!\left(1,\frac{\mathtt{A\_worst}}{\mathtt{G\_local}}\right)
\right).
```

The realized full-window scores are:

| Statistic | `C_obs` |
|---|---:|
| count | 186 |
| minimum | 0 |
| median | 0 |
| unweighted mean | 0.044177363545902307 |
| maximum | 0.47727272727272724 |
| zero-score transitions | 95 |
| below / equal to / above `1/2` | 186 / 0 / 0 |

The proved full-window capacity ceilings are:

| Statistic | `C_cap` |
|---|---:|
| count | 186 |
| minimum | 0.006784399338495748 |
| median | 0.1285745802948713 |
| unweighted mean | 0.16908125524560394 |
| maximum | 0.5545454545454546 |
| below / equal to / above `1/2` | 177 / 1 / 8 |
| below `1` | 186 |

The midpoint classifications use exact integer comparisons, not rounded
scores. For observations, compare `pK` with `2L`; the counts below, equal to,
and above are `186 / 0 / 0`. For capacity ceilings, compare `pA` with `2L`;
the counts are `177 / 1 / 8`. The unique capacity equality occurs at
`(p,q)=(17,19)`, where `L=17`, `A=2`, and `pA=2L=34`.

The closest observed transition to the random/global benchmark, and the
maximum observed score, is `(p,q)=(7,11)`:

```math
L=11,
\qquad
K=3,
\qquad
A=4,
```

```math
\frac{K/L}{2/p}
=
\frac{21}{22},
\qquad
C_{obs}
=
\frac{21}{44}.
```

The same transition has the maximum capacity ceiling

```math
C_{cap}=\frac{61}{110}.
```

Thus every measured observed score lies below `1/2`: these finite full windows
were less destructive than the benchmark rate. This does not prove random-like
transference or friendly intent. The capacity ceiling is a rigorous per-row
worst-case bound, not typical behavior. Its value may exceed `1/2` while the
realized score remains below `1/2`.

All 186 capacity ceilings are below `1` because `A(p,q)<L(p,q)` in every
measured clean full window. This is the already-recorded finite full-window
local-surplus certificate expressed on the new scale, not a new abundance
theorem.

Neither CSV contains `L_D,K_D`. Consequently, no observed annular score or
numeric annular capacity ceiling is reported.

## Related

- [Random-like merge survival](../../candidates/random-like-merge-survival.md)
- [Local surplus](../../candidates/local-surplus.md)
- [Incremental danger-annulus decomposition](incremental-danger-annulus-decomposition.md)
- [Exact accepted local filter strikes](exact-accepted-local-filter-strikes.md)
- [2-gap isolation after filter 3](two-gap-isolation-after-filter-three.md)
