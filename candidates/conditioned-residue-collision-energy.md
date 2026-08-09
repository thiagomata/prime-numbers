# Conditioned Residue-Collision Energy

**Candidate hypothesis:** Unproved and potentially false.

**Collision reduction:** Mathematically proved.

**Conditional implication:** Mathematically proved.

**Empirical status:** BOUNDED FALSIFIER INCONCLUSIVE — exact conditioned-layer
search through prime heads `Q<=251` found no violation. This finite non-witness
does not support or refute the infinitely-many-heads hypothesis. The minimal
algebraic violating histograms are known, so further computation should seek
only those targeted witnesses rather than extend an undirected sweep.

## Purpose

An incoming prime `r` destroys 2-gaps whose starts occupy two particular
residue classes modulo `r`. Candidate #12 controls each residue class
pointwise. Candidate #19 avoids distribution estimates by bounding the
absolute capacity of the two harmful classes, but then requires a conditioned
population of order `Q^2/r`.

This candidate takes a third route. It bounds the second moment of the residue
histogram through an exact count of pairs of 2-gap starts whose difference is
divisible by `r`. If that collision count is near its uniform benchmark, only
a constant number of current 2-gaps is needed to force one survivor.

## Setup

Fix a future prime head `Q` and one conditioned layer with incoming prime
`r`, where

```math
5\le r<Q.
```

Let `S_r(W_Q)` be the set of complete 2-gap starts present immediately before
filter `r` in

```math
W_Q=[Q,Q^2),
```

and write

```math
N_r=|S_r(W_Q)|.
```

Define the ordered same-residue collision count

```math
C_r
=
\#\{
(x,y)\in S_r(W_Q)^2:
r\mid(x-y)
\}.
```

## Candidate Hypothesis

At every layer in the conditioned chain, suppose

```math
\boxed{
C_r
\le
N_r+\frac{N_r^2}{r}
}
```

and

```math
\boxed{
N_r>\frac{2r^2}{(r-2)^2}.
}
```

The integer population condition is

```math
N_r\ge
\begin{cases}
6,&r=5,\\
4,&r=7,\\
3,&r\ge11.
\end{cases}
```

The hereditary candidate asks for both inequalities through every conditioned
layer for infinitely many future heads `Q`.

## Why The Collision Scale Is Natural

The collision count always contains the `N_r` diagonal pairs `(x,x)`. If the
off-diagonal starts behaved uniformly among the `r` residue classes, their
same-class contribution would have scale `N_r^2/r`. The candidate uses

```math
N_r+\frac{N_r^2}{r}
```

as a deterministic upper benchmark. This heuristic explains the scale but is
not a proof of the inequality.

After filters `2` and `3`, every 2-gap start is `5 modulo 6`. The proved
autocorrelation identity is

```math
C_r
=
N_r
+2
\sum_{1\le h\le
\left\lfloor(Q^2-Q-3)/(6r)\right\rfloor}
A_r(6rh),
```

where

```math
A_r(d)
=
\#\{
x:
x,x+2,x+d,x+d+2
\text{ survive in }W_Q
\}.
```

Thus the candidate can be attacked through upper bounds for explicit
four-point patterns.

## Exact Minimal Falsifiers

For residue multiplicities `(c_a)`, the exact identity

```math
C_r-N_r
=
2\sum_a\binom{c_a}{2}
```

shows that the collision inequality permits at most `N_r^2/(2r)` unordered
same-class pairs. At the candidate's smallest allowed populations, the first
violating histograms are:

| `(r,N_r)` | Minimal violating nonzero multiplicities | Pair count | Allowed pair count |
|-----------|-------------------------------------------|------------|--------------------|
| `(5,6)` | `3+2+1` | `4` | `18/5` |
| `(7,4)` | `2+2` | `2` | `8/7` |
| `r>=11, N_r=3` | `2+1` | `1` | `9/(2r)<1` |

These are exact algebraic countermodels to the collision inequality at the
minimal populations. Basic spacing does not exclude them: starts in one
residue class may be separated by multiples of `6r`. They are not candidate
counterexamples until the complete histogram is realized by an actual
conditioned square-window population.

A dependency-free exact search recomputed those populations and histograms for
every prime head through `Q<=251` and found no violating layer. Because the
candidate asks for successful chains at infinitely many heads, neither this
finite agreement nor any isolated future failure decides its main quantifier.

## Why The Candidate Is Sufficient

The proved collision-energy lemma says that survival follows from

```math
C_r
<
N_r^2
\left(
\frac12-\frac1r+\frac{2}{r^2}
\right).
```

Under the candidate collision bound, it is enough that

```math
N_r+\frac{N_r^2}{r}
<
N_r^2
\left(
\frac12-\frac1r+\frac{2}{r^2}
\right).
```

Because `N_r>0`, divide by `N_r` and rearrange:

```math
\begin{aligned}
\frac1{N_r}
&<
\left(
\frac12-\frac1r+\frac{2}{r^2}
\right)-\frac1r
&&[\text{Rearrangement}]\\
&=
\frac12-\frac2r+\frac{2}{r^2}\\
&=
\frac{(r-2)^2}{2r^2}.
&&[\text{Factorization}]
\end{aligned}
```

This is exactly

```math
N_r>\frac{2r^2}{(r-2)^2},
```

the candidate's population condition. Therefore the collision-energy
criterion holds, the harmful count is strictly less than `N_r`, and at least
one complete 2-gap survives filter `r`.

Because both premises are evaluated on the actual population remaining after
all preceding filters, the implication composes through the finite chain.
After the last filter below `Q`, a surviving complete 2-gap in `[Q,Q^2)` is
square-safe. Infinitely many successful heads would therefore give infinitely
many twin-prime certificates.

## Relation To Candidates #12, #14, #19, And #22

- **#12, pointwise residue balance:** asks for `L-infinity` control of residue
  counts. Candidate #20 asks for an `L2`-type pair count and tolerates some
  uneven individual classes, provided the total collision energy is small.
- **#14, hereditary shot spacing:** uses a close cluster to beat a locally
  sparse shot train. Candidate #20 does not require a close pair; it prevents
  excessive concentration modulo the incoming prime.
- **#19, sixfold harmful capacity:** uses no pseudorandomness and has a fully
  proved absolute destruction cap, but needs order `Q^2/r` gaps. Candidate #20
  needs only `6`, `4`, or `3` gaps, at the price of an unproved relative
  four-point correlation bound.
- **#22, harmless-class collision energy:** removes the two harmful classes,
  recenters on the `r-2` survivor classes, and asks only for their energy
  `U_r`. The exact relation is

  ```math
  V_r
  =
  U_r
  +
  \frac{r}{2(r-2)}b_r^2
  +
  \frac12\Delta_r^2.
  ```

  Thus #20 controls all three components at once, while #22 separates the
  remaining distributional term from total harmful excess and left/right
  imbalance.

These are real tradeoffs. Candidate #20 should not be called stronger merely
because its population floor is smaller; its collision premise contains the
new difficulty. For current proof work, #20 is a useful pointwise testbed, but
#22's harmless energy and candidate #21's weighted aggregate are the more
precise primary targets.

Property #83 gives candidate #20 a direct localized role in candidate #24.
For one incoming prime, let `V_r=C_r-N_r^2/r` be the residue energy of the
old-period start histogram. If `B_j` is the centered harmful excess in old-
period copy block `j`, then

```math
\sum_{j=0}^{r-1}B_j^2\le4V_r
```

and every `k` consecutive complete blocks satisfy

```math
\left|\sum_{j\in J}B_j\right|^2\le4kV_r.
```

Thus a relative collision theorem for #20 controls #24's harmful excess on
the complete old-period blocks inside the square window. It still leaves the
two partial old-period boundary fragments, and late layers may contain no
complete old-period block at all. The bridge is proved; the collision and
short-boundary estimates are not.

## Algebraic Proof Program

The most concrete route is:

1. use the autocorrelation identity to replace `C_r` by the sum of the
   four-point counts `A_r(6rh)`;
2. derive an upper-bound-sieve estimate for that sum in the conditioned window;
3. normalize it by an independently proved lower bound for `N_r`;
4. verify that the resulting constants imply
   `C_r<=N_r+N_r^2/r`.

An acceptable weaker result may replace the coefficient `1` by `lambda_r`:

```math
C_r\le N_r+\lambda_r\frac{N_r^2}{r}.
```

The exact population condition then becomes

```math
\frac1{N_r}
<
\frac12-\frac{1+\lambda_r}{r}+\frac{2}{r^2}.
```

This formula makes the constant budget explicit and allows partial algebraic
progress without changing the survival argument.

## Limitation

No relative collision bound is currently proved for conditioned square
windows. Standard upper-bound sieves naturally estimate the four-point
patterns in terms of window length and local density. The candidate instead
needs a bound in terms of the actual, unknown `N_r`.

Converting an absolute four-point upper bound into
`N_r+N_r^2/r` may require a lower bound for `N_r` strong enough to encounter
the parity problem again. This normalization step is the main risk. The
candidate is valuable only if the four-point upper correlation can be related
to `N_r` without already assuming the final short-window positivity that the
argument is meant to prove.

## Established Inputs

- [Two-class survival from residue collision energy](
  ../properties/sieve-sequence/two-class-survival-from-collision-energy.md
  )
- [Orthogonal residue-energy decomposition after a two-class filter](
  ../properties/sieve-sequence/orthogonal-residue-energy-decomposition-after-two-class-filter.md
  )
- [Harmful residue capacity after filter three](
  ../properties/sieve-sequence/harmful-residue-capacity-after-filter-three.md
  )
- [Square-safe certification](
  ../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md
  )
- [Copy-block harmful excess is controlled by residue energy](
  ../properties/sieve-sequence/copy-block-harmful-excess-controlled-by-residue-energy.md
  )
