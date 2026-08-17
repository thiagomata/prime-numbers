# Safe-Zone Exhaustion Tight Bound

**Candidate hypothesis:** Unproved.

**Empirical status:** The implemented estimate had zero overshoot violations at
every available ground-truth point reported for prime heads from `13` through
`131`. This is finite evidence, not a proof.

**Stainless status:** Not verified.

## Setup

Let `p` be a prime sieve-sequence head and let

```math
M=\prod_{\substack{r<p\\r\text{ prime}}}r.
```

Define the number of stage-`p` survivors strictly inside the square-safe window
by

```math
A(p)=\#\{n\in[p,p^2):\gcd(n,M)=1\}.
```

The practical density estimate is

```math
\widehat A(p)=(p^2-p)\prod_{\substack{r<p\\r\text{ prime}}}\left(1-\frac1r\right).
```

## Candidate Hypothesis

For every prime `p >= 13`,

```math
A(p)\ge\widehat A(p).
```

Equivalently, the density estimate never places the square-safe exhaustion
boundary to the right of the true boundary. The lower endpoint `13` is part of
the proposed statement, not a consequence of the finite checks. If a later
audit changes the intended universal range, this hypothesis must be revised
explicitly.

## Why It Matters

Every stage-`p` survivor below `p^2` is prime. Thus `A(p)` is the exact number
of certified-prime survivors before acceptance and certified primality can
first diverge.

The known universal lower bound grows only linearly in `p`. By contrast,
`\widehat A(p)` has the practical scale `p^2/log p` and closely tracks the
boundary drawn in the sieve-sequence visualizations. Proving the candidate
would replace a useful empirical curve with a universal lower certificate at
that sharper scale.

This candidate does not assert the existence of a 2-gap, local 2-gap survival,
or infinitely many twin primes. It concerns the total number of accepted values
inside one square-safe interval.

## Evidence Boundary

The maintained source reports ground-truth comparisons for prime heads from
`13` through `131` and no implemented overshoot violations in that available
range. It also reports that the ratio between the observed count and the
estimate stays close to `1` and tightens over the measured data.

Those observations are finite and dataset-dependent. They do not establish the
quantifier over every prime `p >= 13`, an asymptotic error term, or monotone
improvement of the ratio.

## Missing Theorem

Mertens' product theorem controls

```math
\prod_{\substack{r<p\\r\text{ prime}}}\left(1-\frac1r\right),
```

which describes a global or full-period density. The candidate needs a lower
bound for rough numbers in the particular short interval `[p,p^2)`. That
interval is a vanishing fraction of the primorial period as `p` grows, so the
global density cannot simply be substituted for its local count.

The missing input is therefore a short-interval localization or
equidistribution theorem strong enough to control `A(p)` at the scale of
`\widehat A(p)`.

## Failed Paths

### Global Density Substitution

Explicit Mertens-product bounds, including the Rosser-Schoenfeld bounds cited in
the source note, control the product itself but do not turn its global average
into a lower bound on `[p,p^2)`. The approach fails because it omits the required
short-interval localization step.

Retry this route only with an independent theorem that transfers the
rough-number density into this specific interval with an error smaller than the
proposed main term.

### Naive Legendre/Möbius Inclusion-Exclusion

The exact identity

```math
\Phi(n,p)=\sum_{d\mid M}\mu(d)\left\lfloor\frac nd\right\rfloor
```

leads under termwise absolute estimation to an error bounded by the number of
squarefree divisors of `M`, namely `2^k` when `k` primes lie below `p`. In this
application that error overwhelms the main term and makes the resulting lower
bound vacuous.

Retry this route only with cancellation or structured remainder control that
replaces the absolute `2^k` error.

## Known Proved Baseline

Two proved facts remain separate from this candidate:

1. The first composite stage-`p` survivor is exactly `p^2`.
2. For every prime `p >= 11`, the cited Schroeder rough-number bound gives

```math
A(p)\ge\left\lfloor\frac{2(p^2-1)}p\right\rfloor.
```

The first fact identifies the square-safe boundary. The second supplies a
universal but much looser lower count. Neither proves the tight candidate.

## Related

- [Safe-Zone Exhaustion Curve](../properties/sieve-sequence/safe-zone-exhaustion-curve.md)
- [Safe-Window 2-Gaps Certify Twin Primes](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)
- [Visualization Figure Notes](../presentations/sieve-sequence-visualization/figures/README.md)
