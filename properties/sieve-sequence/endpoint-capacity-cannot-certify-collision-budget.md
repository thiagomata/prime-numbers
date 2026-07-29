# Endpoint Capacity Cannot Certify The Collision Budget

**Status:** Mathematically proved logical insufficiency result. Stainless
verification is not claimed.

## Meaning

Endpoint isolation and population capacities allow a filter to hit every
2-gap in the same endpoint orientation. In that admissible abstract
configuration, the signed-imbalance energy alone exceeds candidate #21's
entire one-layer survival allowance.

Therefore no theorem using only the class sizes and capacity constraints from
property #56 can prove candidate #21. A successful candidate #13 theorem must
add arithmetic information that excludes such endpoint concentration.

This does not claim that every actual sieve layer realizes the extremal
configuration.

## One-Layer Configuration

Fix an incoming prime

```math
r>2
```

and a positive number `G` of isolated complete 2-gaps. Let the anchor
population have `G` left endpoints, `G` right endpoints, and any nonnegative
number of non-endpoints:

```math
A\ge2G.
```

Let the filter hit exactly

```math
H=G
```

anchors, all of them left endpoints:

```math
k_L=G,
\qquad
k_R=0.
```

This satisfies property #56's complete capacity constraints:

```math
0\le k_L,k_R\le G,
```

```math
0\le H-k_L-k_R=0\le A-2G.
```

The total destruction and signed imbalance are

```math
K=G,
\qquad
\Delta=G.
```

Thus every one of the `G` gaps is destroyed.

## Candidate #21 Comparison

For a one-layer chain, candidate #21 has

```math
W=1
```

and expected surviving main term

```math
T=G\left(1-\frac2r\right).
```

Its complete second-moment allowance is

```math
\frac{T^2}{2W}
=
\frac{G^2}{2}
\left(1-\frac2r\right)^2.
```

The orthogonal residue-energy decomposition contains the nonnegative signed
imbalance contribution

```math
\frac12\Delta^2=\frac{G^2}{2}.
```

Since `r>2`,

```math
0<1-\frac2r<1,
```

so

```math
\boxed{
\frac12\Delta^2
=
\frac{G^2}{2}
>
\frac{G^2}{2}
\left(1-\frac2r\right)^2
=
\frac{T^2}{2W}.
}
```

The imbalance term alone exceeds the entire candidate #21 allowance, before
the harmful-excess and harmless-dispersion terms are added.

## Consequence

The capacity premises admit both:

- representative endpoint sampling;
- complete concentration on one endpoint orientation.

They cannot distinguish survival from total destruction. Hence the sharp
capacity envelope in property #56 is a boundary theorem, not a route to the
desired collision budget.

Retrying a capacity-only proof is justified only after adding a new premise
that forbids or quantitatively suppresses the concentrated vertex. Examples
include:

1. a residue-correlation bound for left and right endpoint sets;
2. a joint mean-square estimate for their centered residue counts;
3. averaging over incoming primes or future heads with a proved cancellation
   law.

## Validation

The strict inequality was checked exactly for positive integer `G<=20` and
primes

```math
r\in\{3,5,7,11,13\}.
```

The finite checks validate arithmetic only; the universal proof is the
displayed inequality `0<1-2/r<1`.

## Related

- [Endpoint-observable joint capacity envelope](
  endpoint-observable-joint-capacity-envelope.md
  )
- [Orthogonal residue-energy decomposition after a two-class filter](
  orthogonal-residue-energy-decomposition-after-two-class-filter.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
- [Uniform local observable sampling](
  ../../candidates/uniform-local-observable-sampling.md
  )
