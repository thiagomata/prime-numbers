# Endpoint-Observable Joint Capacity Envelope

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

Candidate #13 needs two endpoint observables: total endpoint hits and
left-versus-right imbalance. Treating their errors separately loses the fact
that both arise from the same two endpoint-class counts.

This property solves the exact joint finite-population extremal problem. The
maximum occurs at a boundary pattern that concentrates as many endpoint hits
as possible in one orientation. The result is the sharp conclusion available
from endpoint isolation and class capacities alone; any smaller bound must
use arithmetic information about which residue class the filter actually
hits.

## Setup

Let an accepted-anchor population contain:

- `G` left endpoints of isolated complete 2-gaps;
- `G` right endpoints;
- `A-2G` non-endpoints.

Assume

```math
A>0,
\qquad
0\le2G\le A.
```

Let a filter hit exactly `H` anchors, where `0<=H<=A`. Write

```math
k_L
```

and

```math
k_R
```

for its left- and right-endpoint hit counts. Define

```math
\mu=\frac{GH}{A},
```

```math
e_L=k_L-\mu,
\qquad
e_R=k_R-\mu.
```

Property #34 gives

```math
H\beta=e_L+e_R,
\qquad
\Delta=e_L-e_R.
```

For an incoming prime `r>2`, define the exact scalar energy

```math
\mathcal Q_r(e_L,e_R)
=
\frac{r}{2(r-2)}(e_L+e_R)^2
+
\frac12(e_L-e_R)^2.
```

## Exact Feasible Polygon

Endpoint isolation makes the left endpoints, right endpoints, and
non-endpoints disjoint. Therefore

```math
0\le k_L\le G,
\qquad
0\le k_R\le G,
```

and the number of non-endpoint hits satisfies

```math
0\le H-k_L-k_R\le A-2G.
```

Put

```math
s=k_L+k_R,
\qquad
d=k_L-k_R.
```

The feasible total endpoint-hit interval is

```math
\boxed{
\ell\le s\le u,
}
```

where

```math
\ell=\max(0,H+2G-A),
\qquad
u=\min(H,2G).
```

For fixed `s`, the square constraints on `(k_L,k_R)` give

```math
\boxed{
|d|\le\min(s,2G-s).
}
```

Both bounds are attained by concentrating the endpoint hits as far as
possible into one orientation.

## Exact Maximum

In `(s,d)` coordinates,

```math
\mathcal Q_r
=
\frac{r}{2(r-2)}
\left(
s-\frac{2GH}{A}
\right)^2
+
\frac12d^2.
```

For fixed `s`, the coefficient of `d^2` is positive, so the maximum uses

```math
|d|=\min(s,2G-s).
```

Define

```math
F(s)
=
\frac{r}{2(r-2)}
\left(
s-\frac{2GH}{A}
\right)^2
+
\frac12\min(s,2G-s)^2.
```

On each of the intervals `[0,G]` and `[G,2G]`, `F` is a convex quadratic.
Its maximum on `[ell,u]` is therefore attained at `ell`, at `u`, or at the
joining point `G` when that point is feasible.

Let

```math
\mathcal S
=
\{\ell,u\}
\cup
\left(
\{G\}\text{ if }\ell\le G\le u
\right).
```

Then the sharp joint capacity envelope is

```math
\boxed{
\max_{\text{feasible }(k_L,k_R)}
\mathcal Q_r(e_L,e_R)
=
\max_{s\in\mathcal S}
\left[
\frac{r}{2(r-2)}
\left(
s-\frac{2GH}{A}
\right)^2
+
\frac12\min(s,2G-s)^2
\right].
}
```

The formula applies to integer counts as written. The values `ell`, `u`, and
`G` are integers, and the extremal orientation counts realizing
`|d|=min(s,2G-s)` are integral.

## Interpretation Of The Vertices

- `s=ell` minimizes endpoint hits by placing as many filter hits as possible
  on non-endpoints.
- `s=u` maximizes total endpoint hits.
- `s=G`, when feasible, fills one endpoint orientation as much as possible
  while maximizing `|d|`.

At every tested vertex, the worst imbalance places all feasible endpoint hits
first into one orientation. Endpoint isolation alone does not prefer left
over right and supplies no cancellation between them.

## Relation To Separate Sampling Bounds

If candidate #13 supplies the separate pointwise bounds

```math
|\beta|\le\eta,
\qquad
|\Delta|\le H\eta,
```

then

```math
\mathcal Q_r
\le
H^2\eta^2
\left(
\frac{r}{2(r-2)}+\frac12
\right)
=
\boxed{
H^2\eta^2\frac{r-1}{r-2}.
}
```

The joint capacity formula is different: it is sharp without choosing
`eta`, but may be much larger because it permits adversarial concentration
on endpoint classes. Comparing the two formulas identifies exactly how much
residue-sampling information an `eta` theorem must add beyond population
capacity.

## Boundary

This property does not prove candidate #13. It proves the best possible
one-layer bound using only:

1. the three class sizes `G,G,A-2G`;
2. the total number `H` of hits;
3. endpoint isolation.

Any improvement must rule out one or more extremal vertices for the actual
incoming residue class. That requires arithmetic correlation information,
not another rearrangement of `K`, `beta`, or `Delta`.

## Validation

The formula was checked by exhaustive exact rational enumeration for:

```math
1\le A\le17,
\qquad
0\le2G\le A,
\qquad
0\le H\le A,
```

and

```math
r\in\{5,7,11\}.
```

For every admissible parameter tuple, the maximum over all integer
`(k_L,k_R)` equaled the displayed vertex formula. This finite validation
checks the algebra; the proof is the convexity argument above.

## Related

- [Isolation of 2-gaps after filtering by 3](
  two-gap-isolation-after-filter-three.md
  )
- [Two endpoint observables separate harmful excess and imbalance](
  two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Weighted composition of endpoint and strike-density errors](
  weighted-scalar-error-composition.md
  )
- [Uniform local observable sampling](
  ../../candidates/uniform-local-observable-sampling.md
  )
