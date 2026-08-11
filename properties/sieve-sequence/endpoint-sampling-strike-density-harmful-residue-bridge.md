# Endpoint Sampling And Strike Density Recombine Into Harmful Residues

**Status:** Mathematically proved exact identity. Stainless verification is
not claimed.

## Meaning

Candidates #13 and #23 split the harmful-excess error into endpoint sampling
and accepted-anchor strike density. The split is useful for assigning
responsibilities, but the two errors are not intrinsically separate.

When recombined, they are exactly the centered counts of 2-gap starts in the
two harmful residue classes. This gives a more direct scalar target for
candidate #21: control those two residue counts jointly, without first
proving separate sampling and strike-density theorems and recombining them by
Minkowski.

## Setup

Let `S` be a set of `G` isolated complete 2-gap starts. For an incoming prime
`r>2`, define

```math
k_L
=
\#\{x\in S:r\mid x\},
```

```math
k_R
=
\#\{x\in S:r\mid x+2\}.
```

Thus `k_L` and `k_R` are the counts in start-residue classes `0` and `-2`
modulo `r`.

Let `A` be the accepted-anchor population and `H` the number of anchors hit
by the filter. Define

```math
\varepsilon=\frac HA-\frac1r,
```

and, when `H>0`,

```math
\beta
=
\frac{k_L+k_R}{H}
-
\frac{2G}{A}.
```

Put

```math
e_L=k_L-\frac{GH}{A},
\qquad
e_R=k_R-\frac{GH}{A}.
```

The Orthogonal Residue-Energy Split property gives

```math
H\beta=e_L+e_R,
\qquad
\Delta=e_L-e_R,
```

where `Delta=k_L-k_R`.

## Harmful Residue Deviations

Center the two start-residue counts at their uniform residue mean:

```math
\delta_0=k_L-\frac Gr,
\qquad
\delta_{-2}=k_R-\frac Gr.
```

Since

```math
\frac{GH}{A}
=
\frac Gr+G\varepsilon,
```

we obtain

```math
\boxed{
e_L=\delta_0-G\varepsilon,
\qquad
e_R=\delta_{-2}-G\varepsilon.
}
```

Taking the sum and difference gives

```math
\boxed{
H\beta
=
\delta_0+\delta_{-2}-2G\varepsilon,
}
```

```math
\boxed{
\Delta
=
\delta_0-\delta_{-2}.
}
```

## Exact Recombination

The harmful excess is

```math
b
=
k_L+k_R-\frac{2G}{r}.
```

Therefore

```math
\boxed{
b=\delta_0+\delta_{-2}.
}
```

Using the preceding endpoint-sampling identity,

```math
\boxed{
b=H\beta+2G\varepsilon.
}
```

Thus candidate #13's unsigned endpoint error and candidate #23's strike
density error are exactly a decomposition of the sum of the two harmful
residue deviations. The signed endpoint error is already their difference.

## Direct Joint Scalar Energy

Candidate #21's two scalar terms at this layer are

```math
\frac{r}{2(r-2)}b^2+\frac12\Delta^2.
```

In harmful-residue coordinates this is exactly

```math
\boxed{
\frac{r}{2(r-2)}
\left(
\delta_0+\delta_{-2}
\right)^2
+
\frac12
\left(
\delta_0-\delta_{-2}
\right)^2.
}
```

This is the same two-dimensional quadratic form as the Joint Capacity Envelope property, but centered
at the natural residue mean `G/r` rather than the conditional sampling mean
`GH/A`.

## Consequence For Candidate Strategy

There are now two valid proof interfaces:

1. **Separated interface:** bound `beta` through candidate #13, bound
   `epsilon` through candidate #23, and combine them using the Weighted Error Composition property.
2. **Direct interface:** jointly bound `delta_0` and `delta_(-2)`, the two
   harmful residue deviations of the 2-gap-start population.

The direct interface can be strictly sharper because it retains correlation
between endpoint sampling and strike density. It is the minimal
two-harmful-class specialization of candidate #12; it does not require
uniformity in every residue class or for every gap word.

This property does not prove either interface. It shows that after the
separate generic algebraic audits of #13 and #23 reach distribution
boundaries, the direct two-class residue theorem is the natural surviving
scalar target.

## Zero-Hit Case

The harmful-residue deviations and direct energy remain defined when `H=0`.
In that case `beta` need not be defined, but

```math
k_L=k_R=0,
\qquad
\delta_0=\delta_{-2}=-\frac Gr,
```

and the direct identities still hold. Thus the direct interface is
division-free.

## Validation

The identities were checked with exact rational arithmetic for all

```math
1\le A\le15,
\qquad
0\le2G\le A,
\qquad
0\le H\le A,
```

all capacity-feasible integer `(k_L,k_R)`, and

```math
r\in\{5,7,11\}.
```

The checks validate the algebra only.

## Related

- [Two endpoint observables separate harmful excess and imbalance](
  two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Weighted composition of endpoint and strike-density errors](
  weighted-scalar-error-composition.md
  )
- [Orthogonal residue-energy decomposition after a two-class filter](
  orthogonal-residue-energy-decomposition-after-two-class-filter.md
  )
- [Uniform local observable sampling](
  ../../candidates/uniform-local-observable-sampling.md
  )
- [Local pattern-residue balance](
  ../../candidates/local-pattern-residue-balance.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
