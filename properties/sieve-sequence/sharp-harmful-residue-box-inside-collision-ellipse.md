# Sharp Harmful-Residue Box Inside The Collision Ellipse

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

The Pointwise Margin Insufficiency property proves that candidate #12's existing pointwise survival margin
is too weak for candidate #21's quadratic budget. This property computes the
exact stronger pointwise threshold.

The scalar energy is maximized when the two harmful residue deviations have
the same sign. The largest symmetric coordinate box contained strictly
inside the collision ellipse is smaller than the ordinary survival box by
the factor `sqrt((r-2)/r)`.

## Setup

Let `r>2` and let

```math
\delta_0,
\qquad
\delta_{-2}
```

be the centered 2-gap-start counts in the two harmful residue classes.
Define

```math
\mathcal Q_r(\delta_0,\delta_{-2})
=
\frac{r}{2(r-2)}
(\delta_0+\delta_{-2})^2
+
\frac12(\delta_0-\delta_{-2})^2.
```

Assume the symmetric pointwise bound

```math
|\delta_0|\le E,
\qquad
|\delta_{-2}|\le E.
```

## Exact Box Maximum

The quadratic form `mathcal Q_r` is convex. Its maximum on the square
`[-E,E]^2` is therefore attained at a vertex.

At a same-sign vertex,

```math
(\delta_0,\delta_{-2})=(E,E)
```

or `(-E,-E)`, so

```math
\mathcal Q_r
=
\frac{r}{2(r-2)}(2E)^2
=
\frac{2r}{r-2}E^2.
```

At an opposite-sign vertex,

```math
(\delta_0,\delta_{-2})=(E,-E)
```

or `(-E,E)`, so

```math
\mathcal Q_r
=
\frac12(2E)^2
=
2E^2.
```

Because `r/(r-2)>1`, the same-sign value is larger. Hence

```math
\boxed{
\max_{|\delta_0|,|\delta_{-2}|\le E}
\mathcal Q_r(\delta_0,\delta_{-2})
=
\frac{2r}{r-2}E^2.
}
```

The bound is sharp, with equality at both same-sign vertices.

## Sharp One-Layer Threshold

Let

```math
T=G\left(1-\frac2r\right)
```

be candidate #21's one-layer main term. Its scalar ellipse is

```math
\mathcal Q_r(\delta_0,\delta_{-2})
<
\frac{T^2}{2}.
```

The complete coordinate box lies strictly inside this ellipse exactly when

```math
\frac{2r}{r-2}E^2<\frac{T^2}{2}.
```

Equivalently,

```math
\boxed{
E
<
\frac T2
\sqrt{\frac{r-2}{r}}.
}
```

This threshold is sharp for a symmetric coordinatewise theorem. If equality
holds, the same-sign vertices lie on the ellipse. If `E` is larger, those
vertices lie outside it.

Candidate #12's existing one-filter survival margin is only

```math
E<\frac T2.
```

Since

```math
\sqrt{\frac{r-2}{r}}<1,
```

the collision-budget threshold is strictly stronger.

## Weighted Aggregate Consequence

At layer `i`, suppose

```math
|\delta_{i,0}|\le E_i,
\qquad
|\delta_{i,-2}|\le E_i.
```

Then

```math
\boxed{
\sum_iw_i
\left[
\frac{r_i}{2(r_i-2)}
(\delta_{i,0}+\delta_{i,-2})^2
+
\frac12(\delta_{i,0}-\delta_{i,-2})^2
\right]
\le
\sum_iw_i\frac{2r_i}{r_i-2}E_i^2.
}
```

Thus a sufficient aggregate candidate #12 theorem is any explicit bound

```math
\sum_iw_i\frac{2r_i}{r_i-2}E_i^2
\le
\mathcal B_{\mathrm{harm}}(Q)
```

that fits candidate #21 after the independent harmless-dispersion budget is
inserted.

## Boundary

The property computes the exact norm conversion; it does not prove that the
actual harmful residue deviations satisfy the required `E_i`.

It also shows why separate coordinatewise bounds may still be suboptimal. A
direct ellipse or covariance theorem can permit larger deviations in one
direction when the other direction is small. Nevertheless, this sharp box is
the correct benchmark for evaluating any pointwise residue-discrepancy
proposal.

## Validation

The four vertex values and threshold equivalence were checked with exact
rational arithmetic for:

```math
r\in\{5,7,11,13,17,19\},
```

and positive rational values

```math
E\in\left\{\frac12,1,\frac32,2,3\right\}.
```

These finite checks validate the arithmetic only.

## Related

- [Pointwise two-class margin does not imply the collision budget](
  pointwise-two-class-margin-does-not-imply-collision-budget.md
  )
- [Endpoint sampling and strike density recombine into harmful residues](
  endpoint-sampling-strike-density-harmful-residue-bridge.md
  )
- [Local pattern-residue balance](
  ../../candidates/local-pattern-residue-balance.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
