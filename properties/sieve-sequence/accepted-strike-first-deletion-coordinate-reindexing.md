# Accepted-Strike First-Deletion Coordinate Reindexing

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

The First-Deletion Variance Identity property expresses accepted-strike energy as population times a Gram
trace minus pairwise variance between first-deletion classes. The pairwise
variance looks like a new cross-layer cancellation term.

This property reindexes every one of those distances by coordinate. The
complete first-deletion variance is exactly the sum of the ordinary
three-value variances at each layer: current deletion, current survival, and
anchors deleted earlier. Combined with the Active Two-Class Variance property, the global identity
collapses back to the original strike energy.

Therefore first-deletion factorization alone is a coordinate rewrite, not an
upper estimate. It becomes useful only after adding new arithmetic
information about deletion-class masses.

## Setup

Use the First-Deletion Variance Identity property's class counts

```math
n_k=H_k\quad(k<m),
\qquad
n_m=A_m,
```

and first-deletion vectors `v_k`. Let

```math
C=\operatorname{diag}(c_0,\ldots,c_{m-1}),
\qquad c_i>0.
```

Write

```math
\mathcal V_{\mathrm{del}}
=
\sum_{k<\ell}
n_kn_\ell
\lVert C^{1/2}(v_k-v_\ell)\rVert^2.
```

## Coordinate Reindexing

Fix coordinate `i`. Across the first-deletion classes, that coordinate has
three values:

```math
\begin{array}{c|c|c}
\text{classes} & \text{total mass} & \text{coordinate value}\\
\hline
k<i & A_0-A_i & 0\\
k=i & H_i & 1-1/r_i\\
k>i & A_{i+1} & -1/r_i.
\end{array}
```

The unordered pairwise squared-distance contribution in coordinate `i` is
therefore

```math
\begin{aligned}
\mathcal V_i
&=
c_iH_iA_{i+1}\\
&\quad+
c_i(A_0-A_i)
\left[
H_i\left(1-\frac1{r_i}\right)^2
+
\frac{A_{i+1}}{r_i^2}
\right].
\end{aligned}
```

The bracket is exactly the local Gram diagonal `G_(ii)`. Hence

```math
\boxed{
\mathcal V_i
=
c_i
\left[
H_iA_{i+1}
+
(A_0-A_i)G_{ii}
\right].
}
```

Summing the independent coordinate contributions gives

```math
\boxed{
\mathcal V_{\mathrm{del}}
=
\sum_{i=0}^{m-1}
c_i
\left[
H_iA_{i+1}
+
(A_0-A_i)G_{ii}
\right].
}
```

## Exact Collapse

The First-Deletion Variance Identity property states

```math
\mathcal E_D
=
A_0\sum_i c_iG_{ii}
-
\mathcal V_{\mathrm{del}}.
```

Substitute the coordinate formula:

```math
\begin{aligned}
\mathcal E_D
&=
\sum_i c_i
\left[
A_0G_{ii}
-
H_iA_{i+1}
-
(A_0-A_i)G_{ii}
\right]\\
&=
\sum_i c_i
\left[
A_iG_{ii}-H_iA_{i+1}
\right]
&&[\text{Simplification}]\\
&=
\sum_i c_iD_i^2
&&[\text{Active Two-Class Variance}].
\end{aligned}
```

Thus

```math
\boxed{
A_0\operatorname{tr}(CG)
-
\mathcal V_{\mathrm{del}}
=
\sum_i c_iD_i^2.
}
```

This is exactly the original definition of the weighted strike energy.

## Consequence

No subset of the first-deletion variance can be called an independent gain
without checking what complementary coordinate terms were discarded. The
minimum separation `H_iA_(i+1)` is the Active Two-Class Variance property's active two-class variance;
the remaining term `(A_0-A_i)G_(ii)` accounts exactly for anchors already
deleted before layer `i`.

Accordingly, the following purely algebraic route is exhausted:

1. factor the local Gram matrix by first-deletion class;
2. apply the population-times-trace variance identity;
3. reindex or lower-bound deletion-vector distances using only their
   triangular coordinates.

Any progress from this representation must add a theorem not contained in
the identities themselves—for example, a quantitative constraint on the
actual `H_i`, an average over heads, or an arithmetic correlation estimate.

## Validation

Exact rational checks were performed on:

```math
I=[19,19^2),\quad P_0=30,\quad(r_0,r_1)=(7,11),
```

and

```math
I=[17,17^2),\quad P_0=6,\quad(r_0,r_1,r_2)=(5,7,11).
```

For arbitrary positive rational test weights, the direct pairwise
first-deletion variance equaled the reindexed coordinate sum exactly. These
checks validate the derivation only.

## Related

- [Accepted-strike first-deletion variance identity](
  accepted-strike-first-deletion-variance-identity.md
  )
- [Accepted-strike active two-class variance identity](
  accepted-strike-active-two-class-variance-identity.md
  )
- [Accepted-strike localized layer Gram matrix](
  accepted-strike-localized-layer-gram-matrix.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
