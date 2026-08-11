# Accepted-Strike Active Two-Class Variance Identity

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

At one layer, the centered strike observable has only two nonzero values:
one on anchors deleted by the incoming prime and one on anchors that survive
that prime. Its weighted two-class variance therefore has an exact closed
form.

This identity strength-tests the most immediate consequence of property
#53's first-deletion dispersion. The forced separation between the current
deletion class and all later classes is real, but its contribution exactly
reconstructs the current squared discrepancy. It is not an independent upper
bound.

## Setup

At layer `i`, let

```math
A_i
=
\#\{n\in I:\gcd(n,P_i)=1\},
```

```math
H_i
=
\#\{n\in I:\gcd(n,P_i)=1,\ r_i\mid n\},
```

and

```math
A_{i+1}=A_i-H_i.
```

Define

```math
D_i=H_i-\frac{A_i}{r_i}.
```

On the `H_i` deleted anchors, the centered strike observable equals
`1-1/r_i`. On the `A_(i+1)` surviving anchors, it equals `-1/r_i`.
Therefore its local squared norm is

```math
G_{ii}
=
H_i\left(1-\frac1{r_i}\right)^2
+
\frac{A_{i+1}}{r_i^2}.
```

## Exact Identity

Using `A_i=H_i+A_(i+1)`,

```math
\begin{aligned}
A_iG_{ii}-H_iA_{i+1}
&=
(H_i+A_{i+1})
\left[
H_i\left(1-\frac1{r_i}\right)^2
+
\frac{A_{i+1}}{r_i^2}
\right]
-
H_iA_{i+1}\\
&=
\left[
H_i\left(1-\frac1{r_i}\right)
-
\frac{A_{i+1}}{r_i}
\right]^2
&&[\text{Expansion}]\\
&=
\left(H_i-\frac{A_i}{r_i}\right)^2
&&[\text{Substitution}]\\
&=
D_i^2.
\end{aligned}
```

Hence

```math
\boxed{
D_i^2
=
A_iG_{ii}
-
H_iA_{i+1}.
}
```

This is the exact two-point weighted-variance identity for the active
population at layer `i`.

## Relation To First-Deletion Dispersion

The First-Deletion Variance Identity property proves that deletion class `i` is separated from every later
class by weighted squared distance at least `c_i`. Since the total mass in
later classes is exactly `A_(i+1)`,

```math
\sum_{k<\ell}
n_kn_\ell
\lVert C^{1/2}(v_k-v_\ell)\rVert^2
\ge
\sum_i c_iH_iA_{i+1}.
```

Inserted into the First-Deletion Variance Identity property's global variance identity, this gives

```math
\mathcal E_D
\le
A_0\operatorname{tr}(CG)
-
\sum_i c_iH_iA_{i+1}.
```

The per-layer identity shows why this does not close candidate #23. Since

```math
c_iH_iA_{i+1}
=
c_iA_iG_{ii}-c_iD_i^2,
```

the proposed correction already contains the unknown target `c_iD_i^2`.
Using only this forced separation rearranges the same strike-energy identity;
it does not estimate it.

The remaining parts of the full deletion-class variance are still exact and
nonnegative. Exploiting them requires quantitative mass in deletion classes
separated by more than the single compulsory coordinate, or an external
estimate for the actual `H_i`.

## Boundary

The result does not make first-deletion factorization useless. It rules out
one specific shortcut: retaining only the minimum distance `c_i` between a
deletion class and all later classes.

A useful continuation must retain the additional distances

```math
\sum_{i<j<\ell}\frac{c_j}{r_j^2}
```

and the terminal coordinate of the later deletion class, or prove arithmetic
dispersion of the `H_i`. If these terms are discarded, the argument returns
exactly to `mathcal E_D`.

## Validation

The identity was checked with exact rational arithmetic on:

```math
I=[19,19^2),\quad P_0=30,\quad(r_0,r_1)=(7,11),
```

and

```math
I=[17,17^2),\quad P_0=6,\quad(r_0,r_1,r_2)=(5,7,11).
```

Every layer satisfied `D_i^2=A_iG_(ii)-H_iA_(i+1)` exactly. These finite
checks validate the derivation only.

## Related

- [Accepted-strike first-deletion variance identity](
  accepted-strike-first-deletion-variance-identity.md
  )
- [Accepted-strike localized layer Gram matrix](
  accepted-strike-localized-layer-gram-matrix.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
