# Accepted-Strike First-Deletion Variance Identity

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

Every initially accepted integer is either first deleted by one incoming
prime or survives the complete chain. Its vector of centered strike
observables depends only on that first-deletion class.

This gives an exact rank-one factorization of the Localized-Layer Gram Matrix property's localized Gram
matrix. More importantly, candidate #23's strike energy is exactly a
first-deletion barycenter energy. The standard population upper bound has an
explicit negative correction equal to the weighted variance between
different deletion classes.

The identity does not yet lower-bound that variance. It identifies the
precise positive quantity that must be retained for first-deletion structure
to improve on generic Cauchy.

## Setup

Let

```math
P_{i+1}=P_i r_i
\qquad(0\le i<m)
```

and let `I` be an integer interval. Define

```math
A_i
=
\#\{n\in I:\gcd(n,P_i)=1\},
```

```math
H_i
=
\#\{n\in I:\gcd(n,P_i)=1,\ r_i\mid n\}.
```

Then

```math
A_{i+1}=A_i-H_i.
```

Put

```math
n_k=H_k\quad(0\le k<m),
\qquad
n_m=A_m.
```

The classes partition the `A_0` initially accepted integers, so

```math
\boxed{
\sum_{k=0}^{m}n_k=A_0.
}
```

Let

```math
g_i(n)
=
\mathbf 1_{\gcd(n,P_i)=1}
\left(
\mathbf 1_{r_i\mid n}-\frac1{r_i}
\right)
```

and `D_i=sum_(n in I) g_i(n)`.

## First-Deletion Vectors

For `k<m`, define `v_k in R^m` by

```math
(v_k)_i
=
\begin{cases}
-1/r_i,&i<k,\\
1-1/r_k,&i=k,\\
0,&i>k.
\end{cases}
```

Define the survivor vector

```math
(v_m)_i=-\frac1{r_i}.
```

If an initially accepted integer is first deleted at layer `k<m`, then it
survives every earlier filter, is divisible by `r_k`, and is absent from
every later acceptance set. Its observable vector is therefore exactly
`v_k`. A final survivor is not divisible by any `r_i`, so its vector is
`v_m`.

Consequently, the discrepancy vector `D=(D_0,...,D_(m-1))` satisfies

```math
\boxed{
D=\sum_{k=0}^{m}n_kv_k.
}
```

## Rank-One Gram Factorization

Let `G` be the Localized-Layer Gram Matrix property's localized Gram matrix:

```math
G_{ij}
=
\sum_{n\in I}g_i(n)g_j(n).
```

Grouping the initially accepted integers by first deletion gives

```math
\boxed{
G
=
\sum_{k=0}^{m}n_kv_kv_k^T.
}
```

This proves directly that `G` is positive semidefinite and has rank at most
the number of nonempty first-deletion classes.

## Exact Weighted Variance Identity

Let `C=diag(c_0,...,c_(m-1))` with `c_i>0`, and put

```math
u_k=C^{1/2}v_k.
```

The weighted strike energy is

```math
\mathcal E_C
=
D^TCD
=
\left\lVert\sum_kn_ku_k\right\rVert^2.
```

For any weighted finite family,

```math
\left(\sum_kn_k\right)
\left(\sum_kn_k\lVert u_k\rVert^2\right)
-
\left\lVert\sum_kn_ku_k\right\rVert^2
=
\sum_{k<\ell}n_kn_\ell\lVert u_k-u_\ell\rVert^2.
```

Using `sum n_k=A_0` gives the exact identity

```math
\boxed{
\mathcal E_C
=
A_0\sum_{k=0}^{m}n_k\lVert u_k\rVert^2
-
\sum_{0\le k<\ell\le m}
n_kn_\ell\lVert u_k-u_\ell\rVert^2.
}
```

Because

```math
\sum_kn_k\lVert u_k\rVert^2
=
\operatorname{tr}(CG),
```

this is equivalently

```math
\boxed{
\mathcal E_C
=
A_0\operatorname{tr}(CG)
-
\sum_{k<\ell}
n_kn_\ell
\lVert C^{1/2}(v_k-v_\ell)\rVert^2.
}
```

Thus the generic bound

```math
\mathcal E_C\le A_0\operatorname{tr}(CG)
```

loses exactly the displayed first-deletion dispersion.

## Explicit Vector Norms

For `k<m`,

```math
\boxed{
\lVert u_k\rVert^2
=
\sum_{i<k}\frac{c_i}{r_i^2}
+
c_k\left(1-\frac1{r_k}\right)^2.
}
```

For the survivor class,

```math
\boxed{
\lVert u_m\rVert^2
=
\sum_{i<m}\frac{c_i}{r_i^2}.
}
```

If `k<ell<m`, direct subtraction gives

```math
\boxed{
\lVert u_k-u_\ell\rVert^2
=
c_k
+
\sum_{k<i<\ell}\frac{c_i}{r_i^2}
+
c_\ell\left(1-\frac1{r_\ell}\right)^2.
}
```

If `k<m` and `ell=m`, then

```math
\boxed{
\lVert u_k-u_m\rVert^2
=
c_k
+
\sum_{k<i<m}\frac{c_i}{r_i^2}.
}
```

In particular, distinct first-deletion vectors are separated by at least
`c_k` when the earlier class is `k`.

## Candidate #23 Specialization

Set

```math
c_i
=
w_i\frac{r_i}{2(r_i-2)}.
```

Then `mathcal E_C=mathcal E_D`, candidate #23's exact weighted energy. Hence

```math
\boxed{
\mathcal E_D
=
A_0\operatorname{tr}(CG)
-
\sum_{k<\ell}
n_kn_\ell
\lVert C^{1/2}(v_k-v_\ell)\rVert^2.
}
```

This formulation is noncircular. It remains valid when `A_m=0`, and it never
divides by a late or final survivor population.

The identity shows exactly what a useful first-deletion theorem must prove:
the class counts must be sufficiently spread that the negative pairwise
variance nearly cancels the population-times-trace term. Merely deleting the
negative term returns generic Cauchy. Bounding it usefully requires
independent lower information about more than one deletion class, or an
analytic estimate forcing the deletion-time distribution away from a single
class.

## Sharp Abstract Population Envelope

If the only retained information is

```math
n_k\ge0,
\qquad
\sum_kn_k=A_0,
```

then the barycenter formula and the triangle inequality give

```math
\begin{aligned}
\sqrt{\mathcal E_D}
&=
\left\lVert\sum_kn_kC^{1/2}v_k\right\rVert\\
&\le
\sum_kn_k\lVert C^{1/2}v_k\rVert\\
&\le
A_0\max_k\lVert C^{1/2}v_k\rVert.
\end{aligned}
```

Therefore

```math
\boxed{
\mathcal E_D
\le
A_0^2
\max_k\lVert C^{1/2}v_k\rVert^2.
}
```

This envelope is sharp over abstract nonnegative class counts: place all
`A_0` units in a class attaining the maximum norm. This does not claim that
every such concentrated vector is realized by a square-safe sieve interval.
It proves that the rank-one factorization and total population alone cannot
exclude it.

Consequently, triangular support of the `v_k` is not by itself the missing
theorem. Any strict universal improvement must use an arithmetic constraint
on the actual deletion-class counts, such as a lower bound for dispersion
between at least two classes or cancellation after averaging over heads.

## Validation

Exact rational checks were performed on:

```math
I=[19,19^2),\quad P_0=30,\quad(r_0,r_1)=(7,11),
```

with deletion-class counts `(13,7,71)`, and

```math
I=[17,17^2),\quad P_0=6,\quad(r_0,r_1,r_2)=(5,7,11),
```

with deletion-class counts `(18,10,5,58)`.

For arbitrary positive rational test weights, the discrepancy barycenter,
rank-one Gram factorization, and weighted variance identity all held exactly.
These checks validate the derivation only.

## Related

- [Accepted-strike localized layer Gram matrix](
  accepted-strike-localized-layer-gram-matrix.md
  )
- [Accepted-strike cross-layer CRT orthogonality](
  accepted-strike-cross-layer-crt-orthogonality.md
  )
- [First-deletion pair terminal energy](
  first-deletion-pair-terminal-energy.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
