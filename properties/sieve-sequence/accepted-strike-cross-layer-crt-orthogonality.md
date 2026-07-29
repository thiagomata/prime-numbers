# Accepted-Strike Cross-Layer CRT Orthogonality

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

The centered divisibility observables for different incoming filters are
exactly orthogonal on one complete final CRT period. This gives a genuine
cross-layer mean-square inequality for candidate #23.

The exact norms also expose the limitation. They are normalized by the full
final primorial period, not by the short safe window. Bessel's inequality
therefore produces a bound proportional to the final period times the local
window length. Cross-layer orthogonality is real, but complete-period
orthogonality alone does not provide the missing local discrepancy estimate.

## Setup

Let

```math
P_{i+1}=P_i r_i
\qquad(0\le i<m),
```

where `P_0` is squarefree, the `r_i` are distinct primes, and
`gcd(P_i,r_i)=1`. Write

```math
R=P_m.
```

On the residue ring `Z/RZ`, define the centered layer observable

```math
g_i(a)
=
\mathbf 1_{\gcd(a,P_i)=1}
\left(
\mathbf 1_{r_i\mid a}-\frac1{r_i}
\right).
```

For an integer interval `I`, let `f_I(a)` be the number of elements of `I`
congruent to `a modulo R`. Then

```math
D_i(I)
=
\sum_{a\bmod R}f_I(a)g_i(a)
```

is exactly

```math
D_i(I)
=
\#\{n\in I:\gcd(n,P_i)=1,\ r_i\mid n\}
-
\frac1{r_i}
\#\{n\in I:\gcd(n,P_i)=1\}.
```

This is candidate #23's accepted-strike discrepancy.

## Pairwise Orthogonality

For `i<j`, the support of `g_j` satisfies

```math
\gcd(a,P_j)=1.
```

Because `r_i` divides `P_j`, every point in this support has `r_i` not
dividing `a`. Hence

```math
g_i(a)=-\frac1{r_i}
```

whenever `g_j(a)` is nonzero. Therefore

```math
\begin{aligned}
\sum_{a\bmod R}g_i(a)g_j(a)
&=
-\frac1{r_i}\sum_{a\bmod R}g_j(a)
&&[\text{Support of }g_j].
\end{aligned}
```

Among residues coprime to `P_j`, CRT makes the `r_j` coordinate uniform.
Exactly one of its `r_j` values is divisible by `r_j`, so its centered sum is
zero:

```math
\sum_{a\bmod R}g_j(a)=0.
```

Consequently,

```math
\boxed{
\sum_{a\bmod R}g_i(a)g_j(a)=0
\qquad(i\ne j).
}
```

## Exact Norms

Conditional on `gcd(a,P_i)=1`, the `r_i` coordinate is uniform. Thus

```math
\begin{aligned}
\frac1R\sum_{a\bmod R}g_i(a)^2
&=
\frac{\varphi(P_i)}{P_i}
\left[
\frac1{r_i}\left(1-\frac1{r_i}\right)^2
+
\left(1-\frac1{r_i}\right)\frac1{r_i^2}
\right]
&&[\text{CRT}]\\
&=
\frac{\varphi(P_i)}{P_i}
\frac{r_i-1}{r_i^2}
&&[\text{Simplification}].
\end{aligned}
```

Hence

```math
\boxed{
\lVert g_i\rVert_2^2
=
R\frac{\varphi(P_i)}{P_i}\frac{r_i-1}{r_i^2}.
}
```

## Exact Bessel Bound

The nonzero `g_i` form an orthogonal family. Finite-dimensional Bessel
inequality gives

```math
\boxed{
\sum_{i=0}^{m-1}
\frac{D_i(I)^2}{
R\frac{\varphi(P_i)}{P_i}\frac{r_i-1}{r_i^2}
}
\le
\sum_{a\bmod R}f_I(a)^2.
}
```

If `I` has length `L<=R`, no two elements of `I` have the same residue modulo
`R`, so the right side is exactly `L`. Therefore

```math
\boxed{
\sum_{i=0}^{m-1}
\frac{r_i^2}{
\frac{\varphi(P_i)}{P_i}(r_i-1)
}
D_i(I)^2
\le
LR.
}
```

Using property #49's `mathcal M_i=r_iD_i`, the same theorem is

```math
\boxed{
\sum_{i=0}^{m-1}
\frac{\mathcal M_i(I)^2}{
\frac{\varphi(P_i)}{P_i}(r_i-1)
}
\le
LR.
}
```

## Consequence For Candidate #23

Let

```math
c_i
=
w_i\frac{r_i}{2(r_i-2)}
```

be candidate #23's energy coefficient. Bessel implies

```math
\begin{aligned}
\mathcal E_D
&=
\sum_i c_iD_i(I)^2\\
&\le
\left(
\max_i c_i\lVert g_i\rVert_2^2
\right)
\sum_i\frac{D_i(I)^2}{\lVert g_i\rVert_2^2}\\
&\le
\boxed{
LR
\max_i
\left[
w_i
\frac{\varphi(P_i)}{P_i}
\frac{r_i-1}{2r_i(r_i-2)}
\right].
}
\end{aligned}
```

The factor `R` is the decisive obstruction. In the intended regime, the
final primorial can be much larger than the square-safe window. This bound is
then far above the local scale required by candidate #21.

The theorem does not show that the actual energy is large, and it does not
refute candidate #23. It proves that complete-period CRT orthogonality, used
only through Bessel's inequality, has the wrong normalization. A useful
improvement must localize the orthogonality, introduce another averaging
variable, or exploit arithmetic structure of the interval correlations
beyond their complete-period Gram matrix.

## Validation

Exact rational checks were performed for

```math
(P_0;r_0,r_1,r_2)=(6;5,7,11)
```

and

```math
(P_0;r_0,r_1)=(30;7,11).
```

All cross inner products were zero. For `R=2310`, the first chain's exact
squared norms were

```math
\frac{616}{5},
\qquad
\frac{528}{7},
\qquad
\frac{480}{11},
```

matching the displayed formula. These finite checks validate the arithmetic
derivation; they are not evidence for an unproved asymptotic estimate.

## Related

- [Accepted-strike summatory coprime remainder](
  accepted-strike-summatory-coprime-remainder.md
  )
- [Accepted-strike CRT lift-index transform](
  accepted-strike-crt-lift-index-transform.md
  )
- [Black-box large sieve does not fit the weighted collision budget](
  black-box-large-sieve-does-not-fit-weighted-collision-budget.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
