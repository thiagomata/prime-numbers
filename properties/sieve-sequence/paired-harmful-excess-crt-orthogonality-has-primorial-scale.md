# Paired Harmful-Excess CRT Orthogonality Has Primorial Scale

**Status:** Mathematically proved boundary result. Stainless verification is
not claimed.

## Meaning

Candidate #24's harmful-excess coordinates form an exactly orthogonal family
over one complete final CRT period. Each coordinate also has mean zero, so
complete period blocks make no contribution to it.

This is a genuine cross-layer fact, but its direct Bessel bound has the wrong
normalization for a short safe window. The upper bound contains the number of
final paired-survivor classes in a complete primorial period. Thus
complete-period orthogonality alone cannot provide candidate #24's missing
energy estimate.

## Setup

Let `M_0` be squarefree and let `r_0,...,r_{m-1}` be distinct odd primes not
dividing `M_0`. Define

```math
M_{i+1}=M_ir_i,
\qquad
R=M_m.
```

On `Z/RZ`, let

```math
F_i(n)
=
\mathbf 1_{\gcd(n(n+2),M_i)=1}
```

be the indicator that the pair `(n,n+2)` survives all filters installed
before `r_i`. Let

```math
h_i(n)
=
\mathbf 1_{r_i\mid n(n+2)}.
```

Because `r_i>2`, the two harmful residues `0` and `-2 modulo r_i` are
distinct. Write

```math
p_i=\frac2{r_i},
\qquad
a_i=1-p_i,
```

and define the centered paired observable

```math
\boxed{
g_i(n)=F_i(n)(h_i(n)-p_i).
}
```

For an integer interval `I`, the corresponding harmful excess is

```math
\begin{aligned}
b_i(I)
&=
\sum_{n\in I}g_i(n)\\
&=
\#\{n\in I:F_i(n)=1,\ h_i(n)=1\}
-
\frac2{r_i}\#\{n\in I:F_i(n)=1\}.
\end{aligned}
```

This is exactly candidate #24's coordinate `b_i=K_i-2N_i/r_i`.

## Complete-Block Cancellation

The function `g_i` has period `M_{i+1}`. Conditional on `F_i(n)=1`, CRT makes
the `r_i` coordinate uniform. Exactly two of its `r_i` values have `h_i=1`.
Therefore

```math
\begin{aligned}
\sum_{n\bmod M_{i+1}}g_i(n)
&=
\sum_{\substack{n\bmod M_{i+1}\\F_i(n)=1}}
(h_i(n)-p_i)\\
&=
\#\{F_i=1\}
\left(
\frac2{r_i}-p_i
\right)\\
&=0.
\end{aligned}
```

Hence every complete `M_{i+1}` block contributes zero to `b_i(I)`.
The discrepancy is entirely in the incomplete boundary blocks.

## Pairwise Cross-Layer Orthogonality

Suppose `i<j`. On the support of `g_j`, the pair `(n,n+2)` survives every
prime in `M_j`, including `r_i`. Thus

```math
F_i(n)=1,
\qquad
h_i(n)=0,
\qquad
g_i(n)=-p_i.
```

It follows that

```math
\begin{aligned}
\sum_{n\bmod R}g_i(n)g_j(n)
&=
-p_i\sum_{n\bmod R}g_j(n)
&&[\text{Support of }g_j]\\
&=0
&&[\text{Complete-block cancellation}].
\end{aligned}
```

By symmetry,

```math
\boxed{
\sum_{n\bmod R}g_i(n)g_j(n)=0
\qquad(i\ne j).
}
```

## Exact Norms

Let

```math
d_i
=
\frac1R\sum_{n\bmod R}F_i(n)
```

be the complete-period density of pairs surviving before `r_i`. On the
support of `F_i`, the variable `h_i` equals `1` with frequency `p_i` and `0`
with frequency `a_i`. Therefore

```math
\begin{aligned}
\frac1R\sum_{n\bmod R}g_i(n)^2
&=
d_i
\left[
p_i(1-p_i)^2+a_ip_i^2
\right]
&&[\text{CRT}]\\
&=
d_ip_ia_i
&&[\text{Simplification}].
\end{aligned}
```

Thus

```math
\boxed{
\lVert g_i\rVert_2^2
=
Rd_ip_ia_i.
}
```

## Complete-Period Bessel Bound

Let `f_I(a)` count the elements of `I` congruent to `a modulo R`. Then

```math
b_i(I)=\sum_{a\bmod R}f_I(a)g_i(a).
```

The nonzero `g_i` are orthogonal, so Bessel's inequality gives

```math
\boxed{
\sum_{i=0}^{m-1}
\frac{b_i(I)^2}{Rd_ip_ia_i}
\le
\sum_{a\bmod R}f_I(a)^2.
}
```

If `I` has length `L<=R`, its elements occupy distinct residue classes modulo
`R`, and the right side is exactly `L`. Hence

```math
\boxed{
\sum_{i=0}^{m-1}
\frac{b_i(I)^2}{d_ip_ia_i}
\le
LR.
}
```

## Consequence For Candidate #24

Candidate #24's harmful-excess energy is

```math
E_b
=
\sum_iw_i\frac1{2a_i}b_i(I)^2.
```

Using the Bessel bound,

```math
\begin{aligned}
E_b
&\le
\left(
\max_i
\frac{w_i}{2a_i}
\lVert g_i\rVert_2^2
\right)
\sum_i
\frac{b_i(I)^2}{\lVert g_i\rVert_2^2}\\
&\le
\boxed{
LR\max_i\frac{w_id_i}{r_i}.
}
\end{aligned}
```

Now let

```math
P_i=A_{0,i}=\prod_{j<i}a_j.
```

The paired-survivor densities and terminal weights satisfy

```math
d_i=d_0P_i,
\qquad
d_m=d_0P_m,
\qquad
w_i=A_{i+1,m}=\frac{P_m}{P_ia_i}.
```

Consequently,

```math
\frac{w_id_i}{r_i}
=
\frac{d_m}{r_i-2}.
```

Since the `r_i` increase,

```math
\boxed{
E_b
\le
\frac{LRd_m}{r_0-2}.
}
```

The quantity `Rd_m` is the exact number of final paired-survivor residue
classes in one complete CRT period. It remains primorial-scale in the
intended short-window regime. The bound is therefore far larger than the
local extinction threshold that candidate #24 must beat.

## Boundary

This property does not show that `E_b` is large and does not refute candidate
#24. It proves that black-box Bessel applied to complete-period CRT
orthogonality cannot establish the needed upper bound.

A successful cross-layer estimate must retain information discarded by this
argument. In particular, it must control localized interval correlations of
the `g_i`, exploit cancellation among their actual coefficients, or introduce
an averaging mechanism that replaces the complete-period factor by a local
scale.

No empirical evidence is used in this result.

## Related

- [Weighted Deletion Conservation Law](weighted-deletion-conservation-law.md)
- [Harmful-Excess Energy Is Terminal](weighted-harmful-excess-energy-is-terminal.md)
- [Accepted-Strike Cross-Layer CRT Orthogonality](accepted-strike-cross-layer-crt-orthogonality.md)
- [Short-Interval Localization Destroys Prime Conductor Decay](short-interval-localization-destroys-prime-conductor-decay.md)
- [Candidate #24: Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
