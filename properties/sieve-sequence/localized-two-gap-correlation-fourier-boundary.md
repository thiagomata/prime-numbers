# Localized Two-Gap Correlation: Fourier Boundary

**Status:** Problem boundary. The rectangle identities are mathematically
proved; the required localized spectral bound is open here. Stainless
verification is not claimed.

## Meaning

Complete-period two-gap correlations average over every possible starting
point. A square-window collision count restricts both the starting point and
the separation. In quotient coordinates this is a two-dimensional rectangle
count.

Fourier analysis still gives an exact formula, but multiplying the CRT product
set by an interval indicator convolves their spectra. The missing theorem is a
convolution bound that retains enough of the CRT conductor decay after origin
localization.

## Setup

Let

```math
n=M',
\qquad
U\subseteq\mathbb Z/n\mathbb Z
```

be the quotient set of complete-period 2-gap starts. Let `I` be a cyclic
interval of quotient-coordinate origins and define

```math
g(u)
=
\mathbf 1_U(u)\mathbf 1_I(u).
```

Write

```math
J=|U\cap I|
=
\sum_{u\bmod n}g(u).
```

Let `r` be coprime to `n`, and let `0<=H<=n`.

## Rectangle Count

Define

```math
\mathcal R(I,H;r)
=
\sum_{u\bmod n}
g(u)
\sum_{h=1}^{H}g(u+rh).
```

This counts ordered pairs of localized 2-gap starts whose quotient-coordinate
difference is one of

```math
r,2r,\ldots,Hr\pmod n.
```

When `I` is obtained from a lifted absolute interval and the chosen differences
do not wrap around the cyclic boundary, this is the corresponding linear
square-window pair count. If wraparound is possible, the cyclic count must be
split at the boundary before being interpreted linearly.

## Exact Localized Fourier Formula

For an additive character `chi` modulo `n`, define

```math
\widehat g(\chi)
=
\sum_{u\bmod n}
g(u)\overline{\chi(u)}
```

and

```math
D_H(\chi;r)
=
\sum_{h=1}^{H}\chi(rh).
```

The localized cyclic autocorrelation is

```math
A_I(h)
=
\sum_{u\bmod n}g(u)g(u+h).
```

Finite Fourier inversion gives

```math
A_I(h)
=
\frac1n
\sum_\chi
|\widehat g(\chi)|^2\chi(h).
```

Therefore

```math
\boxed{
\mathcal R(I,H;r)
=
\frac1n
\sum_\chi
|\widehat g(\chi)|^2D_H(\chi;r).
}
```

The trivial character has

```math
\widehat g(1)=J,
\qquad
D_H(1;r)=H,
```

so the localized rectangle discrepancy is

```math
\mathcal E_I(H;r)
=
\mathcal R(I,H;r)-\frac{H}{n}J^2
```

with exact expansion

```math
\boxed{
\mathcal E_I(H;r)
=
\frac1n
\sum_{\chi\ne1}
|\widehat g(\chi)|^2D_H(\chi;r).
}
```

## Immediate Fourth-Moment Bound

Character orthogonality gives

```math
\sum_{\chi\ne1}|D_H(\chi;r)|^2=nH-H^2.
```

Hence

```math
\boxed{
|\mathcal E_I(H;r)|
\le
\frac1n
\sqrt{
\sum_{\chi\ne1}|\widehat g(\chi)|^4
}
\sqrt{nH-H^2}.
}
```

The exact missing quantity is thus the nontrivial fourth moment of the
localized spectrum.

## Product Becomes Convolution

Let

```math
f=\mathbf 1_U,
\qquad
b=\mathbf 1_I.
```

Then

```math
g=fb.
```

With the Fourier normalization used above, pointwise multiplication becomes
normalized convolution:

```math
\boxed{
\widehat g(\chi)
=
\frac1n
\left(
\widehat f*\widehat b
\right)(\chi).
}
```

The complete-period theorem gives an explicit CRT factorization for
`hat(f)`. The interval spectrum `hat(b)` is an explicit Dirichlet kernel. The
localized spectrum is their convolution, not their product.

## Generic Young Audit

Let

```math
L=|I|.
```

For the cyclic interval Dirichlet kernel, the standard pointwise estimate

```math
|\widehat b(k)|
\le
\min\left(
L,
\frac{n}{2\min(k,n-k)}
\right)
```

gives

```math
\|\widehat b\|_1
\ll
n\log(2L)
```

and

```math
\boxed{
\|\widehat b\|_{4/3}
\ll
n^{3/4}L^{1/4}.
}
```

The second estimate follows by splitting the frequency sum at `n/L`:
there are order `n/L` coefficients of size at most `L`, while the remaining
tail is bounded by the summable power `(n/k)^(4/3)`.

Define

```math
C_4
=
\prod_{p\mid n}
\left(
1+\frac{6p-16}{(p-2)^4}
\right).
```

The exact CRT fourth-moment theorem and Parseval give

```math
\|\widehat f\|_4
=
G C_4^{1/4},
\qquad
\|\widehat f\|_2
=
(nG)^{1/2}.
```

Young's convolution inequality applied to the normalized convolution first
gives

```math
\|\widehat g\|_4
\le
\frac1n
\|\widehat f\|_4
\|\widehat b\|_1
\ll
G C_4^{1/4}\log(2L).
```

The `L2*L(4/3)` form gives the sharper interval-dependent estimate

```math
\boxed{
\|\widehat g\|_4
\ll
n^{1/4}G^{1/2}L^{1/4}.
}
```

Inserting this into the immediate fourth-moment discrepancy bound yields

```math
|\mathcal E_I(H;r)|
\ll
G\sqrt{LH}.
```

This is rigorous, but it is not the required origin transference. It retains
the complete-period population `G` rather than the localized population

```math
J=|U\cap I|.
```

When `n` is much larger than `L`, `G` can be much larger than `J`, and this
estimate can be worse than a trivial bound using only the localized set.
Consequently, generic Young inequalities do not fit candidate #21's weighted
collision budget without a separate noncircular relation between `G` and `J`.

## Limitation

The exact factorized spectrum of the complete CRT set does not automatically
survive multiplication by a short interval. The `L4*L1` Young bound loses the
logarithmic interval Fourier `L1` norm and retains `G`; the
`L2*L(4/3)` bound removes that logarithm but still yields only
`G sqrt(LH)`. Both discard conductor localization before it can interact with
the interval.

This note does not prove a useful localized convolution bound. It identifies
the exact two-dimensional transference theorem, proves that the first generic
norm routes are insufficient, and gives the quantitative test every stronger
inequality must pass.

## Related

- [Fourier bound for two-gap correlation prefixes](
  fourier-two-gap-correlation-prefix-bound.md
  )
- [Complete-period two-gap pair-correlation average](
  complete-period-two-gap-pair-correlation-average.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
