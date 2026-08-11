# Harmless Energy As Spectral Excess Above The Two-Class Floor

**Status:** Mathematically proved exact identity and problem boundary.
Stainless verification is not claimed.

## Meaning

After filter `r`, the two harmful residue classes contain no survivors. This
forces a minimum amount of nontrivial Fourier mass even when the remaining
`r-2` harmless classes are perfectly uniform.

Candidate #22's harmless energy is exactly the spectral mass above that forced
floor. Removing the harmful classes therefore sharpens the center, but it does
not automatically make the localized spectrum small.

## Setup

Let `r>2`, and let

```math
d_a\ge0,
\qquad
a\pmod r,
```

be the post-filter 2-gap-start counts. The harmful classes are empty:

```math
d_0=d_{-2}=0.
```

Write

```math
M=\sum_{a\bmod r}d_a.
```

For `k modulo r`, define the additive Fourier transform

```math
\widehat d(k)
=
\sum_{a\bmod r}
d_a
\exp\left(-\frac{2\pi i k a}{r}\right).
```

Then

```math
\widehat d(0)=M.
```

## Parseval Form

Finite Parseval gives

```math
\sum_{a\bmod r}d_a^2
=
\frac1r
\sum_{k\bmod r}
|\widehat d(k)|^2.
```

The full `r`-class variance of the post-filter set is therefore

```math
\begin{aligned}
V_r
&=
\sum_{a\bmod r}d_a^2-\frac{M^2}{r}\\
&=
\boxed{
\frac1r
\sum_{\substack{k\bmod r\\k\ne0}}
|\widehat d(k)|^2.
}
\end{aligned}
```

Candidate #22's harmless energy is

```math
U
=
\sum_{a\notin\{0,-2\}}d_a^2
-
\frac{M^2}{r-2}.
```

Because the two omitted class counts are zero,

```math
U
=
V_r
-
\left(
\frac{M^2}{r-2}-\frac{M^2}{r}
\right).
```

Hence

```math
\boxed{
U
=
\frac1r
\sum_{\substack{k\bmod r\\k\ne0}}
|\widehat d(k)|^2
-
\frac{2M^2}{r(r-2)}.
}
\qquad[\text{Q.E.D.}]
```

## Sharp Forced Spectral Floor

Cauchy--Schwarz on the `r-2` harmless classes gives

```math
\sum_{a\notin\{0,-2\}}d_a^2
\ge
\frac{M^2}{r-2}.
```

Using Parseval, this is equivalent to

```math
\boxed{
\frac1r
\sum_{\substack{k\bmod r\\k\ne0}}
|\widehat d(k)|^2
\ge
\frac{2M^2}{r(r-2)}.
}
```

Equality holds exactly when every harmless class has the same count. Thus the
subtracted term is the sharp nontrivial spectral floor forced by the two empty
classes, and

```math
\boxed{
U
=
\text{nontrivial spectral mass}
-
\text{forced two-class floor}.
}
```

In particular, `U>=0`, with equality exactly at harmless-class uniformity.

## Sharp Unconstrained Upper Envelope

Without additional structure, all `M` survivors may occupy one harmless
class. Then

```math
\sum_a d_a^2=M^2.
```

Consequently,

```math
\boxed{
0
\le
U
\le
M^2\left(1-\frac1{r-2}\right)
=
M^2\frac{r-3}{r-2}.
}
```

Both endpoints are sharp whenever the corresponding integer class counts are
feasible. Thus Parseval and the two empty classes alone permit quadratic
harmless energy.

## Comparison With The Existing Localization Boundary

The localized two-gap Fourier property bounds a short correlation rectangle
through the fourth moment of a localized spectrum. Generic Young inequalities
give a bound of scale

```math
G\sqrt{LH},
```

where `G` is the complete-period 2-gap population, rather than the local
population `M`.

Harmless recentering subtracts only the explicit local floor

```math
\frac{2M^2}{r(r-2)}.
```

Without an independent noncircular relation between `G` and `M`, that
subtraction cannot convert a bound retaining `G` into the local weighted
estimate required by candidate #22.

Similarly, in the regime covered by the short-interval localization property,
where the interval length is at most the complementary CRT modulus, a fraction
`1-1/r` of the total spectral energy lies in characters nontrivial at `r`; the
complete-period fraction `2/r` is not preserved. Subtracting the forced
two-class floor does not reverse that localization effect.

## Consequence For Candidate #22

The exact spectral target is not merely to bound nontrivial Fourier mass. It
is to bound the excess above

```math
\frac{2M_i^2}{r_i(r_i-2)}
```

after square-window localization and then sum that excess with weights `w_i`.

A viable Fourier argument must exploit cancellation involving the localized
difference kernel, post-deletion conditioning, or a new local spectral
inequality normalized directly by `M_i`. Reusing complete-period conductor
weights or generic convolution norms does not supply the needed estimate.

## Limitation

This property does not rule out Fourier analysis. It rules out treating the
two deleted classes as if they restored complete-period spectral decay after
localization.

The weighted spectral-excess theorem required by candidate #22 remains open.

## Related

- [Harmless energy as a fixed-set pair correlation](
  harmless-energy-fixed-set-pair-form.md
  )
- [Complete-period uniformity of harmless 2-gap classes](
  complete-period-harmless-class-uniformity.md
  )
- [Localized two-gap correlation: Fourier boundary](
  localized-two-gap-correlation-fourier-boundary.md
  )
- [Short-interval localization destroys prime conductor decay](
  short-interval-localization-destroys-prime-conductor-decay.md
  )
- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
