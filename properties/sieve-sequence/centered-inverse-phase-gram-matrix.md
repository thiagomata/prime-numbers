# Centered Inverse-Phase Gram Matrix

**Status:** Mathematically proved exact finite identities. Stainless
verification is not claimed.

## Meaning

Property #43 expresses every harmless-class count as an interval sum of one
common CRT word at an explicit inverse phase. Candidate #22 does not measure
the uncentered size of those samples: it first subtracts their mean across the
`r-2` harmless classes.

This property inserts that mean projection exactly. The centered cost of one
Fourier frequency is governed by an explicit geometric phase sum. The
interaction of two different frequencies is governed by an equally explicit
Gram entry.

Centering strongly suppresses frequencies that are nearly constant on the
inverse phases. It does not diagonalize the Fourier expansion. The remaining
proof problem is a structured quadratic-form estimate involving both the CRT
spectrum and this phase Gram matrix.

## Setup

Use the notation of property #43:

```math
P>r\ge5,
\qquad
\gcd(P,r)=1,
\qquad
rs=1+kP,
```

with `1<=s<P` and `1<=k<r`.

Write the lower endpoint as

```math
A=qr+b,
\qquad
0\le b<r.
```

For each canonical residue `0<=a<r`, set

```math
\varepsilon_a=\mathbf 1_{a<b},
\qquad
v_a=q+sa+\varepsilon_a\pmod P.
```

Let

```math
H
=
\{0,1,\ldots,r-1\}\setminus\{0,r-2\},
\qquad
h=|H|=r-2.
```

For a frequency `m modulo P`, define the phase vector on `H`

```math
\phi_m(a)
=
e^{2\pi i m v_a/P}.
```

Let `C` subtract the mean on `H`:

```math
(Cz)(a)
=
z(a)-\frac1h\sum_{c\in H}z(c).
```

Finally define

```math
K_m
=
\sum_{a\in H}\phi_m(a).
```

## Exact Mean-Projection Identity

The vector `C phi_m` has squared norm

```math
\begin{aligned}
\|C\phi_m\|_2^2
&=
\sum_{a\in H}
\left|
\phi_m(a)-\frac{K_m}{h}
\right|^2\\
&=
\sum_{a\in H}|\phi_m(a)|^2
-\frac{|K_m|^2}{h}\\
&=
h-\frac{|K_m|^2}{h}.
\end{aligned}
```

Therefore

```math
\boxed{
\|C\phi_m\|_2^2
=
h-\frac{|K_m|^2}{h}.
}
\qquad[\text{Q.E.D.}]
```

The cost lies between `0` and `h`. It is small exactly when the frequency is
nearly constant across the selected inverse phases.

## Closed Formula For The Phase Sum

For a nonzero frequency `m modulo P`, define

```math
\omega_m=e^{2\pi i m/P},
\qquad
\zeta_m=e^{2\pi i ms/P}.
```

The inverse relation gives

```math
\zeta_m^r
=
e^{2\pi i mrs/P}
=
e^{2\pi i m(1+kP)/P}
=
\omega_m.
```

Before removing the harmful classes, the phase sum is

```math
\begin{aligned}
\sum_{a=0}^{r-1}\phi_m(a)
&=
e^{2\pi i mq/P}
\left(
\omega_m\sum_{a=0}^{b-1}\zeta_m^a
+
\sum_{a=b}^{r-1}\zeta_m^a
\right)\\
&=
e^{2\pi i mq/P}
\left(
\omega_m\frac{1-\zeta_m^b}{1-\zeta_m}
+
\frac{\zeta_m^b-\zeta_m^r}{1-\zeta_m}
\right)\\
&=
e^{2\pi i mq/P}
\zeta_m^b
\frac{1-\omega_m}{1-\zeta_m}.
\end{aligned}
```

The denominator is nonzero: `zeta_m=1` would imply `m=0 modulo P` because
`s` is invertible modulo `P`.

Define

```math
\delta_0=\mathbf 1_{0<b},
\qquad
\delta_-=\mathbf 1_{r-2<b}.
```

Removing classes `0` and `r-2` gives the exact harmless phase sum

```math
\boxed{
K_m
=
e^{2\pi i mq/P}
\left[
\zeta_m^b\frac{1-\omega_m}{1-\zeta_m}
-\omega_m^{\delta_0}
-\omega_m^{\delta_-}\zeta_m^{r-2}
\right].
}
```

For the zero frequency,

```math
K_0=h.
```

Thus every single-frequency centered cost is explicit.

## Exact Cross-Frequency Gram Entry

For any frequencies `m,n modulo P`,

```math
\begin{aligned}
\langle C\phi_m,C\phi_n\rangle
&=
\sum_{a\in H}
\phi_m(a)\overline{\phi_n(a)}
-\frac{K_m\overline{K_n}}h\\
&=
K_{m-n}
-\frac{K_mK_{-n}}h.
\end{aligned}
```

Therefore

```math
\boxed{
\langle C\phi_m,C\phi_n\rangle
=
K_{m-n}
-\frac{K_mK_{-n}}h.
}
\qquad[\text{Q.E.D.}]
```

The diagonal case `m=n` recovers

```math
h-\frac{|K_m|^2}{h}.
```

The off-diagonal entries are generally not zero. Centering is not an
orthogonality theorem.

## Insertion Into The Harmless Energy

Let `g_r` be the periodic CRT word from property #43, let

```math
\rho=\frac1P\sum_{u\bmod P}g_r(u),
```

and define the centered Fourier coefficients

```math
\widehat g_0(m)
=
\sum_{u\bmod P}
\bigl(g_r(u)-\rho\bigr)e^{-2\pi imu/P}.
```

For fiber length `ell_a`, put

```math
D_{\ell_a}(m)
=
\sum_{j=0}^{\ell_a-1}e^{2\pi imj/P},
\qquad
\psi_m(a)
=
D_{\ell_a}(m)\phi_m(a).
```

Fourier inversion and property #43 give the exact class-count vector

```math
d
=
\rho\ell
+
\frac1P
\sum_{m\ne0}
\widehat g_0(m)\psi_m.
```

Consequently candidate #22's energy is exactly

```math
\boxed{
U
=
\left\|
\rho C\ell
+
\frac1P
\sum_{m\ne0}
\widehat g_0(m)C\psi_m
\right\|_2^2.
}
```

This formula keeps the two possible fiber lengths explicit.

## Equal-Length Core

If every harmless fiber has one common length `ell`, then `C ell=0` and

```math
\psi_m=D_\ell(m)\phi_m.
```

Expanding the square gives

```math
\boxed{
\begin{aligned}
U
&=
\frac1{P^2}
\sum_{\substack{m\ne0\\n\ne0}}
\widehat g_0(m)\overline{\widehat g_0(n)}
D_\ell(m)\overline{D_\ell(n)}\\
&\qquad\qquad\cdot
\left(
K_{m-n}
-\frac{K_mK_{-n}}h
\right).
\end{aligned}
}
```

This is the exact centered inverse-phase quadratic form.

## What The Identity Resolves

The uncentered large-sieve audit in property #43 was incomplete as an audit
of candidate #22: it ignored the projection `C`. The new diagonal factor

```math
h-\frac{|K_m|^2}{h}
```

can be much smaller than `h`, so frequencies that look large to an
uncentered estimate may be almost free after harmless-class centering.

The identity also exposes the next obstruction. The harmless energy is not
the sum of the diagonal single-frequency costs. The cross-frequency kernel

```math
K_{m-n}-\frac{K_mK_{-n}}h
```

must be controlled together with the factored CRT coefficients
`hat(g_0)(m)` and the interval multipliers `D_ell(m)`.

## Remaining Algebraic Test

A successful continuation may take either of two precise forms:

1. prove that the full Gram operator is small on the particular vector
   `hat(g_0)(m)D_ell(m)`, using CRT factorization; or
2. prove cancellation after summing the centered Gram forms with candidate
   #21's chain weights.

Bounding every Gram entry by its absolute value discards the new centering
and returns to a complete-period-scale estimate. That route should not be
repeated.

## Related

- [Harmless-class counts as translated CRT fibers](
  harmless-class-crt-translated-fibers.md
  )
- [Harmless energy as spectral excess above the two-class floor](
  harmless-energy-spectral-excess.md
  )
- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
