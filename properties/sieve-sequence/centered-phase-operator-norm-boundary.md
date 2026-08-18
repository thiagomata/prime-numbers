# Centered Phase Operator Norm Boundary

**Status:** Mathematically proved exact finite operator identity and strategy
boundary. Stainless verification is not claimed.

## Meaning

The Inverse-Phase Gram Matrix property shows that harmless-class centering can make an individual
Fourier frequency much cheaper than an uncentered estimate predicts. This
property tests whether those single-frequency savings improve the generic
operator norm after all frequencies are combined.

They do not. The inverse phases are distinct modulo the old period, so their
full Fourier rows are exactly orthogonal. Projecting away the classwise
constant vector removes one singular direction but leaves every other
singular value equal to `sqrt(P)`.

Consequently, applying the sharp centered operator norm to an arbitrary
Fourier coefficient vector reproduces the full-shift Parseval bound. Any
improvement for candidate #22 must use arithmetic alignment of the particular
CRT spectrum and interval multipliers, not only centering and operator norm.

## Setup

Use the notation of the CRT Fiber Translation property and #44:

```math
P>r\ge5,
\qquad
rs=1+kP,
\qquad
A=qr+b,
\qquad
0\le b<r.
```

For `0<=a<r`, set

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
h=r-2.
```

Define the `h by P` phase matrix

```math
\mathsf A_{a,m}
=
e^{2\pi i m v_a/P},
\qquad
a\in H,
\quad
m\pmod P.
```

Let `C` be the orthogonal projection that subtracts the mean across the
`h` harmless rows.

## The Inverse Phases Are Distinct

Suppose `v_a=v_c modulo P` for two distinct canonical residues `a,c`. Put

```math
d=a-c,
\qquad
\delta=\varepsilon_a-\varepsilon_c.
```

Then

```math
sd+\delta\equiv0\pmod P.
```

Multiplying by `r` and using `rs=1+kP` shows

```math
P\mid d+r\delta.
```

There are three cases.

If `delta=0`, then

```math
0<|d|<r<P,
```

so `P` cannot divide `d`.

If `delta=1`, then `a<b<=c`, so `d<0` and

```math
1\le d+r\le r-1<P.
```

If `delta=-1`, then `c<b<=a`, so `d>0` and

```math
-P<-(r-1)\le d-r\le-1.
```

Again divisibility by `P` is impossible. Therefore

```math
\boxed{
a\ne c
\quad\Longrightarrow\quad
v_a\ne v_c\pmod P.
}
\qquad[\text{Q.E.D.}]
```

In particular, the harmless phases are distinct.

## Exact Fourier Row Orthogonality

For harmless rows `a,c`, character orthogonality modulo `P` gives

```math
\begin{aligned}
(\mathsf A\mathsf A^*)_{a,c}
&=
\sum_{m\bmod P}
e^{2\pi i m(v_a-v_c)/P}\\
&=
\begin{cases}
P,&a=c,\\
0,&a\ne c.
\end{cases}
\end{aligned}
```

Hence

```math
\boxed{
\mathsf A\mathsf A^*=P I_h.
}
```

Since `C=C^*=C^2`,

```math
\boxed{
C\mathsf A\mathsf A^*C
=
PC.
}
\qquad[\text{Q.E.D.}]
```

Thus `C mathsf A` has singular value `sqrt(P)` with multiplicity `h-1` and
singular value zero in the constant row direction.

Equivalently, the frequency-side Gram matrix

```math
\mathsf G
=
\mathsf A^*C\mathsf A
```

has nonzero eigenvalue `P` with multiplicity `h-1`. Its entries are exactly
the centered phase Gram entries from the Inverse-Phase Gram Matrix property.

## The Sharp Generic Bound

For every coefficient vector `alpha` on the `P` frequencies,

```math
\boxed{
\|C\mathsf A\alpha\|_2^2
\le
P\|\alpha\|_2^2.
}
```

The constant `P` is sharp. Given any nonzero centered harmless-row vector
`z`, take

```math
\alpha=\frac1P\mathsf A^*z.
```

Then

```math
C\mathsf A\alpha=z,
\qquad
\|\alpha\|_2^2=\frac1P\|z\|_2^2,
```

so equality holds.

## Exact Return To Full-Shift Parseval

Consider the equal-fiber-length core of the Inverse-Phase Gram Matrix property. Put

```math
\alpha_m
=
\frac1P
\widehat g_0(m)D_\ell(m)
```

for nonzero `m`, and `alpha_0=0`. Then

```math
U=\|C\mathsf A\alpha\|_2^2.
```

The sharp operator bound gives

```math
\begin{aligned}
U
&\le
P\sum_{m\bmod P}|\alpha_m|^2\\
&=
\frac1P
\sum_{m\ne0}
|\widehat g_0(m)|^2|D_\ell(m)|^2\\
&=
\sum_{v\bmod P}|E_\ell(v)|^2.
\end{aligned}
```

The last line is exactly the full-shift Parseval energy from the CRT Fiber Translation property.
Thus the generic centered operator norm gives no improvement over the
full-shift bound.

## The One-Unit Fiber-Length Correction

The actual fiber lengths differ by at most one. Write

```math
\ell_a=\ell+\mathbf 1_{a\in L}
```

for some set of longer harmless fibers `L`, and let `R_L` be the diagonal row
mask of that set.

The extra last point in a long fiber contributes another phase matrix of the
form

```math
C R_L\mathsf A
```

times unit-modulus frequency factors. Since

```math
(C R_L\mathsf A)(C R_L\mathsf A)^*
=
P C R_L C,
```

and `R_L` is an orthogonal projection,

```math
\boxed{
\|C R_L\mathsf A\|_{\mathrm{op}}^2
\le P.
}
```

Therefore splitting off the one-unit length imbalance and applying only
operator norms still retains the period scale. The correction does not
create a generic local-population estimate.

## Consequence For Candidate #22

The centered Gram identity remains useful, but its value cannot be extracted
through a black-box spectral norm:

```math
\text{centering}
+\text{full Fourier orthogonality}
\Longrightarrow
\text{full-shift Parseval scale}.
```

A successful estimate must exploit that the actual coefficient vector is

```math
\widehat g_0(m)D_\ell(m),
```

where `hat(g_0)` has explicit CRT factorization and `D_ell` is an interval
multiplier. Entrywise absolute values, a generic operator norm, or a generic
large-sieve inequality all discard the required arithmetic alignment.

The remaining noncircular possibilities are:

1. a bilinear estimate coupling the CRT factors of `hat(g_0)` to the exact
   centered kernel from the Inverse-Phase Gram Matrix property; or
2. cancellation after the centered forms are summed with candidate #21's
   chain weights.

## Related

- [Harmless-class counts as translated CRT fibers](
  harmless-class-crt-translated-fibers.md
  )
- [Centered inverse-phase Gram matrix](
  centered-inverse-phase-gram-matrix.md
  )
- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
