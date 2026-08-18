# Harmless-Class Counts As Translated CRT Fibers

**Status:** Mathematically proved exact identities and strategy boundary.
Stainless verification is not claimed.

## Meaning

Fix the filters installed before a prime `r`. After writing a surviving
2-gap start in harmless class `a modulo r` as

```math
x=a+rt,
```

multiplication by the inverse of `r modulo P` removes every dependence on
`a` from the prior-filter condition. Each harmless-class count is therefore
the count of one common periodic CRT word in an interval translated by a
class-dependent phase.

The phases are almost equally spaced around the old period. This makes the
remaining theorem precise: candidate #22 needs an `L^2` discrepancy estimate
for a small, well-spaced family of translated interval sums of the same CRT
word.

The normal form does not itself supply that estimate. Parseval over all
translations still retains the complete-period population. A generic
large-sieve transfer based only on phase spacing has the same scale and does
not reach the desired local `M` normalization.

## Setup

Let `P` be the product of the primes installed before `r`, and assume

```math
P>r\ge5,
\qquad
\gcd(P,r)=1.
```

Let `s` be the canonical inverse of `r modulo P`:

```math
1\le s<P,
\qquad
rs\equiv1\pmod P.
```

There is an integer `k` such that

```math
rs=1+kP.
```

Because `1<=s<P`,

```math
1\le k<r.
```

Moreover,

```math
\gcd(k,r)=1,
```

since every common divisor of `k` and `r` would divide
`rs-kP=1`.

Fix an integer interval

```math
I=[A,B),
\qquad
A<B.
```

For a canonical residue `0<=a<r`, define

```math
\lambda_a
=
\left\lceil\frac{A-a}{r}\right\rceil,
\qquad
\mu_a
=
\left\lceil\frac{B-a}{r}\right\rceil.
```

Then the integers in `I` congruent to `a modulo r` are exactly

```math
x=a+rt,
\qquad
\lambda_a\le t<\mu_a.
```

Let

```math
g_r(u)
=
\mathbf 1_{\gcd((ru)(ru+2),P)=1},
```

viewed as a periodic word modulo `P`.

## Exact Translated-Fiber Identity

For every integer `t`,

```math
\begin{aligned}
a+rt
&\equiv
r(sa+t)
\pmod P
&&[\text{Since }rs\equiv1\pmod P].
\end{aligned}
```

The same congruence holds after adding `2`. Therefore

```math
\gcd((a+rt)(a+rt+2),P)=1
```

if and only if

```math
g_r(sa+t)=1.
```

Let `d_a` be the number of starts in `I` that lie in class `a modulo r`,
survive every prior filter, and also survive `r`. For a harmless class

```math
a\notin\{0,r-2\},
```

survival of `r` is automatic. Hence

```math
\boxed{
d_a
=
\sum_{t=\lambda_a}^{\mu_a-1}g_r(sa+t)
=
\sum_{u=\lambda_a+sa}^{\mu_a+sa-1}g_r(u).
}
\qquad[\text{Q.E.D.}]
```

Thus all harmless classes sample one common word. Only the interval length

```math
\ell_a=\mu_a-\lambda_a
```

and translated phase

```math
v_a=\lambda_a+sa\pmod P
```

depend on `a`.

Because residue classes partition an interval as evenly as possible,

```math
\ell_a
\in
\left\{
\left\lfloor\frac{B-A}{r}\right\rfloor,
\left\lceil\frac{B-A}{r}\right\rceil
\right\}.
```

In particular, any two fiber lengths differ by at most one.

## The Translation Phases Are Well Spaced

Write

```math
A=qr+b,
\qquad
0\le b<r.
```

Then

```math
\lambda_a
=
q+\mathbf 1_{a<b},
```

so the non-inverse part of `v_a` changes by at most one between any two
classes.

For distinct residues `a,c`, put `h=a-c`. Then `0<|h|<r`. Because
`gcd(k,r)=1`, the canonical residue

```math
j=[kh]_r
```

lies in `{1,...,r-1}`. From `rs=1+kP`,

```math
sh
\equiv
\frac{h+jP}{r}
\pmod P.
```

The representative on the right lies strictly between `0` and `P`, and both
its distances to the endpoints are at least

```math
\frac{P-r+1}{r}.
```

Let `dist_P` denote cyclic distance modulo `P`. Since
`lambda_a-lambda_c` has absolute value at most one,

```math
\boxed{
\operatorname{dist}_P(v_a,v_c)
\ge
\frac{P-r+1}{r}-1.
}
```

The harmless phases are therefore an almost equally spaced subset of the old
period, with spacing on the order of `P/r`.

## Exact Discrepancy Form

Let

```math
G
=
\#\{u\pmod P:g_r(u)=1\},
\qquad
\rho=\frac GP.
```

For a length `ell` and phase `v`, define the centered interval sum

```math
E_\ell(v)
=
\sum_{j=0}^{\ell-1}\bigl(g_r(v+j)-\rho\bigr).
```

The translated-fiber identity becomes

```math
d_a
=
\rho\ell_a+E_{\ell_a}(v_a).
```

Let `H` be the `r-2` harmless residues and write

```math
\overline z
=
\frac1{r-2}
\sum_{a\in H}
\left(\rho\ell_a+E_{\ell_a}(v_a)\right).
```

Candidate #22's harmless energy is exactly

```math
\boxed{
U
=
\sum_{a\in H}
\left(
\rho\ell_a+E_{\ell_a}(v_a)-\overline z
\right)^2.
}
```

This is an exact translated-interval `L^2` discrepancy problem. The
deterministic length variation is at most one; the open arithmetic content is
the joint behavior of the centered sums `E_{\ell_a}(v_a)`.

## Why Full-Shift Parseval Still Has The Wrong Scale

For fixed `ell`, let

```math
\widehat g_0(m)
=
\sum_{u\bmod P}
\bigl(g_r(u)-\rho\bigr)e^{-2\pi imu/P}
```

and

```math
D_\ell(m)
=
\sum_{j=0}^{\ell-1}e^{2\pi imj/P}.
```

Finite Parseval gives the exact full-shift identity

```math
\boxed{
\sum_{v\bmod P}|E_\ell(v)|^2
=
\frac1P
\sum_{m\ne0}
|\widehat g_0(m)|^2|D_\ell(m)|^2.
}
```

Using only `|D_ell(m)|<=ell` and Parseval for `g_r-rho` yields

```math
\sum_{v\bmod P}|E_\ell(v)|^2
\le
\ell^2G(1-\rho).
```

This is normalized by the complete-period population `G`, not by the actual
local survivor population `M`.

The phase-spacing lemma permits a standard large-sieve estimate for the
sampled values `E_ell(v_a)`. But the trigonometric polynomial has frequencies
through the full modulus `P`. Its large-sieve factor is consequently of size

```math
P+\operatorname{spacing}^{-1}
\asymp
P+r
\asymp
P,
```

so after Fourier normalization it remains at the scale of the full-shift
Parseval quantity. Phase spacing alone does not convert the bound to `O(M)`.

## Consequence For Candidate #22

The translated-fiber identity gives a more precise missing theorem:

> Bound the variance of the centered CRT-word interval sums at the specific
> inverse phases `v_a`, after subtracting their harmless-class mean, by the
> local survivor scale.

Complete-period uniformity, unrestricted Parseval, and a generic large-sieve
sampling inequality do not prove this. A successful argument must use more
of the explicit CRT spectrum, cancellation between the selected phases, or a
new physical-space dispersion estimate tailored to this word.

## Related

- [Complete-period uniformity of harmless 2-gap classes](
  complete-period-harmless-class-uniformity.md
  )
- [Harmless energy as spectral excess above the two-class floor](
  harmless-energy-spectral-excess.md
  )
- [Short-interval localization destroys prime conductor decay](
  short-interval-localization-destroys-prime-conductor-decay.md
  )
- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
