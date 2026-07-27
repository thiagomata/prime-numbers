# Centered Ramanujan Cross-Conductor Geometry

**Status:** Mathematically proved exact finite identities and exact
counterexample to universal cross-conductor orthogonality. Stainless
verification is not claimed.

## Meaning

Property #46 improves the inverse-phase operator norm after restricting to
one exact Fourier conductor. To combine those blocks by a square sum, one
might hope that distinct conductor blocks become orthogonal after subtracting
the harmless-class mean.

The exact cross-block geometry is governed by Ramanujan sums. It can be
written as a finite centered trace, but distinct blocks are not orthogonal in
general. This failure occurs even for coprime conductors.

Therefore multiplicativity of the conductor weights does not by itself
provide the missing square-sum theorem. Any useful recombination must prove a
weighted bilinear estimate for the particular CRT coefficients and interval
multipliers.

## Setup

Use the harmless inverse phases

```math
v_a=u+sa+\mathbf 1_{a<b},
\qquad
a\in H,
\qquad
|H|=h=r-2
```

from properties #43--#46. Let `C` be the orthogonal projection that subtracts
the mean across `H`.

For an exact conductor `q|P`, define the primitive-character phase matrix

```math
(\mathsf A_q)_{a,t}
=
e^{2\pi i t v_a/q},
\qquad
\gcd(t,q)=1.
```

Define the Ramanujan sum

```math
c_q(n)
=
\sum_{\substack{t\bmod q\\\gcd(t,q)=1}}
e^{2\pi i tn/q}.
```

## Exact Ramanujan Row Kernel

For harmless rows `a,c`,

```math
\begin{aligned}
(\mathsf A_q\mathsf A_q^*)_{a,c}
&=
\sum_{\substack{t\bmod q\\\gcd(t,q)=1}}
e^{2\pi i t(v_a-v_c)/q}\\
&=
c_q(v_a-v_c).
\end{aligned}
```

Let

```math
(\mathsf R_q)_{a,c}
=
c_q(v_a-v_c).
```

Then

```math
\boxed{
\mathsf A_q\mathsf A_q^*
=
\mathsf R_q.
}
\qquad[\text{Q.E.D.}]
```

This is the exact primitive-character refinement of the all-character phase
multiplicity matrix in property #46.

## Exact Centered Cross-Block Identity

For two conductors `q,q'|P`, set

```math
\mathsf X_{q,q'}
=
\mathsf A_q^*C\mathsf A_{q'}.
```

Its squared Hilbert--Schmidt norm is

```math
\begin{aligned}
\|\mathsf X_{q,q'}\|_{\mathrm{HS}}^2
&=
\operatorname{tr}
\left(
\mathsf X_{q,q'}\mathsf X_{q,q'}^*
\right)\\
&=
\operatorname{tr}
\left(
\mathsf A_q^*C
\mathsf A_{q'}\mathsf A_{q'}^*
C\mathsf A_q
\right)\\
&=
\operatorname{tr}
\left(
C\mathsf R_{q'}C\mathsf R_q C
\right).
\end{aligned}
```

Therefore

```math
\boxed{
\|\mathsf A_q^*C\mathsf A_{q'}\|_{\mathrm{HS}}^2
=
\operatorname{tr}
\left(
C\mathsf R_qC\mathsf R_{q'}C
\right).
}
\qquad[\text{Q.E.D.}]
```

The right-hand side is a completely explicit integer-rational expression
after the mean projection is inserted.

## Exact Failure Of Distinct-Conductor Orthogonality

Take

```math
P=30,
\qquad
r=7,
\qquad
A=11.
```

The canonical inverse of `7 modulo 30` is

```math
s=13,
```

and

```math
A=1\cdot7+4.
```

The harmless classes are

```math
H=\{1,2,3,4,6\},
```

and their phases modulo `30` are

```math
(v_a)_{a\in H}
=
(15,28,11,23,19).
```

Using

```math
c_q(n)
=
\mu\left(\frac q{\gcd(q,n)}\right)
\frac{\varphi(q)}
{\varphi\left(q/\gcd(q,n)\right)}
```

to evaluate the two Ramanujan matrices exactly gives

```math
\boxed{
\|\mathsf A_2^*C\mathsf A_3\|_{\mathrm{HS}}^2
=
\frac{168}{25}
>
0.
}
```

Thus even coprime distinct conductors are not centered-orthogonal.

The interaction can also remain a substantial fraction of the separate block
energies. In the same example,

```math
\|\mathsf A_5^*C\mathsf A_{30}\|_{\mathrm{HS}}^2
=
\frac{798}{5},
```

while

```math
\|\mathsf A_5^*C\mathsf A_5\|_{\mathrm{HS}}^2
=
114,
\qquad
\|\mathsf A_{30}^*C\mathsf A_{30}\|_{\mathrm{HS}}^2
=
\frac{6406}{25}.
```

The squared normalized Hilbert--Schmidt coherence is therefore

```math
\boxed{
\frac{
\|\mathsf A_5^*C\mathsf A_{30}\|_{\mathrm{HS}}^4
}{
\|\mathsf A_5^*C\mathsf A_5\|_{\mathrm{HS}}^2
\|\mathsf A_{30}^*C\mathsf A_{30}\|_{\mathrm{HS}}^2
}
=
\frac{2793}{3203}.
}
```

This exact example rules out a generic small-coherence claim based only on
distinctness or coprimality of the conductors.

## Consequence For Candidate #22

The single-conductor gain from property #46 is real, but the conductor blocks
cannot be recombined by any of the following generic shortcuts:

1. exact orthogonality of distinct conductors;
2. orthogonality restricted to coprime conductors;
3. a uniformly small unweighted Hilbert--Schmidt coherence.

This does not refute a weighted bilinear theorem. Candidate #22 uses the
particular vectors

```math
\widehat g_0(m)D_\ell(m)
```

inside each conductor block, not arbitrary unit vectors. A remaining theorem
would have to exploit cancellation from these CRT coefficients, the interval
multipliers, or the chain weights.

Further finite Fourier rearrangement without such coefficient information
will only reproduce the separate block norms or their large cross
interactions.

## Related

- [Centered inverse-phase Gram matrix](
  centered-inverse-phase-gram-matrix.md
  )
- [Centered phase operator norm boundary](
  centered-phase-operator-norm-boundary.md
  )
- [Exact-conductor phase-block operator bound](
  exact-conductor-phase-block-operator-bound.md
  )
- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
