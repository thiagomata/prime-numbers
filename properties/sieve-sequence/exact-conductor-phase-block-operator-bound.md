# Exact-Conductor Phase-Block Operator Bound

**Status:** Mathematically proved exact finite block estimate and strategy
boundary. Stainless verification is not claimed.

## Meaning

The full centered inverse-phase operator has sharp squared norm `P`, which is
too large for candidate #22. Restricting the Fourier frequencies to one exact
CRT conductor changes the scale.

Characters of conductor `q` see each inverse phase only modulo `q`. The
phases form two affine runs modulo `q`, and no residue can occur too many
times. This gives a conductor-block squared operator norm of order `r+q`,
rather than `P`.

This is a genuine arithmetic improvement. It does not yet prove candidate
#22 because the different conductor blocks are not orthogonal after sampling.
Combining them by triangle inequality introduces an unusable square-root
divisor sum.

## Setup

Use the inverse phases from the properties from CRT Fiber Translation through Phase-Operator Norm Bound:

```math
P>r\ge5,
\qquad
rs\equiv1\pmod P,
\qquad
A=ur+b,
\qquad
0\le b<r,
```

and

```math
v_a=u+sa+\mathbf 1_{a<b}.
```

Let

```math
H
=
\{0,1,\ldots,r-1\}\setminus\{0,r-2\},
\qquad
h=r-2,
```

and let `C` subtract the mean across `H`.

Fix a divisor

```math
q\mid P.
```

Since `s` is invertible modulo `P`, it is also invertible modulo `q`.

## Phase Multiplicity Modulo A Conductor

For a residue `y modulo q`, define

```math
n_y
=
\#\{a\in H:v_a\equiv y\pmod q\},
\qquad
\mu_q=\max_{y\bmod q}n_y.
```

On the first range `0<=a<b`,

```math
v_a=u+1+sa.
```

Because multiplication by `s` permutes the residues modulo `q`, every residue
occurs at most

```math
\left\lceil\frac bq\right\rceil
```

times in this range.

On the second range `b<=a<r`,

```math
v_a=u+sa,
```

so every residue occurs at most

```math
\left\lceil\frac{r-b}{q}\right\rceil
```

times. Removing the two harmful values of `a` cannot increase a
multiplicity. Therefore

```math
\boxed{
\mu_q
\le
\left\lceil\frac bq\right\rceil
+
\left\lceil\frac{r-b}{q}\right\rceil
\le
\left\lceil\frac rq\right\rceil+1.
}
```

In particular,

```math
\boxed{
q\mu_q<r+2q.
}
```

## Complete Conductor-`q` Phase Matrix

Let `mathsf B_q` be the `h by q` matrix containing every additive character
modulo `q`:

```math
(\mathsf B_q)_{a,m}
=
e^{2\pi i m v_a/q},
\qquad
a\in H,
\quad
m\pmod q.
```

Character orthogonality gives

```math
(\mathsf B_q\mathsf B_q^*)_{a,c}
=
\begin{cases}
q,&v_a\equiv v_c\pmod q,\\
0,&v_a\not\equiv v_c\pmod q.
\end{cases}
```

After grouping harmless rows with the same phase, this matrix is a direct sum
of blocks

```math
qJ_{n_y},
```

where `J_(n_y)` is the all-ones matrix of size `n_y`. Its largest eigenvalue
is `q mu_q`. Hence

```math
\boxed{
\|\mathsf B_q\|_{\mathrm{op}}^2
=
q\mu_q.
}
```

Since `C` is an orthogonal projection,

```math
\boxed{
\|C\mathsf B_q\|_{\mathrm{op}}^2
\le
q\mu_q
<
r+2q.
}
\qquad[\text{Q.E.D.}]
```

## Restriction To Exact Conductor

An additive character modulo `P` has exact conductor `q` precisely when its
frequency has the form

```math
m=\frac Pq\,t,
\qquad
\gcd(t,q)=1.
```

At an inverse phase,

```math
e^{2\pi i m v_a/P}
=
e^{2\pi i t v_a/q}.
```

Thus the exact-conductor phase matrix is a column submatrix of `mathsf B_q`.
Deleting columns cannot increase the operator norm, so the same bound applies
to the exact-conductor block:

```math
\boxed{
\|C\mathsf A_q\|_{\mathrm{op}}^2
\le
q\mu_q
<
r+2q.
}
```

This is the conductor-scale replacement for the Phase-Operator Norm Bound property's full squared norm
`P`.

## Composition With The CRT Coefficient Mass

Let `G` be the complete-period population of the CRT word. The existing exact
conductor identity is

```math
\sum_{\operatorname{cond}(m)=q}
|\widehat g_0(m)|^2
=
G^2a(q),
\qquad
a(q)
=
\prod_{p\mid q}\frac2{p-2}.
```

For a common fiber length `ell`, a nontrivial character of conductor `q`
cancels on complete `q`-blocks. Therefore

```math
|D_\ell(m)|
\le
\min(\ell,q).
```

Define the exact-conductor coefficient vector

```math
\alpha_q(m)
=
\frac1P
\widehat g_0(m)D_\ell(m).
```

Then

```math
\|\alpha_q\|_2^2
\le
\frac{G^2}{P^2}
\min(\ell,q)^2a(q).
```

The centered contribution of this one conductor satisfies

```math
\boxed{
\|C\mathsf A_q\alpha_q\|_2
\le
\frac GP
\min(\ell,q)
\sqrt{q\mu_q\,a(q)}.
}
```

This is an explicit conductor-sensitive block estimate.

## Why Triangle Composition Does Not Close The Proof

The full centered vector is the sum of the exact-conductor block vectors.
Applying the triangle inequality gives

```math
\boxed{
\sqrt U
\le
\frac GP
\sum_{\substack{q\mid P\\q>1}}
\min(\ell,q)
\sqrt{q\mu_q\,a(q)}.
}
```

This bound is explicit, but the square-root divisor weights do not have the
benign normalization

```math
\sum_{q\mid P}a(q)=\frac PG.
```

For example,

```math
\sum_{q\mid P}\sqrt{a(q)}
=
\prod_{p\mid P}
\left(
1+\sqrt{\frac2{p-2}}
\right).
```

This product grows much faster than the original conductor normalization.
Including `sqrt(q mu_q)` and `min(ell,q)` only increases the triangle bound.
Thus conductor blocking followed by triangle inequality loses the arithmetic
gain before it reaches the local-population scale.

This does not refute the conductor-block strategy. It proves that the blocks
must be recombined with cross-conductor cancellation or an almost-orthogonal
square-sum theorem. Absolute block summation is not sufficient.

## Remaining Algebraic Test

The next exact question is whether distinct conductor blocks have a useful
centered cross-Gram bound:

```math
\mathsf A_q^*C\mathsf A_{q'}.
```

Its entries are already known from the Inverse-Phase Gram Matrix property, but the conductor
restrictions may create additional cancellation after summation over the
primitive frequencies in each block.

A useful theorem must combine blocks closer to a square sum than to a
triangle sum and must retain the interval multipliers. Otherwise it returns
to the complete-period scale.

## Related

- [Fourier bound for two-gap correlation prefixes](
  fourier-two-gap-correlation-prefix-bound.md
  )
- [Centered inverse-phase Gram matrix](
  centered-inverse-phase-gram-matrix.md
  )
- [Centered phase operator norm boundary](
  centered-phase-operator-norm-boundary.md
  )
- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
