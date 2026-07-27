# Accepted-Strike Divisor Activation Kernel

**Status:** Mathematically proved exact finite quadratic identity. Stainless
verification is not claimed.

## Meaning

Candidate #23's boundary error is a Möbius sum over every divisor of the
currently installed modulus. Expanding its weighted square appears to produce
a quadratic form over exponentially many divisor pairs.

Every divisor enters the boundary sum at one definite layer. Its coefficient
in an accepted-strike discrepancy then depends only on that activation time,
not on the divisor itself. The exponential divisor-pair kernel therefore
collapses exactly to an `(m+1) by (m+1)` kernel on activation shells.

The compressed kernel is a positive-semidefinite Gram matrix and all of its
entries are nonnegative. Hence the layer weights create no sign cancellation
by themselves. All remaining cancellation lies inside the signed Möbius
shell sums.

## Setup

Let

```math
P_{i+1}=P_ir_i,
\qquad
i=0,\ldots,m-1,
```

where the new primes `r_i` do not divide `P_i`. Fix a prime-square window and
write its centered divisor summand as

```math
\epsilon_Q(d)
=
\frac{[Q]_d-[Q^2]_d}{d}.
```

For every layer,

```math
E_i
=
\sum_{\substack{d\mid P_i\\d>1}}
\mu(d)\epsilon_Q(d).
```

Set

```math
q_i=1-\frac1{r_i},
\qquad
D_i=q_iE_i-E_{i+1},
```

and let

```math
c_i
=
w_i\frac{r_i}{2(r_i-2)}
>
0.
```

Candidate #23's quadratic budget is

```math
\mathcal E_D
=
\sum_{i=0}^{m-1}c_iD_i^2.
```

## Divisor Activation Time

For each divisor `d>1` of the final modulus `P_m`, define

```math
\tau(d)
=
\min\{t\in\{0,\ldots,m\}:d\mid P_t\}.
```

Thus

```math
d\mid P_i
\quad\Longleftrightarrow\quad
\tau(d)\le i.
```

Extend every `E_i` to the final divisor set:

```math
E_i
=
\sum_{\substack{d\mid P_m\\d>1}}
\mu(d)\epsilon_Q(d)
\mathbf 1_{\tau(d)\le i}.
```

Substitution into `D_i=q_iE_i-E_{i+1}` gives

```math
D_i
=
\sum_{\substack{d\mid P_m\\d>1}}
\mu(d)\epsilon_Q(d)\theta_i(\tau(d)),
```

where

```math
\boxed{
\theta_i(t)
=
\begin{cases}
-1/r_i,&t\le i,\\
-1,&t=i+1,\\
0,&t>i+1.
\end{cases}
}
```

Indeed:

- if `t<=i`, the divisor occurs in both boundary sums and has coefficient
  `q_i-1=-1/r_i`;
- if `t=i+1`, it occurs only in `E_{i+1}` and has coefficient `-1`;
- if `t>i+1`, it occurs in neither sum.

## Activation-Shell Sums

Define the signed shell sum

```math
Z_t
=
\sum_{\substack{d\mid P_m\\d>1\\\tau(d)=t}}
\mu(d)\epsilon_Q(d).
```

Then

```math
\boxed{
E_i=\sum_{t=0}^{i}Z_t
}
```

and

```math
\boxed{
D_i
=
-\frac1{r_i}\sum_{t=0}^{i}Z_t
-Z_{i+1}.
}
\qquad[\text{Q.E.D.}]
```

Thus the full divisor structure enters the chain only through the `m+1`
numbers `Z_0,...,Z_m`.

## Exact Quadratic Kernel

Expanding the weighted square gives

```math
\begin{aligned}
\mathcal E_D
&=
\sum_{i=0}^{m-1}
c_i
\left(
\sum_{t=0}^{m}\theta_i(t)Z_t
\right)^2\\
&=
\sum_{t=0}^{m}
\sum_{u=0}^{m}
\mathcal K(t,u)Z_tZ_u,
\end{aligned}
```

where

```math
\boxed{
\mathcal K(t,u)
=
\sum_{i=0}^{m-1}
c_i\theta_i(t)\theta_i(u).
}
```

Equivalently, before grouping divisors,

```math
\boxed{
\mathcal E_D
=
\sum_{\substack{d,e\mid P_m\\d,e>1}}
\mu(d)\mu(e)
\epsilon_Q(d)\epsilon_Q(e)
\mathcal K(\tau(d),\tau(e)).
}
```

This is the requested divisor-by-divisor kernel. It factors through activation
times.

## Closed Form Of The Kernel

By symmetry assume `0<=t<=u<=m`.

For `t=u=0`,

```math
\boxed{
\mathcal K(0,0)
=
\sum_{i=0}^{m-1}\frac{c_i}{r_i^2}.
}
```

For `t<u`, the first common nonzero layer is `i=u-1`; there the two
coefficients are `-1/r_{u-1}` and `-1`. At every later layer both coefficients
are `-1/r_i`. Therefore

```math
\boxed{
\mathcal K(t,u)
=
\frac{c_{u-1}}{r_{u-1}}
+
\sum_{i=u}^{m-1}\frac{c_i}{r_i^2},
\qquad
t<u.
}
```

For `t=u>=1`, the activation-layer coefficient is `-1` for both copies:

```math
\boxed{
\mathcal K(u,u)
=
c_{u-1}
+
\sum_{i=u}^{m-1}\frac{c_i}{r_i^2}.
}
```

The remaining entries follow from

```math
\mathcal K(t,u)=\mathcal K(u,t).
```

## Positivity And Its Limitation

The kernel is a Gram matrix:

```math
\mathcal K
=
\Theta^*
\operatorname{diag}(c_0,\ldots,c_{m-1})
\Theta.
```

Consequently,

```math
\boxed{
\mathcal K\succeq0.
}
```

Moreover, every `theta_i(t)` is nonpositive and every `c_i` is positive, so

```math
\boxed{
\mathcal K(t,u)\ge0
}
```

for all activation times.

The layer weights therefore do not create alternating kernel signs that could
cancel the Möbius factors automatically. The only signs remaining in the
quadratic form come from the shell sums `Z_t`.

This is still a substantial compression: candidate #23 no longer needs a
mean-square theorem over arbitrary divisor pairs. It needs control of the
signed activation-shell vector in this explicit positive kernel.

## Remaining Theorem

A useful continuation may prove either:

1. direct cancellation bounds for every shell sum `Z_t`;
2. a weighted bound for the vector `(Z_0,...,Z_m)` in the norm induced by
   `mathcal K`; or
3. cancellation after averaging this shell-kernel energy over future heads
   `Q`.

Taking absolute values inside each `Z_t` recreates exponential divisor mass
and must not be used.

## Related

- [Accepted-strike density as a Möbius boundary sum](
  accepted-strike-density-boundary-decomposition.md
  )
- [Accepted-strike error is a positive quadratic variation](
  accepted-strike-quadratic-variation.md
  )
- [Prime-square window boundary residue formula](
  prime-square-window-boundary-residue-formula.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
