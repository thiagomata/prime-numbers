# Accepted-Strike Error Is A Positive Quadratic Variation

**Status:** Mathematically proved exact identity. Stainless verification is not
claimed.

## Meaning

Accepted-strike discrepancies telescope linearly because each discrepancy is
an adjacent difference of centered boundary errors. Candidate #23 needs the
weighted sum of their squares, however.

Expanding that square gives an exact discrete quadratic-variation identity.
Under the two-endpoint survival weights used by candidate #21, every interior
mass coefficient is strictly positive. Thus squaring does not preserve the
linear cancellation: it creates a genuine positive energy.

## Setup

Let

```math
5\le r_0<r_1<\cdots<r_{m-1}
```

be increasing odd primes. Define

```math
a_i=1-\frac2{r_i},
\qquad
q_i=1-\frac1{r_i},
```

```math
w_i
=
\prod_{j=i+1}^{m-1}a_j,
\qquad
c_i
=
w_i\frac{r_i}{2(r_i-2)}.
```

The weights satisfy

```math
w_{i-1}=a_iw_i
```

for `1<=i<m`.

Let `E_0,...,E_m` be the centered accepted-anchor boundary errors from the
accepted-strike boundary property, and define

```math
D_i
=
q_iE_i-E_{i+1}
=
H_i-\frac{A_i}{r_i}.
```

Candidate #23's denominator-free quadratic budget is

```math
\mathcal E_D
=
\sum_{i=0}^{m-1}c_iD_i^2.
```

## One-Step Square Identity

For arbitrary real `x,y` and `0<q<1`,

```math
\begin{aligned}
(qx-y)^2
&=
q(x-y)^2
+
(1-q)(y^2-qx^2).
\end{aligned}
```

Indeed, the right-hand side expands to

```math
qx^2-2qxy+qy^2
+
(1-q)y^2
-
q(1-q)x^2
=
q^2x^2-2qxy+y^2.
```

Therefore

```math
\boxed{
D_i^2
=
q_i(E_i-E_{i+1})^2
+
(1-q_i)
\left(
E_{i+1}^2-q_iE_i^2
\right).
}
\qquad[\text{Q.E.D.}]
```

## Chain Decomposition

Multiply the one-step identity by `c_i` and sum. Reindexing the positive
`E_{i+1}^2` terms gives

```math
\boxed{
\begin{aligned}
\mathcal E_D
={}&
\sum_{i=0}^{m-1}
c_iq_i(E_i-E_{i+1})^2\\
&+
c_{m-1}(1-q_{m-1})E_m^2\\
&+
\sum_{i=1}^{m-1}\gamma_iE_i^2\\
&-
c_0q_0(1-q_0)E_0^2,
\end{aligned}
}
```

where

```math
\gamma_i
=
c_{i-1}(1-q_{i-1})
-
c_iq_i(1-q_i).
```

This is an exact identity.

## Positivity Of Every Interior Coefficient

Using the definitions and `w_{i-1}=a_iw_i`,

```math
c_{i-1}(1-q_{i-1})
=
\frac{w_i(r_i-2)}
{2r_i(r_{i-1}-2)},
```

while

```math
c_iq_i(1-q_i)
=
\frac{w_i(r_i-1)}
{2r_i(r_i-2)}.
```

Hence

```math
\gamma_i
=
\frac{w_i}{2r_i}
\left(
\frac{r_i-2}{r_{i-1}-2}
-
\frac{r_i-1}{r_i-2}
\right).
```

Increasing odd primes satisfy

```math
r_{i-1}\le r_i-2.
```

It is therefore enough to compare

```math
\frac{r_i-2}{r_i-4}
\quad\text{and}\quad
\frac{r_i-1}{r_i-2}.
```

Cross multiplication gives

```math
(r_i-2)^2-(r_i-1)(r_i-4)=r_i>0.
```

Thus

```math
\boxed{
\gamma_i>0
}
```

for every interior index `1<=i<m`.

## Consequence

All terms in the chain decomposition are nonnegative except the explicit
initial boundary term. Equivalently,

```math
\boxed{
\begin{aligned}
\mathcal E_D
&+
c_0q_0(1-q_0)E_0^2\\
&=
\sum_{i=0}^{m-1}
c_iq_i(E_i-E_{i+1})^2
+
c_{m-1}(1-q_{m-1})E_m^2
+
\sum_{i=1}^{m-1}\gamma_iE_i^2.
\end{aligned}
}
```

The right-hand side is a positive quadratic energy. It measures:

1. variation between adjacent boundary errors;
2. the terminal boundary error;
3. positive interior boundary-error mass.

## Why Linear Telescoping Does Not Prove Candidate #23

The signed first powers satisfy a linear conservation law under one-anchor
weights. The squared discrepancies instead produce the positive energy above.
There is no cancellation left to discard after squaring.

This property therefore does not upper-bound `mathcal E_D`. It shows exactly
what a successful upper bound must control: the variation and magnitude of the
centered boundary-error sequence, relative to the known initial term.

Using only the linear telescope as an upper bound for candidate #23 is
invalid.

## Limitation

The identity gives structural positivity, not a numerical estimate. It can
convert an upper bound on `mathcal E_D` into bounds on boundary variation, but
candidate #23 needs the reverse direction.

A future proof requires new information about `E_i`, such as a direct
boundary-error bound with cancellation, a recurrence limiting its quadratic
growth, or a special property of the square-window endpoints. None follows
from this algebra alone.

## Related

- [Accepted-strike density as a Möbius boundary sum](
  accepted-strike-density-boundary-decomposition.md
  )
- [Endpoint density contracts accepted-strike discrepancy](
  endpoint-density-contracts-strike-discrepancy.md
  )
- [Weighted composition of endpoint and strike-density errors](
  weighted-scalar-error-composition.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
