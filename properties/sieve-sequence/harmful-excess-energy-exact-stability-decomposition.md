# Harmful-Excess Energy Has an Exact Stability Decomposition

**Status:** Mathematically proved conditioned-chain identity. Stainless
verification is not claimed.

## Meaning

The Terminal Harmful-Excess Energy property obtains the sharp lower bound

```math
E_b\ge\frac{(T-N_m)^2}{2W_-}
```

from weighted Cauchy--Schwarz. This property identifies the entire difference
between the two sides. It is exactly a positive weighted square measuring the
distance from the unique endpoint-constrained minimizing harmful-excess
profile.

The result turns the equality condition into a quantitative object. For an
extinct chain, any arithmetic obstruction to the abstract profile constructed
by the Integral Profile Attainment property appears as a positive stability remainder.

This is a lower-bound refinement. It does not upper-bound `E_b` and therefore
does not prove candidate #24 by itself.

## Setup

Use the conditioned-chain notation of the Weighted Deletion Conservation property and #66:

```math
a_i=1-\frac2{r_i},
\qquad
w_i=A_{i+1,m},
\qquad
w_{i-1}=a_iw_i,
```

```math
W_-=\sum_iw_{i-1}=\sum_iw_ia_i,
```

and

```math
E_b
=
\sum_iw_i\frac1{2a_i}b_i^2.
```

The exact weighted conservation law is

```math
\sum_iw_ib_i=T-N_m.
```

For brevity, define the endpoint discrepancy

```math
D=T-N_m.
```

## Endpoint-Constrained Minimizer

Define

```math
\boxed{
b_i^\star
=
\frac{a_iD}{W_-}.
}
```

It has the required weighted total because

```math
\begin{aligned}
\sum_iw_ib_i^\star
&=
\frac{D}{W_-}\sum_iw_ia_i\\
&=
\frac{D}{W_-}W_-\\
&=D.
\end{aligned}
```

Consequently,

```math
\boxed{
\sum_iw_i(b_i-b_i^\star)=0.
}
```

## Exact Square Completion

Expand the weighted squared distance:

```math
\begin{aligned}
\sum_iw_i\frac1{2a_i}(b_i-b_i^\star)^2
&=
\sum_iw_i\frac1{2a_i}b_i^2
-
\sum_iw_i\frac{b_i b_i^\star}{a_i}
+
\sum_iw_i\frac1{2a_i}(b_i^\star)^2.
\end{aligned}
```

The middle term is

```math
\begin{aligned}
\sum_iw_i\frac{b_i b_i^\star}{a_i}
&=
\frac{D}{W_-}\sum_iw_ib_i\\
&=
\frac{D^2}{W_-}.
\end{aligned}
```

The last term is

```math
\begin{aligned}
\sum_iw_i\frac1{2a_i}(b_i^\star)^2
&=
\frac{D^2}{2W_-^2}\sum_iw_ia_i\\
&=
\frac{D^2}{2W_-}.
\end{aligned}
```

Therefore

```math
\sum_iw_i\frac1{2a_i}(b_i-b_i^\star)^2
=
E_b-\frac{D^2}{2W_-},
```

or equivalently

```math
\boxed{
E_b
=
\frac{(T-N_m)^2}{2W_-}
+
\sum_iw_i\frac1{2a_i}
\left(
b_i-\frac{a_i(T-N_m)}{W_-}
\right)^2.
}
\qquad[\text{Q.E.D.}]
```

## Uniqueness

Every coefficient

```math
w_i\frac1{2a_i}
```

is strictly positive. Hence the stability remainder vanishes if and only if

```math
b_i=b_i^\star
=
\frac{a_i(T-N_m)}{W_-}
```

at every layer.

Thus `b^\star` is the unique real harmful-excess profile with weighted total
`T-N_m` that minimizes `E_b`.

## Extinction Form

If `N_m=0`, then `D=T`. Since

```math
T=N_0P_m,
\qquad
W_-=P_m\sum_i\frac1{P_i},
```

the minimizing profile becomes

```math
b_i^\star
=
\frac{a_iN_0}{\sum_j1/P_j}.
```

This is exactly the scaled integral equality profile constructed in property
#67. Therefore every extinct profile satisfies the identity

```math
\boxed{
E_b-\frac{T^2}{2W_-}
=
\sum_iw_i\frac1{2a_i}
\left(
b_i-b_i^\star
\right)^2.
}
```

The amount by which an extinct actual chain exceeds the conservation-only
threshold is precisely its weighted squared distance from the abstract
equality deletion profile.

## Arithmetic Interface

Suppose future CRT analysis proves that every realizable extinct chain obeys

```math
\sum_iw_i\frac1{2a_i}
\left(
b_i-b_i^\star
\right)^2
\ge \Gamma(Q)
```

for some explicit positive `Gamma(Q)`. Then extinction would force

```math
E_b
\ge
\frac{T^2}{2W_-}
+\Gamma(Q).
```

This would enlarge the energy range that certifies survival. The required
input cannot be a fact about abstract integral monotone populations, because
The Integral Profile Attainment property realizes zero remainder under all of those constraints. It must
exclude the equality proportions using actual first-hit residue geometry.

## Boundary

The stability identity is still a terminal lower bound under the extinction
alternative. It supplies neither:

1. an unconditional upper bound for the energy of an actual chain; nor
2. a positive value of `Gamma(Q)`.

Candidate #24 still requires a separate arithmetic upper bound. A future
positive stability gap would make such an upper bound easier to use, but it
would not replace it.

## Related Properties And Candidate

- [Weighted deletion conservation law](weighted-deletion-conservation-law.md)
- [Weighted harmful-excess energy is already terminal](
  weighted-harmful-excess-energy-is-terminal.md
  )
- [Integral population profiles attain the harmful-energy threshold](
  integral-population-profiles-attain-harmful-energy-threshold.md
  )
- [Weighted harmful-excess quadratic survival](
  ../../candidates/weighted-harmful-excess-quadratic-survival.md
  )

