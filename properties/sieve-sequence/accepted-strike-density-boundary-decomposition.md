# Accepted-Strike Density As A Möbius Boundary Sum

**Status:** Mathematically proved exact identity. Stainless verification is not
claimed.

## Meaning

Before installing a new prime filter, accepted values are the integers
coprime to the product of the old filters. Striking the new residue class is
therefore exactly the same as counting old-accepted integers in a scaled
interval.

Finite inclusion--exclusion separates this strike count into the expected
`1/r` bulk density and an explicit signed boundary sum. Consequently,
candidate #23 does not require a new main-term calculation. It requires
cancellation in the boundary sum that the triangle inequality destroys.

## Setup

Let `P` be a positive squarefree integer, let `r>1` satisfy

```math
\gcd(r,P)=1,
```

and let `L<U` be integers. Define the old-accepted count

```math
C_P(L,U)
=
\#\{n\in\mathbb Z:L\le n<U,\ \gcd(n,P)=1\}.
```

Write

```math
A=C_P(L,U)
```

and let the new filter's accepted strike count be

```math
H
=
\#\{
n\in\mathbb Z:
L\le n<U,\ 
\gcd(n,P)=1,\ 
r\mid n
\}.
```

Set

```math
\ell=U-L,
\qquad
L_r=\left\lceil\frac Lr\right\rceil,
\qquad
U_r=\left\lceil\frac Ur\right\rceil,
\qquad
\ell_r=U_r-L_r.
```

## Exact Scaled-Interval Identity

Every struck integer has a unique form `n=rk`. Since `gcd(r,P)=1`,

```math
\gcd(n,P)=1
\quad\Longleftrightarrow\quad
\gcd(k,P)=1.
```

The interval condition is equivalent to

```math
L_r\le k<U_r.
```

Therefore

```math
\boxed{
H=C_P(L_r,U_r).
}
\qquad[\text{Q.E.D.}]
```

## Centered Inclusion--Exclusion

For every divisor `d` of `P`, the number of its multiples in `[L,U)` is

```math
\left\lceil\frac Ud\right\rceil
-
\left\lceil\frac Ld\right\rceil.
```

Finite inclusion--exclusion gives

```math
C_P(L,U)
=
\sum_{d\mid P}
\mu(d)
\left(
\left\lceil\frac Ud\right\rceil
-
\left\lceil\frac Ld\right\rceil
\right).
```

Define the centered boundary sum

```math
E_P(L,U)
=
\sum_{d\mid P}
\mu(d)
\left(
\left\lceil\frac Ud\right\rceil
-
\left\lceil\frac Ld\right\rceil
-
\frac{\ell}{d}
\right).
```

Using

```math
\sum_{d\mid P}\frac{\mu(d)}d
=
\frac{\varphi(P)}P,
```

we obtain

```math
\boxed{
C_P(L,U)
=
\ell\frac{\varphi(P)}P
+
E_P(L,U).
}
```

Apply the same identity to `[L_r,U_r)`. The scaled-interval identity then
gives

```math
H
=
\ell_r\frac{\varphi(P)}P
+
E_P(L_r,U_r).
```

Subtracting `A/r` proves the exact strike-discrepancy decomposition

```math
\boxed{
H-\frac Ar
=
\left(\ell_r-\frac{\ell}{r}\right)
\frac{\varphi(P)}P
+
E_P(L_r,U_r)
-
\frac1rE_P(L,U).
}
\qquad[\text{Q.E.D.}]
```

If `A>0`, candidate #23's density error is consequently

```math
\boxed{
\varepsilon
=
\frac HA-\frac1r
=
\frac1A
\left[
\left(\ell_r-\frac{\ell}{r}\right)
\frac{\varphi(P)}P
+
E_P(L_r,U_r)
-
\frac1rE_P(L,U)
\right].
}
```

## What The Triangle Inequality Gives

For every `d>1`,

```math
\left|
\left\lceil\frac Ud\right\rceil
-
\left\lceil\frac Ld\right\rceil
-
\frac{\ell}{d}
\right|
<1.
```

The `d=1` summand is zero. Hence

```math
|E_P(L,U)|<\tau(P)-1.
```

Also,

```math
\left|\ell_r-\frac{\ell}{r}\right|<1.
```

The exact decomposition therefore gives the unconditional but crude estimate

```math
\boxed{
\left|H-\frac Ar\right|
<
\frac{\varphi(P)}P
+
\left(1+\frac1r\right)(\tau(P)-1).
}
```

Because `P` is squarefree with `omega(P)` prime factors,

```math
\tau(P)=2^{\omega(P)}.
```

Thus the black-box triangle inequality is exponentially too large as the
number of installed filters grows. It does not prove candidate #23.

## Exact Chain Recurrence

Now fix one interval `[L,U)` and let the old-filter moduli grow by

```math
P_{i+1}=P_ir_i,
\qquad
\gcd(P_i,r_i)=1.
```

Write

```math
A_i=C_{P_i}(L,U),
\qquad
\rho_i=\frac{\varphi(P_i)}{P_i},
\qquad
E_i=A_i-\ell\rho_i.
```

Let `H_i` be the number of `P_i`-accepted anchors struck by `r_i`. Filtering
removes exactly those anchors, so

```math
A_{i+1}=A_i-H_i.
```

Also,

```math
\rho_{i+1}
=
\left(1-\frac1{r_i}\right)\rho_i.
```

Therefore

```math
\begin{aligned}
H_i-\frac{A_i}{r_i}
&=
\left(1-\frac1{r_i}\right)A_i-A_{i+1}\\
&=
\left(1-\frac1{r_i}\right)
\left(\ell\rho_i+E_i\right)
-
\left(\ell\rho_{i+1}+E_{i+1}\right)\\
&=
\boxed{
\left(1-\frac1{r_i}\right)E_i-E_{i+1}.
}
\end{aligned}
\qquad[\text{Q.E.D.}]
```

Set

```math
v_i
=
\prod_{j=i+1}^{m-1}
\left(1-\frac1{r_j}\right).
```

Unrolling the recurrence gives the exact linear conservation law

```math
\boxed{
\sum_{i=0}^{m-1}
v_i
\left(
H_i-\frac{A_i}{r_i}
\right)
=
E_0
\prod_{j=0}^{m-1}
\left(1-\frac1{r_j}\right)
-
E_m.
}
```

This is genuine cross-layer cancellation, but it does not prove candidate
#23's quadratic budget. Candidate #21 uses the different two-endpoint weights

```math
w_i
=
\prod_{j=i+1}^{m-1}
\left(1-\frac2{r_j}\right)
```

and requires control of squared errors. Squaring the one-step recurrence
introduces cross terms `E_iE_{i+1}` whose sign is not controlled by the linear
telescope.

## Consequence For The Proof Strategy

The bulk terms are already exact. The only possible improvement over the
crude bound must use cancellation among the signs `mu(d)`, correlation
between adjacent boundary errors, averaging across the chain weights, or
extra structure in the interval endpoints.

In particular, complete-period uniformity alone is insufficient: it removes
the boundary sums only when the interval is a union of complete periods. The
conditioned square window is far shorter than the primorial period.

The identity is noncircular. Neither its statement nor its proof assumes a
positive late-layer 2-gap population.

## Boundary Of Applicability

This property counts all old-accepted anchors in one integer interval.
Candidate #13 may trim anchors whose fixed-radius neighborhoods cross the
window boundary. Transferring the identity to that convention requires an
explicit endpoint-correction lemma. The correction must be counted rather
than silently absorbed into `E_P`.

The property also supplies no cancellation estimate for `E_P`. That is the
remaining content of candidate #23.

## Related

- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
- [Exact accepted local filter strikes](
  exact-accepted-local-filter-strikes.md
  )
- [Two endpoint observables separate harmful excess and imbalance](
  two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
