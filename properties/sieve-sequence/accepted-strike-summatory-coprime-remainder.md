# Accepted-Strike Summatory Coprime Remainder

**Status:** Mathematically proved exact identity and strategy boundary.
Stainless verification is not claimed.

## Meaning

The Strike CRT Lift-Index property rewrites accepted-strike discrepancy as a bounded lift-index
Möbius transform. Summing the quotient parts shows that this transform is
exactly a dilation remainder for the summatory coprime-counting function.

This gives a clean analytic name to candidate #23's missing theorem. It does
not create a new elementary bound: the lift transform and the original strike
discrepancy are two exact coordinate systems for the same remainder.

## Setup

For squarefree `P`, define

```math
F_P(X)
=
\#\{1\le n\le X:\gcd(n,P)=1\}
```

for `X>=0`. Finite inclusion--exclusion gives

```math
F_P(X)
=
\sum_{e\mid P}
\mu(e)\left\lfloor\frac Xe\right\rfloor.
```

For `r` coprime to `P`, define

```math
T_{P,r}(x)
=
\sum_{e\mid P}
\mu(e)
\left[
\left\lfloor\frac{x-1}{e}\right\rfloor
\right]_r^{(0)}.
```

## Exact Dilation-Remainder Identity

Use

```math
[n]_r^{(0)}
=
n-r\left\lfloor\frac nr\right\rfloor.
```

Then

```math
\begin{aligned}
T_{P,r}(x)
&=
\sum_{e\mid P}\mu(e)
\left\lfloor\frac{x-1}{e}\right\rfloor\\
&\quad
-r\sum_{e\mid P}\mu(e)
\left\lfloor
\frac1r
\left\lfloor\frac{x-1}{e}\right\rfloor
\right\rfloor.
\end{aligned}
```

The nested floor satisfies

```math
\left\lfloor
\frac1r
\left\lfloor\frac{x-1}{e}\right\rfloor
\right\rfloor
=
\left\lfloor\frac{x-1}{re}\right\rfloor
=
\left\lfloor
\frac{
\left\lfloor(x-1)/r\right\rfloor
}{e}
\right\rfloor.
```

Applying the inclusion--exclusion formula to both sums proves

```math
\boxed{
T_{P,r}(x)
=
F_P(x-1)
-
rF_P\left(
\left\lfloor\frac{x-1}{r}\right\rfloor
\right).
}
\qquad[\text{Q.E.D.}]
```

## Exact Form Of Candidate #23

The Strike CRT Lift-Index property gives

```math
\mathcal M_i(Q)
=
T_{P_i,r_i}(Q)
-
T_{P_i,r_i}(Q^2).
```

Hence

```math
\boxed{
\begin{aligned}
\mathcal M_i(Q)
={}&
F_{P_i}(Q-1)-F_{P_i}(Q^2-1)\\
&-
r_iF_{P_i}\left(
\left\lfloor\frac{Q-1}{r_i}\right\rfloor
\right)\\
&+
r_iF_{P_i}\left(
\left\lfloor\frac{Q^2-1}{r_i}\right\rfloor
\right).
\end{aligned}
}
```

Candidate #23's exact budget remains

```math
\boxed{
\mathcal E_D
=
\sum_i
\frac{w_i}{2r_i(r_i-2)}
\mathcal M_i(Q)^2.
}
```

## Strategy Boundary

The summatory identity confirms that the lift-index transform is not an
independent source of cancellation. It is exactly the discrepancy between a
coprime count and its `r`-dilated coprime count at the two endpoints.

Consequently, another algebraic rewrite of floors, residues, or activation
shells cannot by itself upper-bound `mathcal E_D`. The missing input is now
precise:

> a weighted mean-square theorem for dilation remainders of the
> finite-sieve coprime counting function at the prime-square endpoints.

Such a theorem remains noncircular because it contains no final 2-gap
population. It is nevertheless new analytic distribution information, not a
consequence of the existing finite copy/filter identities.

## Related

- [Accepted-strike CRT lift-index transform](
  accepted-strike-crt-lift-index-transform.md
  )
- [Accepted-strike density as a Möbius boundary sum](
  accepted-strike-density-boundary-decomposition.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
