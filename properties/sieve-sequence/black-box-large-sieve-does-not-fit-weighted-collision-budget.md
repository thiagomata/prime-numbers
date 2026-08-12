# Black-Box Large Sieve Does Not Fit The Weighted Collision Budget

**Status:** Mathematically proved quantitative obstruction, conditional only
on granting the stated standard large-sieve input. Stainless verification is
not claimed.

## Meaning

A classical large sieve controls residue variance by the length of the
supporting interval times the local population. That is the right kind of
normalization: unlike the failed Fourier convolution bounds, it uses the
actual number `N` of localized points.

Nevertheless, its standard scale is too large for candidate #21. Even in the
optimistic model where every layer variance belongs to one fixed set, the
black-box upper bound exceeds the entire weighted-energy allowance. The
actual candidate is harder because its conditioned sets change with the
prime, but that issue is not needed for this negative audit.

## Setup

Use the full post-3 filtering chain

```math
5=r_0<r_1<\cdots<r_{m-1}<Q.
```

Let

```math
a_i=1-\frac2{r_i},
\qquad
A=A_{0,m}=\prod_{i<m}a_i,
\qquad
w_i=A_{i+1,m},
\qquad
W=\sum_{i<m}w_i.
```

Let `S` be a fixed set of `N` 2-gap starts in an interval of diameter `L`,
and define its residue variance modulo `r_i` by

```math
V_i
=
\sum_{a\bmod r_i}
\left(
c_{i,a}-\frac{N}{r_i}
\right)^2.
```

## Standard Fixed-Set Input

The usual additive large-sieve inequality, followed by the finite Fourier
identity for residue variance, has the form

```math
\boxed{
\sum_{i<m}r_iV_i
\le
(L+Q^2)N.
}
```

The precise endpoint convention can improve `L+Q^2` by an additive constant.
That cannot affect the obstruction below.

This note grants this inequality as an optimistic input. It does not attempt
to derive it from the project's current verified properties.

## Exact Monotonicity Of The Survival Weights

Define

```math
\lambda_i=\frac{w_i}{r_i}.
```

Since consecutive odd primes satisfy

```math
r_{i+1}\ge r_i+2,
```

and

```math
w_i
=
\left(1-\frac2{r_{i+1}}\right)w_{i+1},
```

we have

```math
\frac{\lambda_i}{\lambda_{i+1}}
=
\frac{r_{i+1}-2}{r_i}
\ge
1.
```

Thus

```math
\lambda_0\ge\lambda_1\ge\cdots\ge\lambda_{m-1}.
```

Because `r_0=5`,

```math
A
=
\frac35w_0,
```

and hence

```math
\boxed{
\lambda_0
=
\frac{w_0}{5}
=
\frac A3.
}
```

## Weighted Large-Sieve Consequence

The granted fixed-set bound gives

```math
\begin{aligned}
\sum_{i<m}w_iV_i
&=
\sum_{i<m}\lambda_i(r_iV_i)\\
&\le
\lambda_0\sum_{i<m}r_iV_i\\
&\le
\boxed{
\frac A3(L+Q^2)N.
}
\end{aligned}
```

Candidate #21's second-moment condition is

```math
2W\sum_{i<m}w_iV_i
<
(NA)^2.
```

For the black-box upper bound itself to imply this condition, it would need

```math
\frac{2WA}{3}(L+Q^2)N
<
N^2A^2,
```

or equivalently

```math
\boxed{
2W(L+Q^2)<3NA.
}
```

## Deterministic Capacity Contradiction

After filtering by `3`, every 2-gap start is in the single class `5 modulo 6`.
An interval of diameter `L` therefore contains at most

```math
N\le\left\lfloor\frac L6\right\rfloor+1
```

such starts. Also,

```math
W\ge w_{m-1}=1,
\qquad
A\le1.
```

Consequently,

```math
3NA
\le
3\left(
\left\lfloor\frac L6\right\rfloor+1
\right)
\le
\frac L2+3,
```

whereas

```math
2W(L+Q^2)
\ge
2(L+Q^2).
```

For the square-window diameter

```math
L=Q^2-Q-3
```

and `Q>=7`, the latter quantity is strictly larger than `L/2+3`. Hence the
required constant inequality cannot hold.

## Conclusion

The standard fixed-set large-sieve scale cannot certify candidate #21. This
does not show that the actual weighted energy is large, and it does not
disprove the candidate. It shows that a proof must gain substantially over
the black-box `L+Q^2` scale.

The needed gain must use structure suppressed by the standard theorem, such
as the nested deletion times, cancellation from the exact centering telescope,
or a dispersion identity specialized to the four-point pattern
`{0,2,d,d+2}`. Merely solving the changing-population bookkeeping and then
applying the ordinary large sieve would still be quantitatively insufficient.

## Related

- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
- [Weighted collision-energy chain survival](
  weighted-collision-energy-chain-survival.md
  )
- [Short-interval localization destroys prime conductor decay](
  short-interval-localization-destroys-prime-conductor-decay.md
  )
