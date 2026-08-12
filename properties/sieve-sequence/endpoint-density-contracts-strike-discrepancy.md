# Endpoint Density Contracts Accepted-Strike Discrepancy

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

After filters `2` and `3` are installed, distinct 2-gaps cannot share an
endpoint. Consequently, the number of complete 2-gap endpoints inside an
eligible anchor set is at most the size of that set.

This simple injection removes the potentially dangerous ratio between the
2-gap population and the accepted-anchor population from candidate #23. The
2-gap-scaled strike-density error is never larger than the unnormalized
accepted-strike discrepancy itself.

## Setup

Let `V` be a finite set of `A>0` accepted anchors at a post-filter-3 stage.
Let `S` be a set of `N` complete 2-gap starts such that, for every `x` in `S`,
both

```math
x
\qquad\text{and}\qquad
x+2
```

belong to `V`.

Let `r>2` be the incoming prime, and let `H` be the number of anchors in `V`
struck by the filter. Define

```math
\varepsilon
=
\frac HA-\frac1r
```

and the unnormalized accepted-strike discrepancy

```math
D
=
H-\frac Ar.
```

## Endpoint-Density Bound

Every gap in `S` contributes two endpoints in `V`. After filter `3`, no
accepted value can be the endpoint of two distinct 2-gaps. The endpoint map is
therefore injective on the `2N` gap-endpoint incidences.

Hence

```math
\boxed{
2N\le A.
}
\qquad[\text{Q.E.D.}]
```

Equivalently,

```math
0\le\frac{2N}{A}\le1.
```

## Strike-Error Contraction

By definition,

```math
\varepsilon
=
\frac1A
\left(
H-\frac Ar
\right)
=
\frac DA.
```

Therefore

```math
\left|2N\varepsilon\right|
=
\frac{2N}{A}|D|
\le
|D|.
```

Thus

```math
\boxed{
\left|2N\varepsilon\right|
\le
\left|H-\frac Ar\right|.
}
\qquad[\text{Q.E.D.}]
```

Squaring preserves the inequality:

```math
\boxed{
\left(2N\varepsilon\right)^2
\le
\left(H-\frac Ar\right)^2.
}
```

## Boundary-Recurrence Form

For the complete accepted-anchor interval counted in the accepted-strike
boundary property, write

```math
E_i
=
A_i-\ell\frac{\varphi(P_i)}{P_i}.
```

The exact recurrence is

```math
H_i-\frac{A_i}{r_i}
=
\left(1-\frac1{r_i}\right)E_i-E_{i+1}.
```

The contraction consequently gives

```math
\boxed{
\left(2N_i\varepsilon_i\right)^2
\le
\left(
\left(1-\frac1{r_i}\right)E_i-E_{i+1}
\right)^2.
}
```

After multiplying by the nonnegative collision coefficient and chain weight,

```math
\boxed{
w_i\frac{r_i}{2(r_i-2)}
\left(2N_i\varepsilon_i\right)^2
\le
w_i\frac{r_i}{2(r_i-2)}
\left(
\left(1-\frac1{r_i}\right)E_i-E_{i+1}
\right)^2.
}
```

Thus candidate #23 no longer needs a lower bound for `A_i` or a separate
upper bound for `N_i/A_i`.

## Composition With Endpoint Sampling

Candidate #13 gives the exact harmful-excess decomposition

```math
b_i
=
H_i\beta_i+2N_i\varepsilon_i.
```

For every `lambda_i>0`, Young's inequality gives

```math
b_i^2
\le
(1+\lambda_i)H_i^2\beta_i^2
+
\left(1+\frac1{\lambda_i}\right)
\left(2N_i\varepsilon_i\right)^2.
```

Using the contraction,

```math
\boxed{
b_i^2
\le
(1+\lambda_i)H_i^2\beta_i^2
+
\left(1+\frac1{\lambda_i}\right)
\left(H_i-\frac{A_i}{r_i}\right)^2.
}
```

This separates candidate #13's endpoint-sampling budget from candidate #23's
accepted-strike budget without retaining a cross term of unknown sign.

## Limitation

The property removes the endpoint-to-anchor ratio, but it does not bound the
remaining adjacent boundary difference

```math
\left(1-\frac1{r_i}\right)E_i-E_{i+1}.
```

It also requires the same anchor convention used in the setup: both endpoints
of every counted gap must belong to `V`. If a different window convention
includes boundary-crossing gaps, those gaps must be removed or handled by an
explicit correction.

The result is a contraction lemma, not the quadratic-variation theorem needed
to finish candidate #23.

## Related

- [Isolation of 2-gaps after filtering by 3](
  two-gap-isolation-after-filter-three.md
  )
- [Two endpoint observables separate harmful excess and imbalance](
  two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Accepted-strike density as a Möbius boundary sum](
  accepted-strike-density-boundary-decomposition.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
