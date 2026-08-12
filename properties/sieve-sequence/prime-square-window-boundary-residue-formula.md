# Prime-Square Window Boundary Residue Formula

**Status:** Mathematically proved exact identity and exact counterexample.
Stainless verification is not claimed.

## Meaning

For the special window `[Q,Q^2)` with prime `Q`, every divisor of an
old-filter modulus is coprime to both endpoints. This removes the ceiling
functions from the accepted-anchor boundary error and replaces each divisor
term by a difference of two explicit residues.

The formula is exact, but primality of `Q` does not force the complete boundary
error to have one sign or to preserve its sign as filters are installed. An
exact example inside one fixed prime-square window shows a negative-to-positive
sign change.

## Setup

Let `Q` be prime and let `P` be squarefree with every prime divisor of `P`
smaller than `Q`. Define

```math
C_P(Q,Q^2)
=
\#\{
n\in\mathbb Z:
Q\le n<Q^2,\ 
\gcd(n,P)=1
\}.
```

The centered accepted-anchor boundary error is

```math
E_P(Q,Q^2)
=
C_P(Q,Q^2)
-
(Q^2-Q)\frac{\varphi(P)}P.
```

For `d>1`, write `[x]_d` for the least positive residue of `x` modulo `d`.
Because `d` divides `P`,

```math
\gcd(Q,d)=1,
```

so neither `[Q]_d` nor `[Q^2]_d` is zero.

## Exact Divisor Summand

For an integer `x` not divisible by `d`,

```math
\left\lceil\frac xd\right\rceil
=
\frac{x-[x]_d}{d}+1.
```

Therefore

```math
\begin{aligned}
&
\left\lceil\frac{Q^2}{d}\right\rceil
-
\left\lceil\frac Qd\right\rceil
-
\frac{Q^2-Q}{d}\\
&=
\left(
\frac{Q^2-[Q^2]_d}{d}+1
\right)
-
\left(
\frac{Q-[Q]_d}{d}+1
\right)
-
\frac{Q^2-Q}{d}\\
&=
\frac{[Q]_d-[Q^2]_d}{d}.
\end{aligned}
```

The `d=1` centered summand is zero. Substituting into finite
inclusion--exclusion proves

```math
\boxed{
E_P(Q,Q^2)
=
\sum_{\substack{d\mid P\\d>1}}
\mu(d)
\frac{[Q]_d-[Q^2]_d}{d}.
}
\qquad[\text{Q.E.D.}]
```

## Exactly Which Individual Terms Vanish

For `d>1`,

```math
[Q]_d=[Q^2]_d
```

if and only if

```math
d\mid Q^2-Q=Q(Q-1).
```

Since `gcd(Q,d)=1`, this is equivalent to

```math
\boxed{
d\mid Q-1.
}
```

Thus every divisor of `gcd(P,Q-1)` contributes zero individually. Divisors
containing at least one prime factor not dividing `Q-1` may contribute with
either sign after multiplication by `mu(d)`.

## Exact Sign-Change Counterexample

Fix the prime-square window

```math
[19,19^2)=[19,361),
\qquad
\ell=342.
```

For

```math
P=30=2\cdot3\cdot5,
\qquad
\varphi(P)=8,
```

finite inclusion--exclusion gives

```math
C_{30}(19,361)=91.
```

Hence

```math
E_{30}(19,361)
=
91-\frac{342\cdot8}{30}
=
-\frac15.
```

After also installing filters `7` and `11`,

```math
P=2310,
\qquad
\varphi(P)=480,
\qquad
C_{2310}(19,361)=71,
```

so

```math
E_{2310}(19,361)
=
71-\frac{342\cdot480}{2310}
=
-\frac5{77}.
```

After installing filter `13`,

```math
P=30030,
\qquad
\varphi(P)=5760,
\qquad
C_{30030}(19,361)=67.
```

Therefore

```math
E_{30030}(19,361)
=
67-\frac{342\cdot5760}{30030}
=
\frac{1403}{1001}
>
0.
```

The same fixed prime-square window consequently has

```math
E_{2310}(19,361)<0
\qquad\text{and}\qquad
E_{30030}(19,361)>0.
```

This refutes both a universal-sign claim and sign preservation under adjoining
the next prime filter.

## Consequence For Candidate #23

The special endpoints provide an exact residue representation and eliminate
all divisor terms supported entirely on `gcd(P,Q-1)`. They do not provide a
universal sign or monotonicity principle for the remaining Möbius sum.

Candidate #23 therefore still requires a genuine cancellation or
mean-square theorem for

```math
\sum_{\substack{d\mid P\\d>1}}
\mu(d)
\frac{[Q]_d-[Q^2]_d}{d}.
```

Rearranging the boundary recurrence, assuming favorable adjacent signs, or
using only the fact that `Q` is prime cannot supply that theorem.

## Limitation

The counterexample refutes universal sign and sign-preservation claims. It
does not prove that every possible bound on the residue sum is impossible.
A new estimate exploiting cancellation across divisors or averaging across
future heads could still exist.

Such an estimate would be new number-theoretic input, not a consequence of
the existing copy/filter identities.

## Related

- [Accepted-strike density as a Möbius boundary sum](
  accepted-strike-density-boundary-decomposition.md
  )
- [Accepted-strike error is a positive quadratic variation](
  accepted-strike-quadratic-variation.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
