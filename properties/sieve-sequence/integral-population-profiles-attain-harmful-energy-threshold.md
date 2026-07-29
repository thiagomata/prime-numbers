# Integral Population Profiles Attain the Harmful-Energy Threshold

**Status:** Mathematically proved algebraic boundary. Stainless verification
is not claimed.

## Meaning

Property #66 proves that extinction forces the weighted harmful-excess energy
to satisfy

```math
E_b\ge\frac{T^2}{2W_-}.
```

Candidate #24 asks actual conditioned sieve chains to stay strictly below
this threshold. One possible source of a stronger estimate would be the fact
that actual populations and deletion counts are nonnegative integers, rather
than arbitrary real variables.

This property rules out that source by itself. For every fixed nonempty prime
chain, there are scaled abstract population profiles for which:

1. every population and deletion count is a nonnegative integer;
2. the population decreases strictly to zero;
3. the exact deletion recurrence holds; and
4. equality holds in property #66.

Thus integrality, population monotonicity, and the recurrence alone cannot
improve candidate #24's sharp threshold. Any improvement must use arithmetic
information about which gap starts the prime filters can actually delete.

## Setup

Fix a nonempty chain

```math
5\le r_0<r_1<\cdots<r_{m-1}.
```

Define

```math
a_i=1-\frac2{r_i},
\qquad
P_i=\prod_{j=0}^{i-1}a_j,
\qquad
P_0=1.
```

For `0<=i<=m`, put

```math
R_i
=
\sum_{j=i}^{m-1}\frac1{P_j},
\qquad
R_m=0,
```

and write

```math
S=R_0=\sum_{j=0}^{m-1}\frac1{P_j}.
```

Every `P_i`, `R_i`, and `S` is a positive rational number, except for
`R_m=0`.

## Equality Profile

Choose a positive integer `N_0` and define the rational profile

```math
\boxed{
N_i
=
\frac{N_0P_iR_i}{S}
}
\qquad(0\le i\le m).
```

This agrees with the chosen initial value because

```math
N_0\frac{P_0R_0}{S}=N_0,
```

and it becomes extinct at the endpoint:

```math
N_m=0.
```

For `i<m`, both `P_i` and `R_i` are positive, so `N_i>0`.

## Strict Monotonicity

Since

```math
R_i=\frac1{P_i}+R_{i+1}
```

and `P_{i+1}=a_iP_i`, the deletion count

```math
K_i=N_i-N_{i+1}
```

satisfies

```math
\begin{aligned}
K_i
&=
\frac{N_0}{S}
\left(
P_iR_i-P_{i+1}R_{i+1}
\right)\\
&=
\frac{N_0P_i}{S}
\left(
\frac1{P_i}
+(1-a_i)R_{i+1}
\right)\\
&>0.
\end{aligned}
```

Therefore

```math
N_0>N_1>\cdots>N_{m-1}>N_m=0.
```

In particular, the profile obeys

```math
0<K_i\le N_i,
\qquad
N_{i+1}=N_i-K_i.
```

## Exact Cauchy Equality

Define the harmful excess as in properties #25 and #66:

```math
b_i=a_iN_i-N_{i+1}.
```

Substituting the equality profile gives

```math
\begin{aligned}
b_i
&=
\frac{N_0P_{i+1}}S
\left(
R_i-R_{i+1}
\right)\\
&=
\frac{N_0P_{i+1}}S\frac1{P_i}\\
&=
\boxed{\frac{a_iN_0}{S}}.
\end{aligned}
```

The energy coefficient is

```math
c_i=\frac{r_i}{2(r_i-2)}=\frac1{2a_i}.
```

Hence

```math
c_ib_i=\frac{N_0}{2S}
```

is constant across every layer. This is exactly the equality condition in
the weighted Cauchy--Schwarz proof of property #66.

To check the value directly, use

```math
w_i=\frac{P_m}{P_{i+1}},
\qquad
W_-=\sum_i\frac{P_m}{P_i}=P_mS,
\qquad
T=N_0P_m.
```

Then

```math
\begin{aligned}
E_b
&=
\sum_iw_ic_ib_i^2\\
&=
\sum_i
\frac{P_m}{P_{i+1}}
\frac1{2a_i}
\frac{a_i^2N_0^2}{S^2}\\
&=
\frac{P_mN_0^2}{2S^2}
\sum_i\frac1{P_i}\\
&=
\frac{P_mN_0^2}{2S}\\
&=
\boxed{\frac{T^2}{2W_-}}.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

## Clearing Denominators

The coefficients

```math
\frac{P_iR_i}{S}
```

are rational and there are only finitely many of them. Choose `N_0` to be a
positive common multiple of their denominators. Then every `N_i` is an
integer. Consequently,

```math
K_i=N_i-N_{i+1}
```

is also a positive integer.

Scaling `N_0` does not change any step of the equality proof. Therefore the
Cauchy threshold is attained exactly by arbitrarily large integral,
strictly decreasing extinction profiles.

## What This Refutes

No proof can relax candidate #24's threshold uniformly using only:

1. `N_i` and `K_i` are integers;
2. `N_i>=0` and `K_i>=0`;
3. `N_{i+1}=N_i-K_i`;
4. the multiplicative coefficients `a_i`;
5. the endpoint condition `N_m=0`.

All five facts hold in the equality construction.

## Boundary

The construction is an abstract deletion schedule. It does not claim that
there is a set of integer gap starts in a prime-square window whose first
prime-hit counts are the constructed `K_i`.

Actual conditioned chains also require CRT residue compatibility: deletion at
layer `i` must come from surviving starts `x` for which

```math
r_i\mid x(x+2).
```

That arithmetic geometry is deliberately absent here. Consequently, this
property does not disprove candidate #24. It proves that the missing theorem
cannot come from population integrality or monotonicity alone.

## Consequence For The Candidate Program

The next useful algebraic object is not another inequality in the scalar
sequence `(N_i)`. It must retain information about the deletion partition of
the initial gap set, for example:

1. first-hit classes indexed by the deleting prime;
2. congruence restrictions on pairs of first-hit classes;
3. a weighted Gram or correlation inequality tied to the actual CRT
   coefficients; or
4. an arithmetic obstruction to the Cauchy-equality deletion proportions.

These directions can upper-bound or exclude harmful-excess profiles in ways
that the population recurrence cannot see.

## Related Properties And Candidates

- [Weighted deletion conservation law](weighted-deletion-conservation-law.md)
- [Weighted harmful-excess energy is already terminal](
  weighted-harmful-excess-energy-is-terminal.md
  )
- [Weighted harmful-excess quadratic survival](
  ../../candidates/weighted-harmful-excess-quadratic-survival.md
  )

