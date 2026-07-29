# Harmful Capacity Separates the Energy Minimizer

**Status:** Mathematically proved conditioned-chain stability theorem.
Stainless verification is not claimed.

## Meaning

Property #67 constructs the unique extinct population profile that attains
candidate #24's conservation-only energy threshold. Property #68 measures the
energy above that threshold by the squared distance from this minimizing
profile.

The sieve also has an arithmetic restriction absent from property #67:
post-filter-3 spacing gives an absolute capacity for the two harmful residue
classes at every layer. This property computes the minimizing profile's
deletion masses exactly and quantifies what happens when a proved capacity is
smaller than one of them.

A violated capacity excludes the Cauchy minimizer and forces a positive,
explicit stability gap. It does not exclude extinction and does not upper-bound
the actual harmful-excess energy. It therefore enlarges a possible survival
certificate but does not prove candidate #24 by itself.

## Setup

Fix a nonempty conditioned chain with

```math
a_i=1-\frac2{r_i},
\qquad
p_i=\frac2{r_i}=1-a_i,
```

```math
P_i=A_{0,i},
\qquad
P_0=1.
```

As in property #67, define

```math
R_i=\sum_{j=i}^{m-1}\frac1{P_j},
\qquad
S=R_0.
```

Let `N_0>0` be fixed. For an extinct profile, `N_m=0`, and property #68's
unique minimizing harmful excess is

```math
\boxed{
b_i^\star=\frac{a_iN_0}{S}.
}
```

The corresponding minimizing populations are

```math
\boxed{
N_i^\star=\frac{N_0P_iR_i}{S}.
}
```

Let `K_i=N_i-N_{i+1}` denote deletion mass. Suppose arithmetic gives an
absolute total harmful capacity

```math
\boxed{K_i\le C_i.}
```

For the square window after filter `3`, the proved capacity is

```math
C_i
=
2\left(
\left\lfloor
\frac{Q^2-Q-3}{6r_i}
\right\rfloor+1
\right).
```

## Exact Deletion Mass Of The Minimizer

Since

```math
R_i=\frac1{P_i}+R_{i+1}
```

and `P_{i+1}=a_iP_i`,

```math
\begin{aligned}
K_i^\star
&=
N_i^\star-N_{i+1}^\star\\
&=
\frac{N_0P_i}{S}
\left(
R_i-a_iR_{i+1}
\right)\\
&=
\frac{N_0P_i}{S}
\left(
\frac1{P_i}+p_iR_{i+1}
\right)\\
&=
\boxed{
\frac{N_0}{S}
\left(
1+p_iP_iR_{i+1}
\right).
}
\end{aligned}
```

Equivalently, using `K_i=p_iN_i+b_i`,

```math
K_i^\star
=
p_iN_i^\star+b_i^\star.
```

Therefore the real minimizing profile is compatible with all total harmful
capacities exactly when

```math
\boxed{
K_i^\star\le C_i
\quad\text{for every }i.
}
```

At the final layer, `R_m=0`, so

```math
K_{m-1}^\star=N_{m-1}^\star=\frac{N_0}{S}.
```

The other layers include the additional expected-deletion term
`p_iP_iR_{i+1}` and can therefore also be the first capacity obstruction.

## Perturbation From The Minimizer

Let `(N_i,K_i,b_i)` be any other extinct real profile with the same initial
population `N_0`. Define

```math
\delta N_i=N_i-N_i^\star,
\qquad
\delta K_i=K_i-K_i^\star,
\qquad
\delta b_i=b_i-b_i^\star.
```

Both profiles satisfy

```math
N_{i+1}=a_iN_i-b_i,
```

and they have the same `N_0`, so

```math
\delta N_0=0.
```

Iterating the difference recurrence gives

```math
\boxed{
\delta N_i
=
-
\sum_{j=0}^{i-1}
A_{j+1,i}\delta b_j.
}
```

Because `K_i=p_iN_i+b_i`,

```math
\begin{aligned}
\delta K_i
&=
p_i\delta N_i+\delta b_i\\
&=
\boxed{
\delta b_i
-
p_i
\sum_{j=0}^{i-1}
A_{j+1,i}\delta b_j.
}
\end{aligned}
```

This is the exact linear functional by which a capacity constraint separates
the actual deletion profile from the energy minimizer.

## Explicit Capacity-Induced Stability Gap

Property #68 gives the exact extinct-chain remainder

```math
\mathcal R
:=
E_b-\frac{T^2}{2W_-}
=
\sum_{j=0}^{m-1}
\alpha_j\delta b_j^2,
```

where

```math
\alpha_j=\frac{w_j}{2a_j}>0.
```

For each layer `i`, define the dual squared norm

```math
\boxed{
D_i
=
\frac1{\alpha_i}
+
p_i^2
\sum_{j=0}^{i-1}
\frac{A_{j+1,i}^2}{\alpha_j}.
}
```

Weighted Cauchy--Schwarz applied to the exact formula for `delta K_i` gives

```math
(\delta K_i)^2
\le
\mathcal R D_i.
```

Write

```math
(x)_+=\max(x,0).
```

If the actual profile satisfies `K_i<=C_i` and the minimizing mass violates
that cap, then

```math
\delta K_i
=
K_i-K_i^\star
\le
-
\left(
K_i^\star-C_i
\right).
```

Hence

```math
\boxed{
\mathcal R
\ge
\frac{
\left(
K_i^\star-C_i
\right)_+^2
}{
D_i
}.
}
```

Taking the strongest coordinate gives

```math
\boxed{
E_b
\ge
\frac{T^2}{2W_-}
+
\max_{0\le i<m}
\frac{
\left(
K_i^\star-C_i
\right)_+^2
}{
D_i
}.
}
\qquad[\text{Q.E.D.}]
```

This is a parameter-only lower bound once `N_0`, the chain, and the arithmetic
capacities are specified.

## Consequence For Survival Certificates

Define

```math
\Gamma_{\mathrm{cap}}
=
\max_i
\frac{
\left(
K_i^\star-C_i
\right)_+^2
}{
D_i
}.
```

Every extinct chain satisfying the capacities obeys

```math
E_b
\ge
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}.
```

Therefore the relaxed strict inequality

```math
\boxed{
E_b
<
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}
}
```

also forces `N_m>0`.

When every `K_i^star<=C_i`, this theorem gives `Gamma_cap=0` and returns to
candidate #24's original threshold. When some cap is violated, the theorem
quantifies the extra allowance supplied by the proved harmful-class spacing.

## Why This Is Not Candidate #19's Population Floor

At the final layer, actual extinction gives

```math
K_{m-1}=N_{m-1}\le C_{m-1}.
```

Proving instead that the actual population satisfies

```math
N_{m-1}>C_{m-1}
```

would directly force survival and is candidate #19's local population route.

The comparison in this property is different:

```math
N_{m-1}^\star=\frac{N_0}{S}>C_{m-1}.
```

It concerns the abstract energy minimizer, not the actual final-layer
population. It excludes equality and creates a stability gap while remaining
compatible with an extinct actual profile having `N_{m-1}<=C_{m-1}`.

Earlier layers can also contribute through `K_i^star>C_i`; the result is not
restricted to the final population test.

## Boundary

This property advances the secondary stability-gap interface, not the primary
upper-bound interface.

The capacity inequalities allow profiles with energy much larger than the
displayed lower bound. They do not prove

```math
E_b
<
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}.
```

A successful survival proof still needs a coefficient-sensitive upper bound
for the actual harmful-excess energy. The new gap is useful only to the extent
that it materially relaxes that separate upper-bound obligation.

The theorem also uses only one capacity violation at a time and takes their
maximum. A joint projection onto all violated capacity half-spaces could yield
a stronger gap, but that is a finite quadratic optimization problem rather
than a new arithmetic estimate.

## Related Properties And Candidates

- [Harmful residue capacity after filter three](
  harmful-residue-capacity-after-filter-three.md
  )
- [Sharp sixfold-capacity harmful-energy envelope](
  sharp-sixfold-capacity-harmful-energy-envelope.md
  )
- [Integral population profiles attain the harmful-energy threshold](
  integral-population-profiles-attain-harmful-energy-threshold.md
  )
- [Harmful-excess energy has an exact stability decomposition](
  harmful-excess-energy-exact-stability-decomposition.md
  )
- [Sixfold harmful-residue capacity](
  ../../candidates/sixfold-harmful-residue-capacity.md
  )
- [Weighted harmful-excess quadratic survival](
  ../../candidates/weighted-harmful-excess-quadratic-survival.md
  )
