# Sharp Harmful-Capacity Excess Envelope

**Status:** Mathematically proved conditional capacity theorem. Stainless
verification is not claimed.

## Meaning

Candidate #24 needs an upper bound for the weighted harmful-excess energy
`E_b`. The Sixfold-Capacity Energy Envelope property solves a stronger one-layer extremal problem involving
both total harmful excess and left/right imbalance. For candidate #24, only
the total harmful count matters.

This property projects the same exact capacity polytope onto that one
coordinate. It gives the sharp one-layer upper bound for `b_i^2` obtainable
from:

1. the actual layer population;
2. the common residue-class capacity; and
3. no further distribution information.

Summing the sharp one-layer bounds gives a valid capacity-only upper envelope
for `E_b`. Combining it with the Capacity Minimizer Separation property's capacity-induced extinction gap
produces a relaxed conditional survival theorem.

The aggregate inequality remains open for actual conditioned chains. This
property identifies its exact capacity-only form; it does not prove that form
fits the survival allowance.

## One-Layer Setup

Let `r>2`. Suppose a local population has residue counts

```math
c_a
\qquad(a\bmod r)
```

with

```math
0\le c_a\le B,
\qquad
\sum_{a\bmod r}c_a=N.
```

Let the two harmful residue classes contain

```math
K=c_0+c_{-2}
```

starts in total. Define

```math
p=\frac2r
```

and the signed harmful excess

```math
b=K-pN.
```

For the post-filter-3 square window, the proved common capacity is

```math
B
=
\left\lfloor
\frac{Q^2-Q-3}{6r}
\right\rfloor+1.
```

## Exact Feasible Harmful Interval

The Sixfold-Capacity Energy Envelope property proves the exact feasible interval

```math
\boxed{
\ell\le K\le u,
}
```

where

```math
\ell=\max(0,N-(r-2)B),
\qquad
u=\min(N,2B).
```

The upper endpoint follows from the capacity of the two harmful classes. The
lower endpoint follows because the other `r-2` classes can hold at most
`(r-2)B` starts.

Both endpoints are attainable whenever `N<=rB`.

## Sharp Harmful-Excess Maximum

Since

```math
b^2=(K-pN)^2
```

is convex as a function of `K`, its maximum over the interval `[ell,u]` occurs
at an endpoint. Therefore

```math
\boxed{
b^2
\le
M_{r,N,B}
:=
\max
\left\{
\left(\ell-\frac{2N}{r}\right)^2,
\left(u-\frac{2N}{r}\right)^2
\right\}.
}
```

Because both endpoints are attainable, this bound is sharp:

```math
\boxed{
\max_{\substack{\sum_ac_a=N\\0\le c_a\le B}}
\left(
c_0+c_{-2}-\frac{2N}{r}
\right)^2
=
M_{r,N,B}.
}
\qquad[\text{Q.E.D.}]
```

After multiplying by the harmful-energy coefficient, one has

```math
\frac{r}{2(r-2)}M_{r,N,B}
\le
\max\mathcal Q_r.
```

the Sixfold-Capacity Energy Envelope property's full envelope also pays for the nonnegative left/right
imbalance term.

## Conditioned-Chain Upper Envelope

For each layer `i`, use the actual population `N_i`, incoming prime `r_i`,
and common capacity `B_i`. Define

```math
\ell_i=\max(0,N_i-(r_i-2)B_i),
\qquad
u_i=\min(N_i,2B_i),
```

```math
M_i
=
\max
\left\{
\left(\ell_i-\frac{2N_i}{r_i}\right)^2,
\left(u_i-\frac{2N_i}{r_i}\right)^2
\right\}.
```

The actual harmful excess satisfies

```math
b_i^2\le M_i.
```

Since

```math
E_b
=
\sum_i
w_i
\frac{r_i}{2(r_i-2)}
b_i^2,
```

one obtains the aggregate capacity envelope

```math
\boxed{
E_b
\le
\mathcal U_{\mathrm{cap}}
:=
\sum_i
w_i
\frac{r_i}{2(r_i-2)}
M_i.
}
```

This upper bound is unconditional once the actual populations and the proved
capacities are supplied.

## Composition With The Capacity Stability Gap

The Capacity Minimizer Separation property defines

```math
\Gamma_{\mathrm{cap}}
=
\max_i
\frac{
\left(
K_i^\star-2B_i
\right)_+^2
}{
D_i
}
```

and proves that extinction forces

```math
E_b
\ge
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}.
```

Consequently, the strict aggregate condition

```math
\boxed{
\mathcal U_{\mathrm{cap}}
<
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}
}
```

implies

```math
E_b
<
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}},
```

which contradicts extinction. Therefore

```math
\boxed{N_m>0.}
\qquad[\text{Q.E.D.}]
```

This is the sharp candidate #24 certificate currently obtainable by combining
the common class capacities with separate one-layer maximization.

## One-Layer Threshold Is Not Weaker

Put

```math
\rho=\frac NB.
```

The Sixfold Population-Ratio Threshold property proves that the stronger full harmful-energy envelope fits its
one-layer allowance exactly when

```math
\boxed{
\rho>\rho_*(r),
\qquad
\rho_*(r)
=
\frac{2}{
2/r+(1-2/r)^{3/2}
}.
}
```

The same threshold is necessary and sufficient for this property's b-only
envelope.

For necessity, the Sixfold Population-Ratio Threshold property's decisive extremal branch is

```math
K=2B.
```

Both harmful classes are full, so their imbalance is zero. The full energy on
that branch is therefore exactly the b-energy used here. It violates the
one-layer allowance whenever `rho<=rho_*(r)`.

For sufficiency, when `rho>rho_*(r)`, the Sixfold Population-Ratio Threshold property proves that every branch of
the stronger full harmful-energy envelope fits the allowance. Its b-component
therefore fits as well.

Thus

```math
\boxed{
\text{sharp b-only capacity envelope fits}
\quad\Longleftrightarrow\quad
\rho>\rho_*(r).
}
```

Since the Sixfold Population-Ratio Threshold property also proves

```math
\rho_*(r)>2,
```

the b-only local condition is strictly stronger than candidate #19's ordinary
capacity-survival condition `N>2B`. Removing left/right imbalance does not
create a weaker capacity-only population threshold.

For a chain with only one layer, the minimizing deletion mass is

```math
K_0^\star=N_0.
```

If `N_0<=2B_0`, then `Gamma_cap=0` and the sharp envelope cannot certify
survival. If `N_0>2B_0`, the ordinary capacity theorem already forces a
survivor. Hence the capacity stability gap creates no new one-layer regime.

## Sharpness And Non-Composition

For each fixed layer, `M_i` is the exact maximum compatible with `N_i`,
`r_i`, and `B_i`. No smaller universal one-layer envelope follows from those
three inputs alone.

The weighted sum need not be sharp over a complete chain. The residue
histograms attaining `M_i` separately may not arise from one nested sequence
of actual survivor sets. Therefore a cross-layer CRT restriction could lower
the true aggregate energy below `mathcal U_cap`.

The preceding one-layer classification shows that such a joint restriction is
not optional if this route is to improve candidate #19. Separate-layer
capacity optimization is exhausted.

The One-Layer Ellipse Non-Composition property gives the corresponding warning for the stronger local harmful
ellipses: separate one-layer success does not automatically fit the global
weighted allowance. Here the sum is a valid upper bound, but proving it below
the displayed threshold is already a terminal conditioned-chain theorem.

## Boundary

The envelope depends on the actual population profile `(N_i)`. Substituting a
coarse bound such as `N_i<=N_0` can destroy the required scale. A useful
universal theorem must retain enough cross-layer arithmetic to control the
weighted endpoint maxima.

This property does not prove

```math
\mathcal U_{\mathrm{cap}}
<
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}.
```

It reduces the remaining capacity-only route to that explicit inequality.
If the inequality is too large, further progress requires a joint restriction
on the harmful totals, not a sharper separate-layer optimization: the
one-layer maxima are already exact.

## Related Properties And Candidates

- [Sharp sixfold-capacity harmful-energy envelope](
  sharp-sixfold-capacity-harmful-energy-envelope.md
  )
- [One-layer harmful ellipses do not compose](
  one-layer-harmful-ellipses-do-not-compose.md
  )
- [Harmful capacity separates the energy minimizer](
  harmful-capacity-separates-energy-minimizer.md
  )
- [Sixfold harmful-residue capacity](
  ../../candidates/sixfold-harmful-residue-capacity.md
  )
- [Weighted harmful-excess quadratic survival](
  ../../candidates/weighted-harmful-excess-quadratic-survival.md
  )
