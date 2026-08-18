# Weighted Composition Of Endpoint And Strike-Density Errors

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

The harmful excess at one filter is the sum of two errors:

1. endpoint-sampling bias among the anchors that were struck;
2. accepted-strike density bias in how many anchors were struck.

Bounding the square of their sum separately at every layer introduces
arbitrary Young parameters. At the chain level, the weighted triangle
inequality gives the optimal aggregate composition directly: the square root
of the combined budget is at most the sum of the two component square roots.

This yields a clean interface between candidates #13, #23, #22, and #21.

## Setup

At layer `i`, let

```math
b_i
=
H_i\beta_i+2N_i\varepsilon_i
```

be the exact harmful-excess decomposition. Assume candidate #13 supplies

```math
|\beta_i|\le\eta_i,
\qquad
|\Delta_i|\le H_i\eta_i.
```

Let the unnormalized accepted-strike discrepancy be

```math
D_i
=
H_i-\frac{A_i}{r_i}.
```

Post-3 endpoint isolation gives the proved contraction

```math
|2N_i\varepsilon_i|\le|D_i|.
```

Define the nonnegative harmful-energy weights

```math
c_i
=
w_i\frac{r_i}{2(r_i-2)}.
```

Finally define the three scalar budgets

```math
\mathcal E_\beta
=
\sum_i c_iH_i^2\eta_i^2,
```

```math
\mathcal E_D
=
\sum_i c_iD_i^2,
```

and

```math
\mathcal E_\Delta
=
\frac12\sum_iw_iH_i^2\eta_i^2.
```

## Weighted Harmful-Excess Bound

For each layer,

```math
|b_i|
\le
H_i\eta_i+|D_i|.
```

Apply the triangle inequality in the weighted Euclidean norm:

```math
\begin{aligned}
\left(
\sum_i c_i b_i^2
\right)^{1/2}
&\le
\left(
\sum_i c_i
\left(
H_i\eta_i+|D_i|
\right)^2
\right)^{1/2}\\
&\le
\left(
\sum_i c_iH_i^2\eta_i^2
\right)^{1/2}
+
\left(
\sum_i c_iD_i^2
\right)^{1/2}\\
&=
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}.
\end{aligned}
```

Squaring gives

```math
\boxed{
\sum_i
w_i\frac{r_i}{2(r_i-2)}b_i^2
\le
\left(
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}
\right)^2.
}
\qquad[\text{Q.E.D.}]
```

This is exactly the best bound obtained by using one common Young parameter
and optimizing it after the two aggregate component budgets are known.

## Composition With Harmless Dispersion

The orthogonal residue-energy identity is

```math
V_i
=
U_i
+
\frac{r_i}{2(r_i-2)}b_i^2
+
\frac12\Delta_i^2.
```

Candidate #13's signed endpoint observable gives

```math
\frac12\sum_iw_i\Delta_i^2
\le
\mathcal E_\Delta.
```

Therefore

```math
\boxed{
\sum_iw_iV_i
\le
\sum_iw_iU_i
+
\left(
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}
\right)^2
+
\mathcal E_\Delta.
}
\qquad[\text{Q.E.D.}]
```

## Exact Interface With Candidate #21

Let

```math
W=\sum_iw_i,
\qquad
T=N_0A_{0,m}.
```

Candidate #21's second-moment condition is

```math
\sum_iw_iV_i<\frac{T^2}{2W}.
```

The preceding property proves that it is sufficient to establish

```math
\boxed{
\sum_iw_iU_i
+
\left(
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}
\right)^2
+
\mathcal E_\Delta
<
\frac{T^2}{2W}.
}
```

Equivalently, the exact remaining allowance offered to candidate #22 is

```math
\boxed{
\mathcal U_*(Q)
=
\frac{T^2}{2W}
-
\left(
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}
\right)^2
-
\mathcal E_\Delta.
}
```

It is sufficient that

```math
\mathcal U_*(Q)>0
\qquad\text{and}\qquad
\sum_iw_iU_i<\mathcal U_*(Q).
```

## What Remains Open

This property performs the composition; it does not bound any candidate
budget. The remaining inputs are:

1. candidate #13 must bound `mathcal E_beta` and `mathcal E_Delta`;
2. candidate #23 must bound `mathcal E_D`, now a denominator-free weighted
   quadratic variation of accepted-anchor boundary errors;
3. candidate #22 must bound `sum_i w_i U_i` below the remaining allowance.

No final survivor count is used to normalize these three quantities.

## Limitation

Minkowski is sharp for aligned component-error vectors. Improving the
displayed composition requires a theorem showing favorable sign correlation
between `H_i beta_i` and `2N_i epsilon_i`. Without such information, replacing
the square-root sum by a smaller universal expression is unjustified.

## Related

- [Two endpoint observables separate harmful excess and imbalance](
  two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Endpoint density contracts accepted-strike discrepancy](
  endpoint-density-contracts-strike-discrepancy.md
  )
- [Orthogonal residue-energy decomposition after a two-class filter](
  orthogonal-residue-energy-decomposition-after-two-class-filter.md
  )
- [Accepted-anchor strike density](
  ../../candidates/accepted-anchor-strike-density.md
  )
- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
