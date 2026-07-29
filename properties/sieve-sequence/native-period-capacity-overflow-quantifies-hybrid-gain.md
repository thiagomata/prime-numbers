# Native-Period Capacity Overflow Quantifies the Hybrid Gain

**Status:** Mathematically proved conditioned-chain corollary. Stainless
verification is not claimed.

## Meaning

Property #72 gives the exact greedy intersection of a native-period Bessel
budget with the coordinatewise harmful-capacity bounds. This property
compresses that linear program into one scalar per cut.

The scalar is the amount by which the normalized capacity box overfills the
available interval-remainder budget. Every unit of this overflow must be
removed by the Bessel constraint. The smallest energy coefficient in the
prefix therefore converts the overflow into a guaranteed reduction from the
all-capacity envelope.

The resulting condition is weaker than evaluating the exact greedy formula,
but simpler. It remains an explicit terminal criterion, not a proof that the
required overflow is universally large.

## Setup

Use property #72's notation. At a positive cut `k`, let

```math
q_{i,k}=M_kd_ip_ia_i,
\qquad
c_{i,k}=\frac{X_i}{q_{i,k}},
```

and

```math
\beta_{i,k}
=
\frac{M_kd_m}{r_i-2}.
```

The sharp greedy allocation is

```math
t_{i,k}^{\star}
=
\min
\left\{
c_{i,k},
\left(
s_k-\sum_{j<i}c_{j,k}
\right)_+
\right\}.
```

Define the normalized capacity overflow

```math
\boxed{
e_k
:=
\left(
\sum_{i<k}c_{i,k}-s_k
\right)_+.
}
```

Also define the gain of cut `k` over property #70's all-capacity envelope:

```math
\boxed{
\Delta_k
:=
\mathcal U_{\mathrm{cap}}
-
\mathcal U_k^{\mathrm{hyb}}.
}
```

## Exact Excluded Mass

The greedy allocation uses all available capacity if the capacity box fits
inside the Bessel budget, and otherwise uses exactly the full budget `s_k`.
Therefore

```math
\sum_{i<k}t_{i,k}^{\star}
=
\min
\left(
s_k,
\sum_{i<k}c_{i,k}
\right).
```

Let

```math
\delta_{i,k}
=
c_{i,k}-t_{i,k}^{\star}.
```

Every `delta_(i,k)` is nonnegative, and

```math
\begin{aligned}
\sum_{i<k}\delta_{i,k}
&=
\sum_{i<k}c_{i,k}
-
\min
\left(
s_k,
\sum_{i<k}c_{i,k}
\right)\\
&=
\left(
\sum_{i<k}c_{i,k}-s_k
\right)_+\\
&=
\boxed{e_k}.
\end{aligned}
```

Thus `e_k` is exactly the normalized capacity mass excluded by native-period
Bessel.

## Two-Sided Gain Bound

The suffix contribution is identical in `U_cap` and
`U_k^(hyb)`. On the prefix,

```math
\alpha_iX_i
=
\beta_{i,k}c_{i,k},
\qquad
\mathcal H_k
=
\sum_{i<k}\beta_{i,k}t_{i,k}^{\star}.
```

Hence

```math
\boxed{
\Delta_k
=
\sum_{i<k}\beta_{i,k}\delta_{i,k}.
}
```

The incoming primes increase, so

```math
\beta_{0,k}
>
\beta_{1,k}
>
\cdots
>
\beta_{k-1,k}
>
0.
```

Using `delta_(i,k)>=0` and `sum delta_(i,k)=e_k`,

```math
\boxed{
\frac{M_kd_m}{r_{k-1}-2}e_k
\le
\Delta_k
\le
\frac{M_kd_m}{r_0-2}e_k.
}
```

In particular, `e_k>0` is equivalent to a strict gain at cut `k`, agreeing
with property #72's exact improvement criterion.

## Simplified Hybrid Upper Bound

Because

```math
\mathcal U_{\mathrm{hyb}}
=
\min_{0\le k\le m}\mathcal U_k^{\mathrm{hyb}},
```

and the empty cut has zero gain,

```math
\mathcal U_{\mathrm{hyb}}
=
\mathcal U_{\mathrm{cap}}
-
\max_{1\le k\le m}\Delta_k.
```

The lower gain estimate therefore gives

```math
\boxed{
E_b
\le
\mathcal U_{\mathrm{hyb}}
\le
\mathcal U_{\mathrm{cap}}
-
\max_{1\le k\le m}
\left[
\frac{M_kd_m}{r_{k-1}-2}e_k
\right].
}
```

This bound is generally weaker than evaluating property #72's exact greedy
formula, but it replaces the entire allocation by one overflow scalar per
cut.

## Survival Composition

Property #69 proves that extinction forces

```math
E_b
\ge
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}.
```

Consequently,

```math
\boxed{
\mathcal U_{\mathrm{cap}}
-
\max_{1\le k\le m}
\left[
\frac{M_kd_m}{r_{k-1}-2}e_k
\right]
<
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}
\quad\Longrightarrow\quad
N_m>0.
}
```

The implication is fully proved. The antecedent is the remaining arithmetic
obligation.

## Boundary

This theorem quantifies the gain already present in property #72; it does not
add a new source of cancellation. It is useful when a lower bound on one
normalized capacity overflow is easier to prove than the full greedy energy
comparison.

If every `e_k` vanishes, native-period Bessel does not improve the
all-capacity envelope. If some `e_k` is positive but too small, the gain may
still fail to clear the extinction deficit. Any universal application must
therefore control both the capacity overflow and its scale relative to the
terminal threshold.

No empirical evidence is used in this result.

## Related

- [Harmful Capacity Separates the Energy Minimizer](harmful-capacity-separates-energy-minimizer.md)
- [Sharp Harmful-Capacity Excess Envelope](sharp-harmful-capacity-excess-envelope.md)
- [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
- [Candidate #24: Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
