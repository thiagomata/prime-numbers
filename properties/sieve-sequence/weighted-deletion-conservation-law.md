# Weighted Deletion Conservation Law

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

The multiplicative weights that arise when a one-layer survival recurrence is
unrolled have an exact per-gap interpretation. Every initial 2-gap contributes
one fixed amount to the weighted harmful excess if it is eventually destroyed,
and an amount smaller by exactly `1` if it survives the whole chain.

Consequently, the weighted signed discrepancy is not an independent route to
survival. It is exactly the multiplicative main term minus the final survivor
count.

## Setup

Fix a future prime head `Q` and a conditioned chain

```math
5\le r_0<r_1<\cdots<r_{m-1}<Q.
```

Let `S_0` be the complete 2-gap starts in `[Q,Q^2)` before the chain begins.
For `x in S_0`, define the alive indicator before layer `i` by

```math
f_i(x)
=
\prod_{j<i}
\mathbf 1_{r_j\nmid x(x+2)}.
```

Thus

```math
N_i=\sum_{x\in S_0}f_i(x)
```

is the number of current 2-gaps before filter `r_i`.

Define the hit indicator

```math
h_i(x)
=
\mathbf 1_{r_i\mid x}
+
\mathbf 1_{r_i\mid x+2}.
```

Because `r_i>2`, it cannot divide both endpoints, so

```math
h_i(x)\in\{0,1\}.
```

The number destroyed at layer `i` is

```math
K_i
=
\sum_{x\in S_0}f_i(x)h_i(x).
```

Set

```math
a_i=1-\frac2{r_i},
\qquad
A_{u,v}=\prod_{j=u}^{v-1}a_j,
\qquad
w_i=A_{i+1,m},
```

and extend the weights by

```math
w_{-1}=A_{0,m}.
```

Finally, define the signed harmful excess

```math
b_i
=
K_i-\frac{2N_i}{r_i}.
```

## Exact Population Recurrence

Filtering cannot create a new 2-gap after filter `2`; it only preserves an old
2-gap whose endpoints both survive. Therefore

```math
N_{i+1}=N_i-K_i.
```

Using the definition of `b_i`,

```math
\begin{aligned}
N_{i+1}
&=
N_i-\left(\frac{2N_i}{r_i}+b_i\right)\\
&=
a_iN_i-b_i.
\end{aligned}
```

This recurrence is exact.

## Per-Gap Contribution

For `x in S_0`, define its first hit time

```math
\tau(x)
=
\min\{i:0\le i<m,\ h_i(x)=1\},
```

and set `tau(x)=m` if no filter in the chain hits either endpoint.

The contribution of `x` to the weighted signed excess is

```math
B(x)
=
\sum_{i=0}^{m-1}
w_i f_i(x)
\left(h_i(x)-\frac2{r_i}\right).
```

The adjacent weights satisfy

```math
\frac{2w_i}{r_i}=w_i-w_{i-1}.
```

### Eventually destroyed gap

Suppose `tau(x)=t<m`. Then `f_i(x)=1` for `i<=t`,
`h_i(x)=0` for `i<t`, and `h_t(x)=1`. Hence

```math
\begin{aligned}
B(x)
&=
-\sum_{i=0}^{t-1}\frac{2w_i}{r_i}
+w_t\left(1-\frac2{r_t}\right)\\
&=
-\sum_{i=0}^{t-1}(w_i-w_{i-1})
+w_ta_t\\
&=
-(w_{t-1}-w_{-1})+w_{t-1}\\
&=
w_{-1}\\
&=
A_{0,m}.
\end{aligned}
```

This calculation also covers `t=0`: the empty sum vanishes and
`w_0a_0=w_{-1}`.

### Final survivor

Suppose `tau(x)=m`. Then `f_i(x)=1` and `h_i(x)=0` for every layer. Since
`w_{m-1}=A_{m,m}=1`,

```math
\begin{aligned}
B(x)
&=
-\sum_{i=0}^{m-1}\frac{2w_i}{r_i}\\
&=
-\sum_{i=0}^{m-1}(w_i-w_{i-1})\\
&=
-(w_{m-1}-w_{-1})\\
&=
A_{0,m}-1.
\end{aligned}
```

Thus the two possible contributions differ by exactly `1`.

## Conservation Law

Let `N_m` be the number of final survivors. Exactly `N_0-N_m` initial gaps
are eventually destroyed. Summing the per-gap contributions gives

```math
\begin{aligned}
\sum_{i=0}^{m-1}w_ib_i
&=
\sum_{x\in S_0}B(x)\\
&=
(N_0-N_m)A_{0,m}
+N_m(A_{0,m}-1)\\
&=
N_0A_{0,m}-N_m.
\end{aligned}
```

Therefore

```math
\boxed{
\sum_{i=0}^{m-1}w_ib_i
=
N_0A_{0,m}-N_m.
}
\qquad[\text{Q.E.D.}]
```

Equivalently,

```math
\boxed{
N_m
=
N_0A_{0,m}
-
\sum_{i=0}^{m-1}w_ib_i.
}
```

## Boundary

The condition

```math
\sum_iw_ib_i<N_0A_{0,m}
```

is exactly equivalent to `N_m>0`. It cannot serve as the missing theorem
without an independent upper bound for the signed excess.

A collision-energy or other structural majorant can still be useful because
it imposes information stronger than the conservation identity. But merely
renaming the left side “cumulative discrepancy” does not lower the proof
difficulty.

## Related

- [Weighted collision-energy chain survival](
  weighted-collision-energy-chain-survival.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
- [Batched short-window discrepancy boundary](
  batched-short-window-discrepancy-boundary.md
  )
