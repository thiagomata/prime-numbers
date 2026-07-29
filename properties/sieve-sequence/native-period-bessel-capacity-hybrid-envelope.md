# Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope

**Status:** Mathematically proved conditioned-chain bound. Stainless
verification is not claimed.

## Meaning

Property #71 applies cross-layer Bessel over the final CRT period and retains
an unusable primorial factor. Property #70 instead bounds every layer
separately by harmful-class capacity.

The two bounds can be combined at an intermediate native period. For any cut
`k`, complete `M_k` blocks cancel from the first `k` harmful-excess
coordinates. Bessel then imposes one joint budget on those prefix
coordinates, while the capacity theorem imposes an individual upper bound on
each coordinate. Their sharp intersection is an explicit linear program.
The later coordinates remain controlled by capacity.

Optimizing over the cut can never be worse than the all-capacity theorem,
because the empty-prefix cut recovers property #70 exactly. This property
does not prove that the optimized envelope clears the extinction threshold.
It gives a strictly sharper algebraic target whenever a native-period Bessel
budget excludes part of the capacity box.

## Setup

Use property #71's nested CRT moduli and paired observables:

```math
M_{i+1}=M_ir_i,
\qquad
g_i(n)
=
F_i(n)
\left(
h_i(n)-\frac2{r_i}
\right).
```

Write

```math
p_i=\frac2{r_i},
\qquad
a_i=1-p_i,
\qquad
b_i=\sum_{n\in I}g_i(n),
```

where `I` is an integer interval of length `L`. Let `d_i` be the
complete-period density of pairs surviving before filter `r_i`.

Candidate #24's energy coefficients are

```math
\alpha_i
=
\frac{w_i}{2a_i},
\qquad
E_b=\sum_{i=0}^{m-1}\alpha_ib_i^2.
```

Property #70 gives the sharp capacity-only coordinate bounds

```math
b_i^2\le X_i,
```

where

```math
X_i
=
\max
\left\{
\left(\ell_i-\frac{2N_i}{r_i}\right)^2,
\left(u_i-\frac{2N_i}{r_i}\right)^2
\right\}.
```

The letter `X_i` is used here to avoid confusing this capacity maximum with
the CRT modulus `M_i`.

## Native-Period Prefix Bessel Bound

Fix a cut

```math
1\le k\le m.
```

Every `g_i` with `i<k` has period `M_{i+1}`, which divides `M_k`. Property
#71's orthogonality proof therefore applies over `Z/M_kZ`, and its norm there
is

```math
\boxed{
q_{i,k}
:=
\lVert g_i\rVert_{2,M_k}^2
=
M_kd_ip_ia_i.
}
```

Let

```math
s_k=L\bmod M_k,
\qquad
0\le s_k<M_k.
```

Each complete interval block of length `M_k` contributes zero to every
`b_i` with `i<k`. After deleting those complete blocks, only one interval
remainder of length `s_k` remains. Its residue indicator has squared norm
`s_k`, so Bessel gives

```math
\boxed{
\sum_{i=0}^{k-1}
\frac{b_i^2}{q_{i,k}}
\le
s_k.
}
```

This is localized to the native prefix period `M_k`, not the final period
`M_m`.

## Sharp Intersection With Capacity

Set

```math
y_i=b_i^2,
\qquad
t_i=\frac{y_i}{q_{i,k}},
\qquad
c_{i,k}=\frac{X_i}{q_{i,k}}.
```

The proved prefix constraints become

```math
0\le t_i\le c_{i,k},
\qquad
\sum_{i<k}t_i\le s_k.
```

The prefix energy is

```math
\sum_{i<k}\alpha_iy_i
=
\sum_{i<k}\beta_{i,k}t_i,
```

where

```math
\begin{aligned}
\beta_{i,k}
&=
\alpha_iq_{i,k}\\
&=
\frac{w_i}{2a_i}
M_kd_ip_ia_i\\
&=
M_k\frac{w_id_i}{r_i}\\
&=
\boxed{
\frac{M_kd_m}{r_i-2}
}.
\end{aligned}
```

The last step uses

```math
d_i=d_0A_{0,i},
\qquad
w_i=A_{i+1,m},
\qquad
d_m=d_0A_{0,m}.
```

Because the incoming primes increase, the positive coefficients
`beta_(i,k)` strictly decrease with `i`. The linear objective is therefore
maximized by using the available Bessel budget on the indices in order.
Define

```math
\boxed{
t_{i,k}^{\star}
=
\min
\left\{
c_{i,k},
\left(
s_k-\sum_{j<i}c_{j,k}
\right)_+
\right\}.
}
```

Then the sharp prefix upper envelope implied by the joint Bessel and capacity
constraints is

```math
\boxed{
\mathcal H_k
=
\sum_{i=0}^{k-1}
\beta_{i,k}t_{i,k}^{\star}.
}
```

To see sharpness, increase `t_0` until either its cap or the total budget is
reached, then repeat with `t_1`, and so on. Moving any positive budget from a
later unsaturated coordinate to an earlier unsaturated coordinate increases
the objective. Hence no other feasible allocation has larger energy.

## Hybrid Chain Envelope

For the endpoint cut `k=0`, define

```math
\mathcal H_0=0.
```

For every cut `0<=k<=m`, apply the sharp prefix envelope to `i<k` and property
#70's individual capacity bounds to `i>=k`:

```math
\boxed{
E_b
\le
\mathcal U_k^{\mathrm{hyb}}
:=
\mathcal H_k
+
\sum_{i=k}^{m-1}\alpha_iX_i.
}
```

Therefore

```math
\boxed{
E_b
\le
\mathcal U_{\mathrm{hyb}}
:=
\min_{0\le k\le m}
\mathcal U_k^{\mathrm{hyb}}.
}
```

At `k=0`,

```math
\mathcal U_0^{\mathrm{hyb}}
=
\sum_i\alpha_iX_i
=
\mathcal U_{\mathrm{cap}}.
```

Consequently,

```math
\boxed{
\mathcal U_{\mathrm{hyb}}
\le
\mathcal U_{\mathrm{cap}}.
}
```

The hybrid theorem is never weaker than property #70.

## Exact Improvement Criterion

For a fixed positive cut `k`, the full prefix capacity vector is feasible for
the Bessel constraint exactly when

```math
\sum_{i<k}c_{i,k}\le s_k.
```

In that case `t_(i,k)^star=c_(i,k)` for every prefix coordinate and the hybrid
does not improve the capacity contribution before `k`.

If instead

```math
\boxed{
\sum_{i<k}
\frac{X_i}{M_kd_ip_ia_i}
>
s_k,
}
```

the Bessel budget excludes a positive part of the capacity box. Since every
energy coefficient is positive,

```math
\mathcal H_k
<
\sum_{i<k}\alpha_iX_i,
```

and therefore

```math
\boxed{
\mathcal U_k^{\mathrm{hyb}}
<
\mathcal U_{\mathrm{cap}}.
}
```

This criterion says exactly when a native-period cut supplies a genuine
algebraic gain.

## Survival Composition

Property #69 proves that extinction forces

```math
E_b
\ge
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}.
```

Combining that lower bound with the hybrid upper envelope gives

```math
\boxed{
\mathcal U_{\mathrm{hyb}}
<
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}
\quad\Longrightarrow\quad
N_m>0.
}
```

This implication is fully proved. What remains open is whether its antecedent
holds for an unbounded family of actual square-safe conditioned chains.

## Boundary

The theorem uses more cross-layer information than separate capacity: a
single native-period Bessel budget couples every harmful-excess coordinate
before the chosen cut. It also avoids property #71's forced use of the final
primorial by optimizing over intermediate moduli.

It does not use off-diagonal localized interval correlations, and it does not
prove a universal gain. If every normalized prefix capacity sum is at most its
remainder length, the hybrid collapses to the all-capacity envelope. Even when
the gain is strict, a separate comparison with the extinction threshold is
still required.

No empirical evidence is used in this result.

## Related

- [Harmful Capacity Separates the Energy Minimizer](harmful-capacity-separates-energy-minimizer.md)
- [Sharp Harmful-Capacity Excess Envelope](sharp-harmful-capacity-excess-envelope.md)
- [Paired Harmful-Excess CRT Orthogonality Has Primorial Scale](paired-harmful-excess-crt-orthogonality-has-primorial-scale.md)
- [Candidate #24: Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
