# Every Fixed Native Cut Fails The Original Threshold

**Status:** Mathematically proved conditional envelope obstruction. Stainless
verification is not claimed.

## Meaning

The Filter-Seven Cut Failure property proves that the fixed native cut after filter `7` cannot clear
candidate #24's original conservation-only threshold on sufficiently long
chains. This property gives the exact arbitrary-cut form.

If candidate #17's population threshold holds at the first layer left outside
a native cut, then that one untouched capacity term eventually exceeds the
original threshold. Consequently, no cut at a fixed layer can certify
candidate #24 along chains whose lengths grow without bound. Any viable
native cut must move outward with the future head.

This is an obstruction for the capacity-based hybrid envelope. It is not a
lower bound for the actual harmful-excess energy.

## Setup

Consider a conditioned chain

```math
r_0=5<r_1<\cdots<r_{m-1}<Q
```

with

```math
Q\ge17,
\qquad
2\le k<m.
```

Define

```math
D=Q^2-Q-3,
\qquad
a_i=1-\frac2{r_i},
\qquad
P_i=\prod_{j<i}a_j.
```

Let `N_0` be the complete 2-gap-start population before filter `5`. Assume
candidate #17's local-count threshold at the first layer outside the cut,
namely `r_k`. The Seven-Layer Density Floor property then gives

```math
X_k\ge B_k^2,
\qquad
B_k
=
\left\lfloor\frac{D}{6r_k}\right\rfloor+1.
```

## First Untouched Suffix Term

The Native-Period Hybrid Envelope property writes the hybrid envelope at cut `k` as a nonnegative prefix
term plus the separate capacity terms with indices `i>=k`. Therefore

```math
\boxed{
\mathcal U_k^{\mathrm{hyb}}
\ge
\alpha_kX_k.
}
```

Since

```math
w_k
=
A_{k+1,m}
=
\frac{P_m}{P_{k+1}}
```

and `P_(k+1)=P_k a_k`, the energy coefficient is

```math
\begin{aligned}
\alpha_k
&=
\frac{w_k}{2a_k}\\
&=
\boxed{
\frac{P_m}{2P_ka_k^2}
}.
\end{aligned}
```

Also `floor(x)+1>=x`, so

```math
B_k\ge\frac{D}{6r_k}.
```

It follows that

```math
\boxed{
\mathcal U_k^{\mathrm{hyb}}
\ge
\frac{P_mD^2}{72P_ka_k^2r_k^2}.
}
```

## Original Threshold Upper Bound

Candidate #24 has

```math
T=N_0P_m,
\qquad
W_-
=
\sum_{i=0}^{m-1}\frac{P_m}{P_i}.
```

Every `P_i<=1`, so

```math
W_-\ge mP_m.
```

Before filter `5`, complete 2-gap starts occupy one residue class modulo `6`.
Thus

```math
N_0
\le
\left\lfloor\frac D6\right\rfloor+1
\le
\frac D6+1.
```

Consequently,

```math
\boxed{
\frac{T^2}{2W_-}
\le
\frac{P_m}{2m}
\left(
\frac D6+1
\right)^2.
}
```

## Exact Fixed-Cut Obstruction

The suffix lower bound exceeds the threshold upper bound whenever

```math
\frac{P_mD^2}{72P_ka_k^2r_k^2}
>
\frac{P_m}{2m}
\left(
\frac D6+1
\right)^2.
```

Canceling `P_m>0` and rearranging gives

```math
m
>
P_ka_k^2r_k^2
\left(
1+\frac6D
\right)^2.
```

Because `a_kr_k=r_k-2`, this becomes the exact criterion

```math
\boxed{
m
>
P_k(r_k-2)^2
\left(
1+\frac6D
\right)^2
\quad\Longrightarrow\quad
\mathcal U_k^{\mathrm{hyb}}
>
\frac{T^2}{2W_-}.
}
```

Equivalently, a necessary condition for this hybrid cut to clear the original
threshold is

```math
\boxed{
\mathcal U_k^{\mathrm{hyb}}
<
\frac{T^2}{2W_-}
\quad\Longrightarrow\quad
m
\le
P_k(r_k-2)^2
\left(
1+\frac6D
\right)^2.
}
```

## Every Fixed Cut Eventually Fails

Fix one index `k`. The prefix prime `r_k` and product `P_k` are then constants,
while

```math
\left(1+\frac6D\right)^2
\longrightarrow1
```

as `Q` grows. The right side of the necessary condition remains bounded.
Therefore, along any family whose number of filter layers `m` tends to
infinity, the fixed cut eventually violates that condition and cannot clear
the original threshold.

Thus

```math
\boxed{
\text{a native cut capable of clearing the original threshold must have }
k=k(Q)\longrightarrow\infty.
}
```

This is a necessary movement condition, not a sufficient growth rate.

## Elementary Lower Bound For The Cut Prime

The exact necessary condition also gives a parameter-free lower bound for the
prime at the cut. Because `k>=2`,

```math
P_k
\le
P_2
=
\frac35\frac57
=
\frac37.
```

Therefore threshold clearance would require

```math
m
\le
\frac37(r_k-2)^2
\left(
1+\frac6D
\right)^2.
```

Solving for `r_k` gives

```math
\boxed{
\mathcal U_k^{\mathrm{hyb}}
<
\frac{T^2}{2W_-}
\quad\Longrightarrow\quad
r_k
\ge
2
+
\frac{
\sqrt{7m/3}
}{
1+6/D
}.
}
```

Thus the prime at a potentially successful native cut must grow at least on
the order of `sqrt(m)`. This uses no estimate for the distribution of primes
and does not convert the prime bound into a sufficient bound on the cut index.

## Recovery Of the Filter-Seven Cut Failure property

For the cut after filter `7`, one has

```math
k=2,
\qquad
r_2=11,
\qquad
P_2=\frac35\frac57=\frac37.
```

Hence

```math
P_2(r_2-2)^2
=
\frac37\cdot9^2
=
\frac{243}{7}
=
\frac{29403}{847}.
```

The general criterion therefore recovers the Filter-Seven Cut Failure property's constant exactly.

## Boundary

The theorem assumes candidate #17's local-count threshold only at the first
layer outside the selected cut. It does not prove that threshold.

It rules out only the original comparison

```math
\mathcal U_k^{\mathrm{hyb}}
<
\frac{T^2}{2W_-}.
```

It does not address:

1. the Capacity Minimizer Separation property's larger capacity-relaxed threshold
   `T^2/(2W_-)+Gamma_cap`;
2. a cut `k(Q)` growing with the chain;
3. the exact greedy envelope using additional realized structure; or
4. localized residue information that replaces `X_k` by a smaller suffix
   upper bound.

The next algebraic question is quantitative: how quickly must `r_k` grow
relative to `m` for the necessary condition to remain possible, and can a
moving native-period Bessel budget still control the growing prefix?

No empirical evidence is used in this result.

## Related

- [Fixed Seven Cut Cannot Clear The Original Threshold](fixed-seven-cut-cannot-clear-original-threshold.md)
- [Seven-Layer Density Floor Maximizes Capacity Width](seven-layer-density-floor-maximizes-capacity-width.md)
- [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
- [Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
