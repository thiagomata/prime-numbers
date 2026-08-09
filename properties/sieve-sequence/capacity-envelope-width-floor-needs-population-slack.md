# Capacity-Envelope Width Floor Needs Population Slack

**Status:** Mathematically proved conditioned-chain boundary. Stainless
verification is not claimed.

## Meaning

Property #73 reduces the useful native-period gain to a lower bound for the
normalized capacity overflow `e_k`. This property extracts the strongest
immediate lower bound supplied by the geometry of property #70's feasible
harmful-count interval.

The sharp squared harmful-excess envelope is at least one quarter of the
feasible interval width squared. That width is exactly the minimum distance of
the current population from empty capacity, the two-harmful-class ceiling,
and full residue capacity.

This gives a concrete overflow floor from actual population slack. It also
proves an obstruction: the envelope vanishes at both the empty population and
the fully occupied feasible population. Therefore the filter prime and class
capacity alone cannot force a positive overflow.

## One-Layer Setup

Let `r>=5`, let `B>=0` be the common capacity of each residue class, and let
the current population satisfy

```math
0\le N\le rB.
```

Property #70 proves that the total harmful count `K` lies in

```math
\ell
=
\max(0,N-(r-2)B),
\qquad
u
=
\min(N,2B).
```

Write

```math
\mu=\frac{2N}{r}.
```

The sharp capacity-only envelope for the squared harmful excess
`b=K-mu` is

```math
X
=
\max
\left\{
(\ell-\mu)^2,
(u-\mu)^2
\right\}.
```

## Exact Midpoint Form

Let

```math
c=\frac{\ell+u}{2},
\qquad
h=\frac{u-\ell}{2}.
```

Then `ell=c-h` and `u=c+h`. The farther endpoint from `mu` has distance

```math
\max
\left(
|\mu-(c-h)|,
|\mu-(c+h)|
\right)
=
h+|\mu-c|.
```

Therefore

```math
\boxed{
X
=
\left(
\frac{u-\ell}{2}
+
\left|
\frac{2N}{r}
-
\frac{\ell+u}{2}
\right|
\right)^2.
}
```

In particular,

```math
\boxed{
X\ge\frac{(u-\ell)^2}{4}.
}
```

Equality holds exactly when the multiplicative center `2N/r` is the midpoint
of the feasible harmful-count interval.

## Exact Feasible Width

The interval width has the closed form

```math
\boxed{
u-\ell
=
\min(N,2B,rB-N).
}
```

This follows by splitting the feasible range into three parts.

If `0<=N<=2B`, then

```math
u=N,
\qquad
\ell=0,
\qquad
u-\ell=N.
```

If `2B<=N<=rB-2B=(r-2)B`, then

```math
u=2B,
\qquad
\ell=0,
\qquad
u-\ell=2B.
```

If `(r-2)B<=N<=rB`, then

```math
u=2B,
\qquad
\ell=N-(r-2)B,
\qquad
u-\ell=rB-N.
```

At the shared endpoints the formulas agree. Combining the cases proves the
displayed minimum formula.

Consequently,

```math
\boxed{
X
\ge
\frac14
\min(N,2B,rB-N)^2.
}
```

## Zero Characterization

Assume `B>0`. Since `X` is the maximum of two squares,

```math
X=0
```

if and only if both endpoints equal `mu`. This requires `u-ell=0`. By the
width formula,

```math
\min(N,2B,rB-N)=0.
```

Because `2B>0` and `0<=N<=rB`, this occurs exactly when

```math
N=0
\qquad\text{or}\qquad
N=rB.
```

At `N=0`, one has `ell=u=mu=0`. At `N=rB`, one has
`ell=u=mu=2B`. Hence

```math
\boxed{
X=0
\quad\Longleftrightarrow\quad
N\in\{0,rB\}.
}
```

If `B=0`, feasibility already forces `N=0`, and again `X=0`.

Thus even the assumption `N>0` cannot yield a positive lower bound from
`r,B` alone: the fully occupied profile `N=rB` is positive and has zero
capacity envelope.

## Conditioned-Chain Overflow Floor

For layer `i`, define the population slack

```math
\sigma_i
:=
\min(N_i,2B_i,r_iB_i-N_i).
```

Then

```math
X_i\ge\frac{\sigma_i^2}{4}.
```

Property #73 defines

```math
e_k
=
\left(
\sum_{i<k}
\frac{X_i}{M_kd_ip_ia_i}
-
s_k
\right)_+.
```

Monotonicity of the positive part gives the explicit lower bound

```math
\boxed{
e_k
\ge
\underline e_k
:=
\left(
\sum_{i<k}
\frac{\sigma_i^2}{4M_kd_ip_ia_i}
-
s_k
\right)_+.
}
```

Property #73 also proves that the hybrid gain at cut `k` satisfies

```math
\Delta_k
\ge
\frac{M_kd_m}{r_{k-1}-2}e_k.
```

Therefore

```math
\boxed{
\Delta_k
\ge
\frac{M_kd_m}{r_{k-1}-2}\underline e_k.
}
```

## Survival Composition

Combining the population-slack gain with properties #69 and #73 gives the
proved sufficient condition

```math
\boxed{
\mathcal U_{\mathrm{cap}}
-
\max_{1\le k\le m}
\left[
\frac{M_kd_m}{r_{k-1}-2}\underline e_k
\right]
<
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}
\quad\Longrightarrow\quad
N_m>0.
}
```

The implication is unconditional once the actual conditioned populations are
supplied.

## Boundary

This theorem gives an algebraic lower bound for the overflow, but not a
population-free one. It is positive only when a prefix has enough aggregate
population slack to overfill its native interval-remainder budget.

No theorem using only `r_i` and `B_i` can obtain a strictly positive universal
floor through this envelope, because `N_i=0` and `N_i=r_iB_i` both make the
one-layer contribution vanish. Further progress must quantitatively keep
some realized populations away from both extremes, or use localized residue
information not represented by the capacity interval.

No empirical evidence is used in this result.

## Related

- [Sharp Harmful-Capacity Excess Envelope](sharp-harmful-capacity-excess-envelope.md)
- [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
- [Native-Period Capacity Overflow Quantifies the Hybrid Gain](native-period-capacity-overflow-quantifies-hybrid-gain.md)
- [Candidate #24: Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
