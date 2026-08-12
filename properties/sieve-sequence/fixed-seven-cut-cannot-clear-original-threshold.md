# Fixed Seven Cut Cannot Clear The Original Threshold

**Status:** Mathematically proved conditional envelope obstruction. Stainless
verification is not claimed.

## Meaning

The Seven-Layer Overflow Forcing property proves that the native cut immediately after filter `7` strictly
improves candidate #24's all-capacity envelope. Strict improvement and
threshold clearance are different questions.

This property performs the missing scale comparison. If candidate #17's
population threshold also holds at the next untouched layer, filter `11`,
then that one suffix capacity term already keeps the fixed-`7` hybrid envelope
above candidate #24's original conservation-only extinction threshold once
the chain has at least `37` layers.

Thus the Seven-Layer Overflow Forcing property's gain is genuine but cannot by itself finish the original
candidate through one fixed early cut. The optimized later cuts and the
capacity-relaxed extinction threshold remain open.

## Setup

Consider a conditioned chain

```math
r_0=5,
\qquad
r_1=7,
\qquad
r_2=11,
\qquad
\cdots,
\qquad
r_{m-1}<Q,
```

with

```math
Q\ge17,
\qquad
m\ge37.
```

Define

```math
D=Q^2-Q-3,
\qquad
P_i=\prod_{j<i}a_j,
\qquad
a_j=1-\frac2{r_j}.
```

Let `N_0` be the complete 2-gap-start population before filter `5`. Assume
candidate #17's local-count threshold at the filter-`11` layer, so property
#75 gives

```math
X_2\ge B_{11}^2,
\qquad
B_{11}
=
\left\lfloor\frac{D}{66}\right\rfloor+1.
```

## Untouched Filter-Eleven Suffix Term

The cut immediately after filter `7` is `k=2`. The Native-Period Hybrid Envelope property leaves every
coordinate `i>=2` under its separate capacity bound, so

```math
\mathcal U_2^{\mathrm{hyb}}
\ge
\alpha_2X_2.
```

The first three multiplicative factors are

```math
a_0=\frac35,
\qquad
a_1=\frac57,
\qquad
a_2=\frac9{11},
```

and hence

```math
P_3
=a_0a_1a_2
=\frac{27}{77}.
```

Since

```math
w_2=\frac{P_m}{P_3},
\qquad
\alpha_2=\frac{w_2}{2a_2},
```

one obtains

```math
\begin{aligned}
\alpha_2
&=
\frac{P_m}{2a_2P_3}\\
&=
\frac{P_m}{
2\cdot(9/11)\cdot(27/77)
}\\
&=
\boxed{\frac{847}{486}P_m}.
\end{aligned}
```

Also `floor(x)+1>=x`, so

```math
B_{11}\ge\frac{D}{66}.
```

Therefore

```math
\boxed{
\mathcal U_2^{\mathrm{hyb}}
\ge
\frac{847}{486}P_m
\left(\frac{D}{66}\right)^2.
}
```

## Upper Bound For The Original Threshold

Candidate #24 has

```math
T=N_0P_m.
```

Its dual sum is

```math
W_-
=
\sum_{i=0}^{m-1}\frac{P_m}{P_i}.
```

Every `0<P_i<=1`, so every summand is at least `P_m`. Hence

```math
W_-\ge mP_m.
```

Before filter `5`, every complete 2-gap start is `5 modulo 6`. A range of
diameter `D` therefore contains at most

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
\left(\frac D6+1\right)^2.
}
```

## Constant Comparison

It is sufficient to prove

```math
\frac{847}{486}
\left(\frac D{66}\right)^2
>
\frac1{2m}
\left(\frac D6+1\right)^2.
```

After rearranging, this is equivalent to

```math
m
>
\frac{29403}{847}
\left(1+\frac6D\right)^2.
```

For `Q>=17`, one has `D>=269`, so

```math
\frac{29403}{847}
\left(1+\frac6D\right)^2
\le
\frac{29403}{847}
\left(\frac{275}{269}\right)^2
<37.
```

The last strict inequality is the integer comparison

```math
29403\cdot275^2
<
37\cdot847\cdot269^2.
```

Thus `m>=37` proves

```math
\boxed{
\mathcal U_2^{\mathrm{hyb}}
>
\frac{T^2}{2W_-}.
}
```

## Consequence

Under the stated assumptions, the fixed native cut immediately after filter
`7` cannot certify candidate #24 through its original sufficient comparison

```math
\mathcal U_2^{\mathrm{hyb}}
<
\frac{T^2}{2W_-}.
```

The obstruction comes from the first untouched layer, not from failure of
the proved filter-`7` overflow. Candidate #17 makes the filter-`11` capacity
envelope wide enough that its suffix term dominates the original threshold.

## Boundary

This theorem does not prove that the actual energy `E_b` exceeds the
threshold. It proves that this particular upper envelope is too large to
certify otherwise.

It also does not address:

1. a later optimized cut `k>=3`, which brings filter `11` into the joint
   Bessel budget;
2. the Capacity Minimizer Separation property's larger capacity-relaxed threshold
   `T^2/(2W_-)+Gamma_cap`; or
3. localized residue or correlation information that reduces the actual
   suffix contribution below its capacity maximum.

The next useful algebraic move is therefore a moving-cut analysis, not a
larger estimate for the already-settled filter-`7` overflow.

No empirical evidence is used in this result.

## Related

- [Seven-Layer Floor Forces Native Overflow](seven-layer-floor-forces-native-overflow.md)
- [Seven-Layer Density Floor Maximizes Capacity Width](seven-layer-density-floor-maximizes-capacity-width.md)
- [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
- [Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
