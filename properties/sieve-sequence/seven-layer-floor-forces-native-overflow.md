# Seven-Layer Floor Forces Native Overflow

**Status:** Mathematically proved unconditional envelope improvement.
Stainless verification is not claimed.

## Meaning

The Seven-Layer Density Floor property shows that candidate #17's local-count threshold maximizes the
population-slack floor used by candidate #24. At the first proved layer,
`r=7`, that threshold is already unconditional. This property inserts the
result into the exact native-period Bessel normalization.

The outcome is a uniform positive result: for every sufficiently large future
head, the native cut immediately after filter `7` strictly improves the
all-capacity harmful-energy envelope.

This proves a genuine cross-layer gain, not survival. The remaining question
is whether the quantified gain is large enough to clear candidate #24's
extinction deficit.

## Setup

Let

```math
Q\ge36,
\qquad
D=Q^2-Q-3,
\qquad
H=D+1=Q^2-Q-2.
```

Here `D` is the diameter of the possible 2-gap starts, while `H` is the
number of integers in the start interval `[Q,Q^2-2)`. the Native-Period Hybrid Envelope property's Bessel
remainder uses the interval length `H`, not the diameter `D`.

Consider the conditioned chain beginning with

```math
r_0=5,
\qquad
r_1=7.
```

The cut immediately after filter `7` is therefore `k=2`, and its native
modulus is

```math
M=2\cdot3\cdot5\cdot7=210.
```

Write

```math
s=H\bmod210,
\qquad
0\le s\le209,
```

and let the one-class filter-`7` capacity be

```math
B
=
\left\lfloor\frac{D}{42}\right\rfloor+1.
```

## Exact Filter-Seven Native Norm

Immediately before filter `7`, the complete 2-gap starts occupy the three
classes

```math
11,17,29\pmod{30}.
```

Their complete-period density is therefore

```math
d=\frac3{30}=\frac1{10}.
```

For the incoming prime `7`, the Native-Period Hybrid Envelope property uses

```math
p=\frac27,
\qquad
a=1-p=\frac57.
```

The exact squared norm of the filter-`7` harmful-excess coordinate over the
native modulus `210` is consequently

```math
\begin{aligned}
q
&=Mdpa\\
&=210\cdot\frac1{10}\cdot\frac27\cdot\frac57\\
&=\boxed{\frac{30}{7}}.
\end{aligned}
```

## Unconditional Width Floor At Seven

The Local Count Shot-Capacity Premise property proves candidate #17's local-count threshold at `r=7` for every
integer `Q>=17`. The Seven-Layer Density Floor property therefore applies and gives

```math
\sigma_7=2B,
\qquad
X_7\ge B^2.
```

The exact norm above is `q_(1,2)`. The filter-`5` capacity term is
nonnegative, so the Native-Period Capacity Overflow property's normalized overflow at cut `k=2` satisfies

```math
\begin{aligned}
e_2
&=
\left(
\sum_{i<2}\frac{X_i}{q_{i,2}}-s
\right)_+\\
&\ge
\left(
\frac{X_1}{q_{1,2}}-s
\right)_+\\
&\ge
\boxed{
\left(
\frac{7B^2}{30}-s
\right)_+}.
\end{aligned}
```

## Positive Overflow For Every Large Head

For `Q>=36`,

```math
D
=Q^2-Q-3
\ge36^2-36-3
=1257.
```

Therefore

```math
B
=
\left\lfloor\frac{D}{42}\right\rfloor+1
\ge
\left\lfloor\frac{1257}{42}\right\rfloor+1
=30.
```

It follows that

```math
\frac{7B^2}{30}
\ge
\frac{7\cdot30^2}{30}
=210.
```

Since `s<=209`,

```math
\boxed{e_2\ge1>0.}
```

The Native-Period Capacity Overflow property proves that positive overflow is equivalent to a strict gain at
that cut. Thus

```math
\boxed{
\mathcal U_2^{\mathrm{hyb}}
<
\mathcal U_{\mathrm{cap}}
}
```

for every integer `Q>=36`. In particular, it holds for every future prime
head `Q>=37`.

## Quantified Gain

The Native-Period Capacity Overflow property also converts the overflow into an explicit energy-envelope
reduction. If `d_m` is the final paired-survivor density, the smallest prefix
coefficient at this cut is the filter-`7` coefficient, so

```math
\begin{aligned}
\Delta_2
&\ge
\frac{210d_m}{7-2}e_2\\
&=
\boxed{42d_m e_2}\\
&\ge
42d_m.
\end{aligned}
```

The sharper explicit form is

```math
\boxed{
\Delta_2
\ge
42d_m
\left(
\frac{7B^2}{30}-(H\bmod210)
\right)_+.
}
```

## Boundary

This theorem removes the first uncertainty identified after the Envelope Width Floor property:
native-period overflow is not merely possible or empirically suggested. It is
provably positive from the first established density floor.

Positivity alone is insufficient for candidate #24. The hybrid envelope can
remain above the extinction threshold even after a strict reduction. The next
audit must compare the quantified reduction

```math
42d_m e_2
```

with the exact remaining deficit

```math
\mathcal U_{\mathrm{cap}}
-
\left(
\frac{T^2}{2W_-}+\Gamma_{\mathrm{cap}}
\right).
```

No empirical evidence is used in this result.

## Related

- [Exact Seven-Layer Capacity Floor](exact-seven-layer-capacity-floor.md)
- [Seven-Layer Density Floor Maximizes Capacity Width](seven-layer-density-floor-maximizes-capacity-width.md)
- [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
- [Native-Period Capacity Overflow Quantifies the Hybrid Gain](native-period-capacity-overflow-quantifies-hybrid-gain.md)
- [Candidate #24: Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
