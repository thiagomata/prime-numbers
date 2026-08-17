# Logarithmic-Worsening Thresholds

**Status:** Conditional mathematical theorem about constructed companion
processes. Uses the quadratic-supply, availability, and mixing premises of
[Fixed-Factor Survival](fixed-factor-survival.md). Not a claim about the real
modular filter.

## Meaning

When the worse-than-random factor grows logarithmically, the model separates
into two phase boundaries: square-window survival fails at one coefficient and
head recurrence fails at a strictly smaller one. The intermediate regime keeps
windows populated while losing infinitely-recurring head 2-gaps.

## Setup

Builds on the [Cumulative Local Hazard Law](cumulative-local-hazard-law.md).
Set

```math
w_r=1+c\log r,
\qquad c\ge0.
```

The total local destruction rate is

```math
f_r
=\frac{2w_r}{r}
=\frac2r+2c\frac{\log r}{r}.
```

## Property

Prime summation gives

```math
\begin{aligned}
D_c(Q)
&=\sum_{r < Q}-\log(1-f_r)
&&[\text{Definition Of }D(Q)]\\
&=2\sum_{r<Q}\frac1r
\;+\;2c\sum_{r<Q}\frac{\log r}{r}+O(1)
&&[\text{Substitution; Summable Remainder}]\\
&=2\log\log Q+2c\log Q+O(1).
&&[\text{Prime-Sum Asymptotics}]
\end{aligned}
```

Hence

```math
P_c(Q)
\asymp
\frac{C_c}{Q^{2c}(\log Q)^2}.
```

For a quadratic square-window supply,

```math
\lambda_c(Q)
\asymp
C_0\frac{Q^{2-2c}}{(\log Q)^2}.
```

Therefore

```math
\begin{aligned}
c < 1
&\Longrightarrow
\text{eventually nonempty square windows almost surely},\\
c\ge1
&\Longrightarrow
\text{square-window expectation tends to zero}.
\end{aligned}
```

For the head, summing over prime heads has the same convergence behavior as

```math
\int^\infty
\frac{dx}{x^{2c}(\log x)^3},
```

which converges at `c = 1/2` and diverges for `c < 1/2`. Therefore

```math
\begin{aligned}
c < \frac12
&\Longrightarrow
\text{infinitely many head events almost surely, with mixing},\\
c\ge\frac12
&\Longrightarrow
\text{only finitely many head events almost surely}.
\end{aligned}
```

$\blacksquare$

## Robust Frontier Summary

Equivalently, the robust relative-factor regimes are

```math
\begin{aligned}
w_r&<(1-\varepsilon)\log r
&&[\text{Square-Window Survival}],\\
w_r&<\left(\frac12-\varepsilon\right)\log r
&&[\text{Head Recurrence}],
\end{aligned}
```

up to the asymptotically negligible additive random baseline. In terms of the
total segment destruction fraction,

```math
\begin{aligned}
f_r&<(2-\varepsilon)\frac{\log r}{r}
&&[\text{Square-Window Survival}],\\
f_r&<(1-\varepsilon)\frac{\log r}{r}
&&[\text{Head Recurrence}].
\end{aligned}
```

These are cumulative asymptotic regimes, not pointwise allowances that reset at
each filter. Irregular schedules must be evaluated through `D(Q)`.

## What This Does And Does Not Say

The `c = 1/2` boundary is on the failure side for the head because the
remaining `(log Q)^{-2}` factor makes the boundary prime series converge
(`int dx/(x (log x)^3) < infinity`). For square windows the `c = 1` boundary
reflects quadratic supply dominating logarithmic losses. The intermediate
range `(1/2) log r ~ w_r < log r` preserves windows but not infinitely
recurring head hits.
