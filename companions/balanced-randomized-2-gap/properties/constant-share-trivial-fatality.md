# Constant-Share Trivial Fatality

**Status:** Conditional mathematical consequence of the
[Bad/Random Square-Window Boundary](bad-random-square-window-boundary.md).
Not a claim about the real modular filter.

## Meaning

A fixed positive adversarial share repeated at every filter is locally fatal
for a trivial reason: the cumulative budget `A(Q)` grows like `Q / log Q`,
far faster than the square-window critical budget `2 log Q`. This is why the
fixed-share question gives the wrong answer to "how much worse than random can
the filter be?" — random destruction itself shrinks as `2/r`, while a fixed
share adds a positive floor and makes the relative factor `w_r` diverge
linearly.

## Setup

Suppose one fixed share `0 < alpha < 1` is adversarial at every filter.

## Property

```math
\begin{aligned}
A(Q)
&=-\pi(Q)\log(1-\alpha)
&&[\text{Constant Share}]\\
&\asymp
\bigl[-\log(1-\alpha)\bigr]\frac{Q}{\log Q}.
&&[\text{Prime Number Theorem}]
\end{aligned}
```

Since `Q / log Q` grows faster than `log Q`, this lies far above the
square-window critical budget. Hence

```math
\begin{aligned}
\lambda_Q^{(\alpha)}
&\asymp
C\frac{Q^2}{(\log Q)^2}(1-\alpha)^{\pi(Q)}\\
&\longrightarrow0.
&&[\text{Exponential Loss Beats Quadratic Growth}]
\end{aligned}
```

Every fixed positive per-filter adversarial share is locally fatal for the
repeated-mixture projection, even though the complete-period population
continues to grow without bound. $\blacksquare$

## Equivalence To Relative-Hazard Language

In relative-factor terms, a fixed `alpha` makes

```math
w_r=1+\frac{r-2}{2}\alpha\sim\frac{\alpha r}{2},
```

an increasingly severe multiple of the shrinking random rate. This is the same
fact viewed through `w_r`: it grows linearly, well past the
[Logarithmic-Worsening](../../properties/logarithmic-worsening-thresholds.md)
frontier. The nontrivial question is how rapidly `w_r` itself may grow, not
what fixed `alpha` is tolerable.

## What This Does And Not Say

This is different from applying one adversarial dilution after all random
filters have finished. A one-time dilution multiplies the final count by
`1 - alpha` once; the repeated model multiplies it once per prime. Confusing
these two experiments reverses the asymptotic conclusion.
