# Fixed-Factor Survival

**Status:** Conditional mathematical theorem about constructed companion
processes. Square-window survival assumes quadratic eligible supply and blind
placement; head recurrence additionally assumes availability bounded below and
adequate cross-layer mixing. Not a claim about the real modular filter.

## Meaning

If a companion is a fixed finite multiple `w` of the random destruction rate,
it remains in the same asymptotic survival class as random filtering. There is
no largest finite constant-factor multiple of random that the model can
tolerate: twice, ten times, or one million times worse than random all survive
once `r` is large enough. The nontrivial transition begins only when the
worsening factor grows with `r`, treated in
[Logarithmic-Worsening Thresholds](logarithmic-worsening-thresholds.md).

## Setup

Builds on the [Cumulative Local Hazard Law](cumulative-local-hazard-law.md).
Let `w >= 0` be fixed and suppose `f_r = 2w/r` for all sufficiently large
filters on the tracked chain. A finite prefix is absorbed into a positive
constant.

## Property

The quadratic Taylor remainder is summable over primes, so

```math
\begin{aligned}
D_w(Q)
&=\sum_{r < Q}-\log\left(1-\frac{2w}{r}\right)
&&[\text{Definition Of }D(Q)]\\
&=2w\sum_{r < Q}\frac1r+O(1)
&&[\text{Taylor Expansion; Summable Remainder}]\\
&=2w\log\log Q+O(1).
&&[\text{Prime Harmonic Sum}]
\end{aligned}
```

Therefore

```math
P_w(Q)\asymp\frac{C_w}{(\log Q)^{2w}}.
```

For a square window with `B(Q) ~ C_0 Q^2` eligible lineages,

```math
\lambda_w(Q)
\asymp
C_0\frac{Q^2}{(\log Q)^{2w}}
\longrightarrow\infty
```

for every finite `w`. The growth is strong enough to make the standard
empty-window bound summable, so only finitely many square windows are empty
almost surely under the blind-placement premise.

For a distinguished head with baseline availability bounded below,

```math
\Pr(H_Q)\asymp\frac{C_w}{(\log Q)^{2w}},
```

and the sum over prime heads diverges for every finite `w`. Under adequate
mixing, head 2-gaps recur infinitely often almost surely.

Hence there is no finite constant-factor maximum worse than random. $\blacksquare$

## What This Does And Does Not Say

The threshold for nontrivial failure is not any finite `w`. It appears only
when `w_r` grows with `r`; the first such growth rate that changes the
conclusion is logarithmic. See
[Logarithmic-Worsening Thresholds](logarithmic-worsening-thresholds.md).
