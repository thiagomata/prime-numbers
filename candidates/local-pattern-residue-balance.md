# Local Pattern-Residue Balance

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Empirical status:** INCONCLUSIVE — window-pass deviation was low-power; the
exact stated margin `νE < N(1−ν/r)` is positive in all 1,890 measured lineage
layers across 53 heads, but the candidate still asks for a proof rather than
finite agreement. See "Empirical status (stated margin, lineage experiment)".

## Candidate Hypothesis

Fix an incoming prime `p`, a local window `J`, and a finite gap word

```math
w=(g_1,\ldots,g_m).
```

An occurrence beginning at `x` visits the vertex offsets

```math
T(w)=\{0,g_1,g_1+g_2,\ldots,g_1+\cdots+g_m\}.
```

Let `N_w(J) > 0` be the number of complete occurrences of `w` in `J`, and let
`N_{w,a}(J)` count those whose starting value is congruent to `a` modulo `p`.
The candidate is that, for every residue class `a`,

```math
\left|
N_{w,a}(J)-\frac{N_w(J)}p
\right|
\le E_p(J,w),
\qquad
E_p(J,w)\ge0.
```

The statement can be required for every finite word, for all words of bounded
length, or for another gap-agnostic family large enough for the intended
application.

## Forbidden Start Residues

Installing `p` removes an occurrence if at least one of its vertices is
congruent to zero modulo `p`. Define

```math
R_p(w)=\{-t\bmod p:t\in T(w)\},
\qquad
\nu_p(w)=|R_p(w)|.
```

The use of distinct residues is essential: different vertices can produce the
same forbidden start class. Assume

```math
\nu_p(w)<p.
```

If `K_w(J)` is the number of occurrences destroyed by the filter, the union
bound and the candidate inequality give

```math
\begin{aligned}
K_w(J)
&\le\sum_{a\in R_p(w)}N_{w,a}(J)\\
&\le\nu_p(w)
\left(\frac{N_w(J)}p+E_p(J,w)\right).
\end{aligned}
```

## Why The Candidate Is Sufficient

The number of surviving occurrences is at least

```math
\begin{aligned}
N'_w(J)
&\ge N_w(J)-K_w(J)\\
&\ge
N_w(J)\left(1-\frac{\nu_p(w)}p\right)
-\nu_p(w)E_p(J,w).
\end{aligned}
```

Therefore the gap-agnostic sufficient condition is

```math
\nu_p(w)E_p(J,w)
<
N_w(J)\left(1-\frac{\nu_p(w)}p\right).
```

It implies `N'_w(J) > 0`.

For the single-gap word `w = (d)`, the offsets are `{0,d}`. Hence

```math
\nu_p((d))=
\begin{cases}
2,&p\nmid d,\\
1,&p\mid d.
\end{cases}
```

In particular, for `d = 2` and `p > 2`, the condition becomes

```math
2E_p(J,(2))
<
N_{(2)}(J)\left(1-\frac2p\right).
```

If `J` is square-safe, the surviving occurrence certifies a twin-prime pair.
The candidate itself, however, applies uniformly to arbitrary finite gap
words.

## Minimal Two-Harmful-Class Form

For the current collision-energy program, pointwise control of every residue
class is stronger than necessary. Let

```math
G=N_{(2)}(J),
```

and define only the two harmful deviations

```math
\delta_0
=
N_{(2),0}(J)-\frac Gp,
\qquad
\delta_{-2}
=
N_{(2),-2}(J)-\frac Gp.
```

The Sampling-Density Recombination property proves that candidate #21's harmful excess and signed endpoint
imbalance are exactly

```math
b=\delta_0+\delta_{-2},
\qquad
\Delta=\delta_0-\delta_{-2}.
```

Consequently, its complete scalar cost is

```math
\boxed{
\frac{p}{2(p-2)}
\left(
\delta_0+\delta_{-2}
\right)^2
+
\frac12
\left(
\delta_0-\delta_{-2}
\right)^2.
}
```

A direct weighted aggregate bound for this expression is the most economical
restricted form of candidate #12 that reproduces candidate #21's full harmful
scalar term. It preserves correlation between the two harmful classes and can
replace the separate candidate #13 endpoint-sampling and candidate #23
strike-density estimates. It does not ask for uniformity in the other `p-2`
classes or for arbitrary gap words.

Its proof role is nevertheless terminal, not independently noncircular.
The Terminal Harmful-Excess Energy property proves that the weighted `b_i^2` component alone being below
candidate #21's complete global allowance already forces a positive final
2-gap-start population. Thus this formulation is a clean theorem target, but
proving it at the required scale would already prove conditioned-chain
survival.

Candidate #24 is leaner still. It keeps only

```math
b_i=\delta_{i,0}+\delta_{i,-2}
```

and asks for

```math
\boxed{
\sum_iw_i
\frac{p_i}{2(p_i-2)}
b_i^2
<
\frac{T^2}{2W_-}.
}
```

It discards the imbalance square and uses the larger natural allowance
because `W_-<W`. Therefore use candidate #24 as the minimal quadratic survival
target; use the full direct norm here only when the joint two-class geometry
provides additional arithmetic leverage.

The Pointwise Margin Insufficiency property proves that the candidate's existing pointwise survival margin
does not automatically supply this stronger quadratic bound. For every prime
`p>=5`, it constructs an integral residue histogram satisfying

```math
\max_a
\left|
N_{(2),a}(J)-\frac Gp
\right|
\le E
```

and

```math
2E<G\left(1-\frac2p\right),
```

while its same-sign harmful deviations lie outside candidate #21's scalar
ellipse. Thus the current margin remains sufficient for surviving one filter,
but not for the cumulative second-moment proof.

The stronger direct target is

```math
\boxed{
\sum_iw_i
\left[
\frac{p_i}{2(p_i-2)}
(\delta_{i,0}+\delta_{i,-2})^2
+
\frac12(\delta_{i,0}-\delta_{i,-2})^2
\right]
\le
\mathcal B_{\mathrm{harm}}(Q),
}
```

with `mathcal B_harm(Q)` small enough to fit candidate #21 after harmless
dispersion is inserted. Because this bound contains the harmful-excess square,
The Terminal Harmful-Excess Energy property shows that it is already terminal whenever
`mathcal B_harm(Q)<T^2/(2W)`.

The Harmful-Residue Box Bound property computes the sharp conversion from the original pointwise
deviation language to this ellipse. If

```math
|\delta_0|,|\delta_{-2}|\le E,
```

then

```math
\boxed{
\frac{p}{2(p-2)}
(\delta_0+\delta_{-2})^2
+
\frac12(\delta_0-\delta_{-2})^2
\le
\frac{2p}{p-2}E^2.
}
```

For a one-layer main term

```math
T=G\left(1-\frac2p\right),
```

the largest symmetric pointwise box strictly inside candidate #21's ellipse
is exactly

```math
\boxed{
E<
\frac T2\sqrt{\frac{p-2}{p}}.
}
```

The candidate's existing survival margin is `E<T/2`; the additional square
root factor is the exact price of controlling the same-sign harmful
direction in the second-moment argument.

The Sixfold-Capacity Energy Envelope property gives a deterministic alternative that does not assume a
deviation bound. If every residue class has the sixfold capacity

```math
B
=
\left\lfloor
\frac{Q^2-Q-3}{6p}
\right\rfloor+1,
```

put

```math
\ell=\max(0,G-(p-2)B),
\qquad
u=\min(G,2B).
```

Then the sharp harmful scalar maximum allowed by the total population and
these class capacities is

```math
\boxed{
\max_{s\in\mathcal S}
\left[
\frac{p}{2(p-2)}
\left(
s-\frac{2G}{p}
\right)^2
+
\frac12\min(s,2B-s)^2
\right],
}
```

where

```math
\mathcal S
=
\{\ell,u\}
\cup
\left(
\{B\}\text{ if }\ell\le B\le u
\right).
```

This controls the scalar ellipse exactly when the displayed maximum is below
`G^2(1-2/p)^2/2`. The Sixfold Population-Ratio Threshold property solves that comparison. Define

```math
\rho_*(p)
=
\frac{2p\sqrt p}{2\sqrt p+(p-2)^{3/2}}.
```

Then the capacity envelope fits the scalar ellipse exactly when

```math
\boxed{G>\rho_*(p)B.}
```

For every `p>=5`,

```math
2<\rho_*(p)<3,
\qquad
\lim_{p\to\infty}\rho_*(p)=2.
```

Thus the missing population theorem is now quantitative: ordinary
two-harmful-class survival asks for `G>2B`, while the collision budget asks
for the slightly stronger sharp ratio above at one layer.

The One-Layer Ellipse Non-Composition property proves that meeting this ratio at every layer does not
automatically fit candidate #21's global weighted allowance. The cumulative
target can still be stated as the direct aggregate theorem

```math
\sum_iw_i
\left[
\frac{p_i}{2(p_i-2)}
(\delta_{i,0}+\delta_{i,-2})^2
+
\frac12(\delta_{i,0}-\delta_{i,-2})^2
\right]
<
\mathcal B_{\mathrm{harm}}(Q).
```

Thus the ratio theorem classifies local capacity. A proof of the aggregate
bound would need new weighted cross-layer information, but the Terminal Harmful-Excess Energy property shows
that such a proof is already a terminal survival theorem rather than one
independent component to be combined later. Candidate #24 supplies the weaker
global target when control of left/right imbalance is unnecessary.

## Relation To Other Candidates

This is a deterministic, phase-sensitive equidistribution condition. It asks
how each old local pattern is distributed across the actual residue classes
used by the filter. That differs from comparing the deterministic filter with
a probabilistic model.

- [Uniform local observable sampling](uniform-local-observable-sampling.md)
  compares the hit set with the whole local population.
- [Random-like merge survival](random-like-merge-survival.md) compares marked
  local behavior with selected random benchmarks.

## Established Inputs

- [Copy-index filter frequency](../properties/sieve-sequence/copy-index-filter-frequency.md)
- [Stable absence and copy-or-merge](../properties/sieve-sequence/absence-of-two-gaps-is-stable.md)
- [Endpoint sampling and strike density recombine into harmful residues](
  ../properties/sieve-sequence/endpoint-sampling-strike-density-harmful-residue-bridge.md
  )
- [Pointwise two-class margin does not imply the collision budget](
  ../properties/sieve-sequence/pointwise-two-class-margin-does-not-imply-collision-budget.md
  )
- [Sharp harmful-residue box inside the collision ellipse](
  ../properties/sieve-sequence/sharp-harmful-residue-box-inside-collision-ellipse.md
  )
- [Sharp sixfold-capacity harmful-energy envelope](
  ../properties/sieve-sequence/sharp-sixfold-capacity-harmful-energy-envelope.md
  )
- [Sharp sixfold-capacity population-ratio threshold](
  ../properties/sieve-sequence/sharp-sixfold-capacity-population-ratio-threshold.md
  )
- [One-layer harmful ellipses do not compose](
  ../properties/sieve-sequence/one-layer-harmful-ellipses-do-not-compose.md
  )
- [Weighted harmful-excess energy is already terminal](
  ../properties/sieve-sequence/weighted-harmful-excess-energy-is-terminal.md
  )
- [Weighted harmful-excess quadratic survival](
  weighted-harmful-excess-quadratic-survival.md
  )
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

Complete-period residue counts do not prove this bound in a short window.
Pointwise balance for every residue class and every finite word is a strong
local equidistribution demand; a useful proof may need a bounded word family,
averaging over stages, or a weaker norm. Matching only the average numerical
gap or average merge size is insufficient because it does not prevent the
filter from concentrating on one local pattern.

## Empirical status (window scale, p to ~19000)

Source: `empirical/sieve-sequence/src/sieve_sequence_empirical/window_cli.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantity: for the word `w=(2)`, `residue_max_dev =
max_a |N_{w,a} - N_w/p|`, the worst deviation of any residue class's 2-gap-start
count from uniform. **Low-power measurement**: one window is a small sample of
the whole residue distribution, so this is a weak test of the candidate.

The first interpretation of this column was not justified. It divided the
maximum deviation by `sqrt(G_local)` and concluded that the residue
distribution approaches uniform. With `p` residue classes, however, the
random-reference scale for a maximum cell deviation depends on both the
typical cell count `G_local/p` and an extreme-value factor such as `log p`
(up to model-dependent constants). Dividing by `sqrt(G_local)` alone can shrink
even without any improving equidistribution.

| quantity | dense (p 5..991) | sparse (p ~1000..19000) | trend |
|----------|------------------|--------------------------|-------|
| `residue_max_dev` (absolute) | med 6.2, max 10.3 | med 43.2, max 73.7 | grows p^(+0.54), r=+0.97 |
| `residue_max_dev / sqrt(G_local)` (insufficient normalization) | med 0.14, max 0.43 | med 0.067, max 0.096 | shrinks p^(-0.09), r=-0.87 |

The table remains a descriptive diagnostic, but neither “approaches uniform”
nor an unfavorable verdict follows from it.

### What must be measured

The direct empirical test is the candidate's own sufficient margin:

```math
\nu_p(w)E_p(J,w)
<
N_w(J)\left(1-\frac{\nu_p(w)}p\right).
```

For `w=(2)`, use `nu=2`, `E=residue_max_dev`, and `N=G_local`, and report the
signed margin at every transition. Then extend the measurement to a bounded,
gap-agnostic word family or to the smaller collection of residue sums that
actually controls harmful filter hits.

## Strategic assessment after empirical review

The present data is **inconclusive**, not favorable or unfavorable. This
candidate nevertheless remains a promising arithmetic mechanism because it
can explain why the filter cannot cherry-pick every locally useful pattern.
The universal “every finite word” version is probably stronger than necessary;
a bounded word family with an explicit margin, measured after conditioning on
earlier filters, is the higher-priority formulation.

## Empirical status (stated margin, lineage experiment)

The candidate's OWN sufficient margin `nu E < N(1 - nu/r)` (for the word
`(2)`, with `nu=2` forbidden classes and `E` the worst residue-class excess)
was measured per layer by the fixed-future-window lineage experiment
(`empirical/sieve-sequence/src/sieve_sequence_empirical/lineage_cli.py`), replacing the earlier `sqrt(G_local)`
normalization that was flagged as insufficient.

**Q=101, 24 layers:** the margin `N(1 - nu/r) - nu E` is **positive at 24/24
layers**, ranging from `+192` (final layer, r=97) to `+1683` (layer 0). It
shrinks across the chain but stays well clear of zero. No layer failed.

**Expanded exact sweep (53 heads, 1,890 layers):** using the same exact
lineage library in-memory on every prime head `17<=Q<=251`, together with
`307,401,503,701,997`, the margin stayed positive at **1,890/1,890** measured
layers. The smallest observed margin was `+12`, at `Q=17`, `r=13`, with
`G_r(W_Q)=18`. No exact layer failure was found.

This is a stronger statement than the window-pass single-transition
measurement: it tests the candidate's stated condition (not a proxy
normalization) and does so after conditioning on every preceding filter. Honest
scope: 53 finite heads still do not prove the margin holds for all `Q`. What
remains open is a proof or a sharper bounded-word reformulation, not whether
the Q101 chain was exceptional.
