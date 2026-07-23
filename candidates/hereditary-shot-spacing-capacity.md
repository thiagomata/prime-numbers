# Hereditary Shot-Spacing Capacity

**Shot geometry:** Mathematically proved for one filter layer.

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Purpose

An incoming prime cannot choose arbitrary accepted values to remove. Its shot
count is fixed, and the numerical distances between consecutive shots are a
scaled copy of the current accepted cofactor gaps. This candidate asks whether
that rigid capacity remains insufficient to cover every relevant local pattern
after conditioning on all preceding future filters.

## Proved One-Layer Shot Geometry

Consider the actual accepted set immediately before installing an incoming
prime `r`. In canonical residue coordinates, let its modulus be `M_r` and its
accepted cofactor residues be

```math
0\le e_0<e_1<\cdots<e_{T_r-1}<M_r.
```

Define the cyclic cofactor gaps by

```math
g_i=
\begin{cases}
e_{i+1}-e_i,&0\le i<T_r-1,\\
M_r+e_0-e_{T_r-1},&i=T_r-1.
\end{cases}
```

The accepted multiples removed by filter `r` form the bi-infinite ordered shot
set

```math
h_{nT_r+i}=r(e_i+nM_r),
\qquad
n\in\mathbb Z,
\quad
0\le i<T_r.
```

A rotation or translation used by the stage representation changes the origin,
not the cyclic distances. With periodic indexing on `g`, the consecutive shot
gaps are exactly

```math
\Delta_{nT_r+i}
=h_{nT_r+i+1}-h_{nT_r+i}
=r g_i.
```

Consequently, every complete numerical period of length `rM_r` contains
exactly `T_r` shots, and

```math
\sum_{i=0}^{T_r-1}\Delta_i=rM_r.
```

Thus the filter has both a fixed number of shots and a fixed cyclic spacing
word. It cannot relocate them independently.

## Exact Spacing Capacity

For `2\le k\le T_r`, define the minimum span of `k` consecutive shots:

```math
\sigma_r(k)
=
\min_{0\le i<T_r}
\sum_{t=0}^{k-2}\Delta_{i+t},
```

where the indices of `Delta` are periodic. This uses `k-1` consecutive shot
gaps, as required to span `k` ordered shots.

Let

```math
J=[u,v),
\qquad
\operatorname{len}(J)=v-u
```

be a half-open numerical interval. If

```math
\operatorname{len}(J)<\sigma_r(k),
```

then `J` contains at most `k-1` shots. Otherwise, its first and kth shots would
have a span smaller than `sigma_r(k)`, contradicting the definition.

This is stronger than knowing only the total shot count or average shot
distance: it controls consecutive partial sums of the actual shot-gap word.

## Hereditary Candidate Hypothesis

Fix a future prime head `q` and an earlier stage after filter `3`. Process every
not-yet-installed prime `r<q` in order. At each layer:

1. use the actual accepted population remaining after every preceding filter;
2. construct that layer's current `M_r`, `T_r`, and shot capacity
   `sigma_r`;
3. count only 2-gaps that are complete inside the chosen interval.

The candidate is that, at every layer in this finite chain, there exist an
integer `k_r` and a half-open interval

```math
J_r\subseteq[q,q^2),
\qquad
2\le k_r\le T_r,
```

such that

```math
G_r(J_r)\ge k_r
\qquad\text{and}\qquad
\operatorname{len}(J_r)<\sigma_r(k_r).
```

Here `G_r(J_r)` counts the complete 2-gaps present immediately before filter
`r`, after all earlier filters in the chain. Both endpoints of every counted
gap lie in `J_r`.

## Why The Candidate Is Sufficient

The spacing inequality permits at most `k_r-1` shots inside `J_r`. After
filter `3`, distinct 2-gaps do not share endpoints, and one shot destroys at
most one of them. Therefore

```math
\begin{aligned}
G_{r^+}(J_r)
&\ge G_r(J_r)-(k_r-1)\\
&\ge k_r-(k_r-1)\\
&=1.
\end{aligned}
```

At least one 2-gap survives that layer. The survivor may change from one layer
to the next; no immortal individual gap is required. Because the hypothesis is
hereditary—each next inequality is evaluated on the population left by every
previous filter—the argument applies through the complete finite chain.

After the last missing prime below `q` is installed, a surviving complete
2-gap in `[q,q^2)` is square-safe and therefore certifies a twin-prime pair.
If the hereditary property holds for infinitely many future heads, it gives
infinitely many certificates.

## Gap-Agnostic Extension

For an arbitrary finite gap word `w`, let `G_r^w(J)` count complete occurrences
inside `J`. Define

```math
C_r(J)=\#\{\text{filter-}r\text{ shots in }J\},
```

and let `mu_w(J)` be the maximum number of counted occurrences containing any
one accepted value. One shot can then destroy at most `mu_w(J)` occurrences,
so

```math
K_r^w(J)\le\mu_w(J)C_r(J).
```

Any condition of the form

```math
G_r^w(J)>\mu_w(J)C_r(J)
```

forces one occurrence of `w` to survive. The spacing theorem can supply the
capacity bound `C_r(J)\le k-1`. Post-3 2-gaps form the special case
`mu_{(2)}(J)=1`.

## Relation To Other Candidates

- [Local surplus](local-surplus.md) compares a whole-window 2-gap count with a
  whole-window shot count.
- [Uniform local observable sampling](uniform-local-observable-sampling.md)
  controls pattern bias through deterministic sampling.
- [Local pattern-residue balance](local-pattern-residue-balance.md) controls
  the residue phases of finite gap words.
- [Forbidden-copy covered runs](forbidden-copy-covered-run.md) studies the
  combined forbidden copy-index classes of a repeated old gap.

Hereditary shot-spacing capacity instead uses the numerical order and partial
sums of the actual shot-gap word at every conditioned future layer.

## Established Inputs

- [Exact accepted local strikes](../properties/sieve-sequence/exact-accepted-local-filter-strikes.md)
- [Copy-index filter frequency](../properties/sieve-sequence/copy-index-filter-frequency.md)
- [2-gap endpoint isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

The rigid shot geometry does not itself prove the hereditary surplus. Equal
total spacing alone permits severe clustering; the useful information lies in
the consecutive partial sums. Earlier filters may also leave a population
whose 2-gap clusters align unusually well with the next scaled shot train.
The open obligation is to prove that such alignment cannot exhaust every
capacity-surplus interval through an arbitrarily long future filter chain.

## Empirical proxy status (window scale, measured)

The candidate stress-test (`candidates/analysis/measure_candidates.py`, 186
transitions: dense p<=991 + sparse every-100th-prime to p~19000, full window
`[q,q^2)`) measures only a coarse whole-window proxy: the actual number of
2-gaps destroyed by filter `p` versus the worst-case count `A(p,q)`, expressed
as `waste_ratio = (A(p,q) - destroyed) / A(p,q)`.

At six transitions the real filter hits its full whole-window worst-case
count, so `waste_ratio = 0`:

| (p,q) | destroyed | A(p,q) | waste_ratio | twin-prime transition? |
|-------|-----------|--------|-------------|------------------------|
| (5,7) | 2 | 2 | 0.000 | no |
| (19,23) | 2 | 2 | 0.000 | no |
| (239,241) | 2 | 2 | 0.000 | yes |
| (313,317) | 2 | 2 | 0.000 | yes |
| (569,571) | 2 | 2 | 0.000 | yes |
| (11681,11689) | 2 | 2 | 0.000 | no |

Notable pattern: three of these six transitions are twin-prime transitions
(`q - p = 2`). At such a transition the window begins with a 2-gap whose
endpoints straddle the new head's residue, which may force the filter to operate
near worst-case. This is a hypothesis from 3 data points, not a conclusion. The
new case at p=11681 shows that whole-window equality remains possible in the
measured large-p sample.

### Across the full measured range (p to ~19000)

The proxy satisfies `waste_ratio > 0` in **180/186** transitions.
Excluding the six worst-case failures, the distribution of `waste_ratio` is
min 0.2, median 1.0, max 1.0 (i.e. the filter frequently destroys *nothing*).
Trend (log-log, n=180): exponent k = +0.031, r = +0.127 — **no detectable
trend**; the favorable overall behavior and the sporadic worst-case hits neither
improve nor worsen systematically with p.

### Correction: this is not a counterexample to the candidate

`waste_ratio=0` says that every counted accepted shot in the whole window
destroyed a 2-gap. The candidate does **not** require a globally wasted shot.
It requires an interval with more relevant 2-gap capacity than the number of
shots admitted by the actual consecutive partial sums `sigma_r(k)`. Such an
interval may exist even when all shots hit somewhere, and `G_local>A(p,q)` can
leave survivors even at whole-window equality. Therefore the six transitions
do not falsify the per-layer interval premise, much less its hereditary
composition. The earlier “counterexample,” “building-block failure,” and
180/186 pass/fail labels are withdrawn; they describe only the proxy.

## Strategic assessment after empirical review

This candidate most directly captures the user's two rigid restrictions:
filters have a fixed shot count and an arithmetically constrained distribution
of shot spacings. It is also the candidate most explicitly concerned with the
relationship between a current population and all future filters. Its proof
priority is high, but its actual condition has not yet been measured.

The next implementation must construct the accepted shot sequence, its
consecutive partial sums `sigma_r(k)`, and search for the interval required by
the candidate at each layer. It should then fix one future square window,
condition the 2-gap population through every intervening filter, and repeat the
capacity test. Only that lineage experiment can reveal whether successive
filters systematically cherry-pick the remaining local clusters.
