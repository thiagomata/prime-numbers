# Hereditary Shot-Spacing Capacity

**Shot geometry:** Mathematically proved for one filter layer.

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Empirical status:** REINFORCED AT FINITE SCALE — exact `k=2` certificates
hold at 4/4 defined Q=17 layers, 23/23 defined Q=101 layers, and 1,837/1,837
defined layers across an expanded exact 53-head sweep through Q997. The
runner's selected `k\le10` witness fields are now exact under the proved
admissible-diameter profile. See [the empirical #14 note](
../empirical/sieve-sequence/hereditary-shot-spacing.md
).

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

## Empirical status (per-layer interval premise, lineage experiment)

The candidate's ACTUAL per-layer premise — exists `J_r\subseteq[q,q^2)` and
`k_r` with `G_r(J_r)\ge k_r` and `len(J_r) < \sigma_r(k_r)` — was measured for
the first time by the fixed-future-window lineage experiment
(`candidates/analysis/run_lineage.py`), which tracks one window's 2-gap
population through every intermediate filter layer by layer (Reading A).

**Q=101, 24 layers (primes 3,5,...,97):** the stored output reports the
per-layer interval premise at **23/23 defined layers** (layer 0 is undefined).
An independent nearest-pair check gives an enclosing length of `8` at all 23
layers. Because exact `sigma_r(2)=2r>=10`, every layer therefore has an exact
finite `k=2` certificate. The runner's chosen `k=10` fields at the later 16
layers are also exact under the proved `D(10)=32` profile. The separately
tracked population leaves **202 2-gaps after all 24 filters** in
`[101,10201)`.

**Expanded exact `k=2` sweep (53 heads, 1,837 defined layers):** a later
read-only in-memory sweep tested every prime head `17<=Q<=251`, together with
`307,401,503,701,997`. No layer failed. At every defined layer, the exact
closest-pair enclosure had length at most `8`, hence remained strictly below
the exact capacity `sigma_r(2)=2r`. The worst observed ratio was `8/(2*5)=0.8`.

This is qualitatively different from the window-pass proxy above: it tests the
candidate's real mechanism (interval vs shot partial sums), not a whole-window
averaged ratio, and it does so across a long hereditary chain rather than
single transitions.

### Finite small-`k` spacing evidence and the exact-profile boundary

The per-layer `\sigma_r(k)` is a whole-period quantity, so naive scaling hits a
primorial wall for full enumeration. What is now proved is stronger than the
earlier monotonicity-only boundary: sufficiently deep complete wheels satisfy
`s_P(k)=D(k)`, and the exact admissible-diameter profile
`D(2..10)=(2,6,8,12,16,20,26,30,32)` is established. Therefore every selected
lineage field with `k<=10` is exact without period materialization.

The supplied 100,000-gap prefixes still matter as location evidence, not as
proof. They repeatedly display the same small-span words, while for `k=10`
the visible prefix minimum changes from `32` to `34` at later stages. Since
`D(10)=32` is now proved, that change means only that a 32-span witness moved
outside the recorded prefix; it does not weaken the full-period theorem.

The finite witnesses, scope, and falsifiers are recorded in
[the empirical #14 note](
../empirical/sieve-sequence/hereditary-shot-spacing.md
).

### Honest scope

- Exact finite `k=2` certificates now cover Q17, Q101, and an expanded sweep
  of 53 heads / 1,837 defined layers. This still does not prove that the
  premise holds for all `Q`.
- The hereditary COMPOSITION (the candidate's full content) is tested only in
  the sense that the chain ran layer-by-layer with Reading-A conditioning; a
  finite family of chains succeeding does not prove the composition holds
  universally.

## Strategic assessment after empirical review

This candidate most directly captures the user's two rigid restrictions:
filters have a fixed shot count and an arithmetically constrained distribution
of shot spacings. It is also the candidate most explicitly concerned with the
relationship between a current population and all future filters. Its proof
priority is high.

The per-layer interval premise (`exists J_r, k_r with G_r(J_r) >= k_r` and
`len(J_r) < sigma_r(k_r)`) holds exactly in the finite Q17 and Q101 checks and
through the expanded 53-head / 1,837-layer sweep via `k=2`. The runner's later
preference for `k=10` is also exact because `sigma_r(10)=32r` at those stages.

What remains unproved is the **hereditary composition** — that the interval
premise holds for some layer in *every* sufficiently long chain, and across
unboundedly many layers / windows. The 53-head sweep materially strengthens
the finite case, but it still does not establish that universal statement. The
natural next steps are: (a) seek a copy-index or conditioned-density theorem
that forces the needed close pair in a future square window; and (b) seek a
uniform conditioned-window population bound.

### Partial proof result (per-layer `k=2` premise)

A proof attempt isolated a valid bounded-separation lemma, recorded as
[interval-premise-from-pair-existence](../properties/sieve-sequence/interval-premise-from-pair-existence.md):

> At a post-filter-3 layer `r`, if two complete 2-gaps have an enclosing
> interval of length less than `2r`, then the `k=2` interval premise holds.

The exact identity `sigma_r(2)=2r` discharges the shot-separation calculation
for this implication. It does not prove that an adequately close pair exists:
the post-filter-3 congruence gives a lower separation bound of `6`, whereas the
lemma needs an upper separation bound below `2r`. Both close-pair existence
and its hereditary persistence remain open.

A follow-up ordered-point theorem,
[local-count-forces-k2-shot-capacity](
../properties/sieve-sequence/local-count-forces-k2-shot-capacity.md
), supplies an explicit sufficient condition for that upper bound:

```math
G_r(W_Q)\ge
\left\lfloor
\frac{Q^2-Q-3}{2r-2}
\right\rfloor+2
```

forces two consecutive complete 2-gaps whose enclosure is shorter than `2r`,
and hence forces the `k=2` premise. This replaces qualitative close-pair
existence by a sharp finite count threshold, but it does not prove that the
conditioned local count meets that threshold in every required layer.

### Bounded chain-population investigation

A follow-up investigation tested whether the copy-index frequency alone gives
a recurrence that carries the 2-gap population through the full chain. Let
`N=G_r(W_Q)`, let `D` be the number of starts destroyed by filter `r`, and let
`N'=N-D`. The naive complete-block proportion would suggest

```math
N'\ge
\left\lceil N\left(1-\frac2r\right)\right\rceil.
```

That inequality is false after conditioning on earlier filters. It fails in
8 of the 24 Q=101 layers, with a largest deficit of 5. Across selected future
heads through Q=997, the harmful-hit excess

```math
D-\frac{2N}{r}
```

continues to grow, reaching about `41.740`. Thus neither the exact
multiplicative recurrence nor a constant correction calibrated from one chain
is a viable proof target.

The finite data instead isolates a square-root discrepancy scale. Let
`N_a` count the starts in residue class `a modulo r`, and define the
candidate-#12 deviation

```math
E=
\max_{0\le a<r}
\left|N_a-\frac Nr\right|.
```

The two endpoint classes that destroy a 2-gap give the following conditional
derivation:

```math
\begin{aligned}
D
&\le
2\left(\frac Nr+E\right)
\quad\text{[By the two forbidden residue classes]},\\
N'
&=N-D
\quad\text{[By Definition]},\\
&\ge
N\left(1-\frac2r\right)-2E
\quad\text{[Substitution]},\\
&\ge
N\left(1-\frac2r\right)-\sqrt N
\quad\text{[If }2E\le\sqrt N\text{]}.
\end{aligned}
```

Over every layer of 16 selected heads from Q=17 through Q=997, the direct
harmful excess divided by `sqrt(N)` is at most about `0.360`, while the
conservative candidate-#12 quantity `2E/sqrt(N)` is at most about `0.834`.
Iterating the unit-square-root recurrence stays positive in these measured
chains. This is reinforcement of a quantitative target, not a proof.

The load-bearing premise `2E <= sqrt(N)` is unproved, and Stainless
verification is not claimed for it. Existing verified count lemmas concern
complete periods; they do not transfer residue balance to the conditioned
short window. A uniform proof through the entire chain would force a positive
fully filtered population in `[Q,Q^2)` and therefore remains
twin-prime-strength. The investigation sharpens #14's boundary: exact
`k=2` shot separation is available, but close-pair existence and hereditary
local residue balance remain unproved. Fixed-`k` stabilization is now proved,
but the exact numerical stable values for `k>2` still require sharp
admissible-diameter proofs.
