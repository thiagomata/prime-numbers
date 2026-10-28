# Cluster Exposure Frontiers for Local 2-Gap Extinction

**Author:** Thiago Henrique Ramos da Mata  
Independent Researcher  
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**License:** [CC BY 4.0](../../LICENSE)

**Status:** Draft article. This note is an empirical and companion-process
draft, not a published chapter article.

**Proof status:** The local two-shot geometry cited here is backed by the
verified Sieve Sequence source and the fixed-shot-distance property note. The
cluster-exposure definitions are mathematical definitions. The plotted curves
are finite empirical measurements over generated prefixes and fixed-seed
random companion simulations. No asymptotic theorem is claimed for the real
sieve.

## Abstract

<div align="justify">
<p style="text-align: justify">

This article studies a local companion problem adjacent to the balanced
2-gap survival-frontier model. The tree-level companion follows one parent
2-gap through an incoming prime filter and preserves the exact fact that two
copy classes are harmful. That gives the random marginal benchmark $2/p$.
It does not, by itself, describe the local population problem in which many
nearby candidate 2-gaps occupy the same region and endpoint deletions alter
the surrounding gap structure.

The object here is a finite local cluster: a fixed number of consecutive
candidate 2-gaps in a generated stage prefix. For each cluster, the article
defines direct endpoint exposure, effective post-filter survival inside the
same value span, and a random companion baseline with the same cluster sizes
and stage heads. It then scales the companion hit probability by an aggression
factor and records the induced extinction frontier.

In the first measured run, using the first 20 generated stages, 10,000 gaps
per stage, clusters of 25 consecutive 2-gap candidates, and stride 1, the
measured prefix exposure has average 5.78254 hits per cluster and direct
survival average 0.768698. The corresponding fixed-seed random baseline has
average exposure 5.74491. When the baseline filter is made increasingly
aggressive, half of the clusters are extinct near aggression 8.79487; at
aggression 20, average survival is 0.0784061 and the extinction rate is
0.728578. These numbers are finite prefix measurements and companion
simulations, not the real sieve law. Their role is to calibrate how severe
local concentration must be in the companion model before nearby 2-gap
clusters disappear.

</p>
</div>

## 1. Introduction

The Sieve Sequence removes multiples of one prime at a time. At a stage headed
by $p$, the accepted values are the integers not divisible by any smaller
prime. Consecutive accepted values with difference $2$ form a 2-gap. A complete
old period copied through the incoming filter $p$ has a rigid local rule: each
old 2-gap has exactly two harmful lift offsets, one for each endpoint, and
those offsets are not chosen freely.

That tree-level fact explains why every parent contributes $p-2$ surviving
copies and why the random benchmark for one copied 2-gap is the marginal rate
$2/p$. It is also deliberately local to one lineage. A finite interval may
contain many candidate 2-gaps. When one endpoint is removed, the adjacent gaps
merge. The deletion is therefore not only a Bernoulli event attached to one
named descendant; it changes the local accepted-value structure in which
neighboring candidates are measured.

The question in this article is not whether one copied 2-gap survives
independently. The question is what amount of local exposure is needed to
extinguish a finite population:

```text
How aggressive must the local filter be before no 2-gap remains in a cluster?
```

This is a different scale from the survival-frontiers companion. The earlier
model follows lineages; the present model evaluates local populations.

The article develops four objects:

1. local clusters of consecutive candidate 2-gaps;
2. measured endpoint exposure and effective post-filter survival;
3. a random companion baseline with the same cluster sizes and heads; and
4. an aggression sweep that turns survival rate into an extinction frontier.

The scope is intentionally limited. No theorem below identifies the real
asymptotic distribution of cluster exposures. The article defines a
measurement, a baseline companion, and an extinction-frontier experiment, then
records the result of the first generated-prefix run.

## 2. Preliminaries And Evidence Boundary

Let $S_p$ be the accepted-value stream at the stage headed by prime $p$. A
candidate 2-gap is an adjacent pair

```math
(x,x+2)
```

inside $S_p$. Installing the filter $p$ removes accepted values divisible by
$p$. A candidate 2-gap is directly destroyed by this filter when at least one
endpoint is removed:

```math
p\mid x
\quad\text{or}\quad
p\mid x+2.
```

The complete-period copy law says that, for one old 2-gap copied through an
incoming odd prime $p$, exactly two lift offsets are harmful. The fixed-distance
property sharpens this: the two endpoint shots are a rigid translated pair,
not an arbitrary two-element subset. If the old period step is $M$ and
$\Delta$ is the canonical residue satisfying

```math
\Delta M \equiv 2 \pmod p,
```

then the endpoint offsets differ by $\Delta$ modulo $p$.

This fixed-distance input is documented in
[`fixed-shot-distance.md`](../../../properties/sieve-sequence/fixed-shot-distance.md)
and verified in
[`SpecSieveSeqTwoGapProperties::assertRightForbiddenLiftOffsetHasFixedSeparation`](../../../src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala).

This article uses that verified geometry as background. The new cluster
definitions below are not Stainless-verified properties. They are empirical
measurement definitions implemented in Python and applied to generated prefix
data.

The following evidence convention is used throughout:

1. **Verified local input.** The two endpoint offsets have a fixed separation
   in the maintained Scala source.
2. **Mathematical definitions.** Cluster exposure, effective survival,
   adversariality, and extinction rate are definitions in this article.
3. **Finite empirical run.** The numerical values come from generated prefix
   data in `first_gaps_per_seq.csv`.
4. **Companion simulation.** The aggression frontier comes from a fixed-seed
   random companion, not from the deterministic sieve itself.

No theorem in this article claims infinitely many twin primes.

## 3. Local Cluster Exposure

A tree-level model follows a single 2-gap as it is copied through an incoming
filter. It is natural there to ask for one descendant's survival probability.
If a parent produces $p$ copied children and two endpoint classes are harmful,
the mean hit probability for a distinguished copied child is

```math
\frac{2}{p}.
```

The cluster model keeps the same marginal scale but changes the population.
Instead of one parent, it takes a local group of candidate 2-gaps and asks how
many of them are directly exposed by the filter.

Let $W$ be a cluster containing $N$ consecutive candidate 2-gaps before
installing filter $p$. The cluster records the adjacent endpoint pairs, not
all accepted values in the interval:

```math
\begin{aligned}
W
&=
\{(x_1,x_1+2),\ldots,(x_N,x_N+2)\}
&&\text{[Cluster Definition]}.
\end{aligned}
```

The direct endpoint exposure counts exactly those candidate pairs for which
the incoming filter removes at least one endpoint:

```math
\begin{aligned}
H_p(W)
&=
\#\{i: p\mid x_i \ \text{or}\ p\mid x_i+2\}
\quad\blacksquare
&&\text{[Endpoint-Hit Count]}.
\end{aligned}
```

This exposure count is the first local statistic. It does not assume
independence between candidates. It records how many candidate 2-gaps in the
cluster are directly hit by the next filter.

The random benchmark keeps the same first-order mean. If each candidate in a
cluster is independently hit with probability $2/p$, the expected number of
hits is obtained by summing the indicator expectations across the cluster:

```math
\begin{aligned}
\mathbb E[H_p^{rand}(W)]
&=
\mathbb E\left[\sum_{i=1}^{N}
\mathbf 1[\text{candidate }i\text{ is hit}]\right]
&&\text{[By Definition of }H_p^{rand}\text{]}\\
&=
\sum_{i=1}^{N}
\mathbb E\left[\mathbf 1[\text{candidate }i\text{ is hit}]\right]
&&\text{[By Linearity of Expectation]}\\
&=
\sum_{i=1}^{N}\frac{2}{p}
&&\text{[Random Companion Hit Rate]}\\
&=
\frac{2N}{p}
\quad\blacksquare
&&\text{[Q.E.D.]}
\end{aligned}
```

Thus the random benchmark preserves the exact marginal two-shot scale while
making no claim about the deterministic placement of those shots.

The empirical adversariality score normalizes observed exposure by this mean:

```math
A_p(W)
=
\frac{H_p(W)}{2N/p}.
```

This turns raw hit counts into a scale-free comparison between clusters whose
incoming primes differ.

For the measured run below, the cluster size is fixed at $N=25$. Thus every
cluster row is computed by the same direct procedure. First, count the
endpoint hits; second, compute the random mean for that same head; third,
divide the two:

```math
\begin{aligned}
H_p(W)
&=
\sum_{i=1}^{25}
\mathbf 1[p\mid x_i \ \text{or}\ p\mid x_i+2]
&&\text{[Endpoint Exposure]}\\
\mathbb E[H_p^{rand}(W)]
&=
\frac{2\cdot25}{p}
&&\text{[Substitute }N=25\text{]}\\
&=
\frac{50}{p}
&&\text{[Simplification]}\\
A_p(W)
&=
\frac{H_p(W)}{50/p}
&&\text{[By Definition of }A_p\text{]}\\
&=
\frac{p\,H_p(W)}{50}
\quad\blacksquare
&&\text{[Q.E.D.]}
\end{aligned}
```

The row-level calculation therefore uses the active prime $p$ rather than a
single global denominator for every stage.

For example, at head $p=73$, a cluster of 25 candidates with three endpoint
hits has random mean $50/73$. Its adversariality score is:

```math
\begin{aligned}
A_{73}(W)
&=
\frac{H_{73}(W)}{50/73}
&&\text{[By Definition]}\\
&=
\frac{3}{50/73}
&&\text{[Substitute }H_{73}(W)=3\text{]}\\
&=
\frac{3\cdot73}{50}
&&\text{[Divide by a Fraction]}\\
&=
\frac{219}{50}
&&\text{[Multiplication]}\\
&=
4.38
\quad\blacksquare
&&\text{[Q.E.D.]}
\end{aligned}
```

This is the maximum per-stage score observed in the head-73 summary row of the
first run; the largest score in the whole first run is 5.36, recorded at head
67. The calculation is deliberately simple: count endpoint hits, divide by the
random mean for that same head and cluster size, and only then compare
clusters across stages.

Values near $1$ place the exposure at the random mean scale. Values larger
than $1$ mark above-mean local concentration. The score is not a theorem about
deterministic adversarial behavior; it is a normalized finite statistic that
allows clusters with different heads $p$ to be compared on one scale.

## 4. Effective Post-Filter Survival

Direct exposure counts original candidate 2-gaps whose endpoints are removed.
But endpoint removal also merges adjacent gaps. A cluster measurement should
therefore record not only direct hits but also the surviving 2-gap population
after the filter acts on the same value span.

For a cluster $W$, let

```math
\begin{aligned}
I(W)&=[x_1,x_N+2]
&&\text{[Original Cluster Span]}\\
S_p'(W)&=\{y\in S_p\cap I(W): p\nmid y\}
&&\text{[Apply Incoming Filter]}
\end{aligned}
```

The first line fixes the finite interval in which the local population is
recounted. The second line removes the values hit by the incoming filter,
without extending the count outside the original span.

The effective survivor count is

```math
\begin{aligned}
E_p(W)
&=
\#\{(y,z): y,z \text{ are adjacent in } S_p'(W),\ z-y=2\}.
&&\text{[Post-Filter 2-Gap Count]}
\end{aligned}
```

Thus $E_p(W)$ recounts 2-gaps after the local deletion and merge effect has
already occurred inside the measured interval.

The direct survival rate and effective survival rate are then

```math
\begin{aligned}
R_p^{direct}(W)
&=
\frac{N-H_p(W)}{N}
&&\text{[Original Candidates Not Directly Hit]}\\
R_p^{effective}(W)
&=
\frac{E_p(W)}{N}
\quad\blacksquare
&&\text{[Post-Filter Count Over Original Cluster Size]}
\end{aligned}
```

The two rates need not be identical by definition: one follows the original
candidate labels, while the other recounts the local post-filter gap structure.

The first rate measures how many original candidate 2-gaps avoid endpoint
deletion. The second recounts 2-gaps after the local filter has been applied
inside the same span. In the first measured run below, every measured cluster
had effective survivor count equal to the direct survivor count, so the
row-level and aggregate direct/effective statistics coincide. This is an
empirical observation about the selected prefixes and spans, not a general
identity. It says that this run did not observe merge effects creating
replacement 2-gaps inside the measured cluster spans.

The computation of these rates is row-by-row. If a size-25 cluster has
$H_p(W)=h$ endpoint hits, then the direct survivor count is $25-h$, and the
direct rate is obtained as follows:

```math
\begin{aligned}
R_p^{direct}(W)
&=
\frac{25-h}{25}
&&\text{[Substitute }N=25\text{]}.
\end{aligned}
```

The smallest measured direct survival rate in the first run is $0.32$. That
comes from the largest measured exposure, $h=17$:

```math
\begin{aligned}
R_p^{direct}(W)
&=
\frac{25-17}{25}
&&\text{[Substitute }h=17\text{]}\\
&=
\frac{8}{25}
&&\text{[Subtraction]}\\
&=
0.32
\quad\blacksquare
&&\text{[Q.E.D.]}
\end{aligned}
```

This is why the minimum survival in the table is $0.32$ rather than an
independent fitted statistic.

The largest measured direct survival rate is $1.00$, which occurs when
$h=0$. The effective rate is computed after deleting multiples of $p$ inside
the same value span and recounting adjacent post-filter 2-gaps. In this run,
the effective survivor count matched the direct survivor count in every
measured row, so the row-level and aggregate direct and effective statistics
are equal.

## 5. Empirical Exposure Distribution

The useful object is not only the mean of $H_p(W)$. The local extinction
question is controlled by the upper tail. For integer threshold $t$, define
the cluster exposure distribution by

```math
F(t)
=
\Pr[H_p(W)\le t],
```

where the probability is empirical over the chosen collection of clusters.

The generated plot overlays three populations:

- faint per-stage prefix CDF lines;
- a thick measured-prefix aggregate CDF; and
- a dashed fixed-seed random companion baseline.

![Cluster exposure distribution lines](/Users/thiagomata/github/thiagomata/prime-numbers/data/candidates/cluster-exposure-curve.svg)

The labels are intentionally conservative. The solid aggregate is a
measured-prefix curve, not the real asymptotic law. It uses finite generated
data and a chosen cluster construction. The dashed curve is a random baseline
using the same cluster sizes and stage heads.

For the first run:

```text
stages       = 20
prefix_len   = 10000
cluster_size = 25
stride       = 1
clusters     = 54056
seed         = 1
```

The aggregate curve is calculated from the cluster rows. If $C_h$ is the
number of measured clusters with exposure $h$, and $T$ is the total number of
clusters, the empirical mass and cumulative distribution are obtained by
counting rows:

```math
\begin{aligned}
T
&=
\sum_h C_h
&&\text{[Total Cluster Count]}\\
&=
54056
&&\text{[Measured Run]}\\
\Pr[H=h]
&=
\frac{C_h}{T}
&&\text{[Empirical Probability]}\\
F(h)
&=
\frac{\sum_{u\le h}C_u}{T}
\quad\blacksquare
&&\text{[Empirical CDF]}
\end{aligned}
```

Thus each plotted CDF point is only a cumulative count divided by the same
total number of measured clusters.

For example, the first two rows of the measured curve are
$C_0=5916$ and $C_1=9812$. The first two probabilities and cumulative values
are:

```math
\begin{aligned}
\Pr[H=0]
&=
\frac{5916}{54056}
&&\text{[Substitute }C_0,T\text{]}\\
&=
0.1094420601
&&\text{[Division]}\\
F(0)
&=
0.1094420601
&&\text{[Only Exposure }0\text{ Included]}\\
\Pr[H=1]
&=
\frac{9812}{54056}
&&\text{[Substitute }C_1,T\text{]}\\
&=
0.1815154654
&&\text{[Division]}\\
F(1)
&=
\frac{5916+9812}{54056}
&&\text{[Cumulative Count]}\\
&=
0.2909575255
\quad\blacksquare
&&\text{[Q.E.D.]}
\end{aligned}
```

This explains the first visible rise of the measured-prefix curve: about
$10.94\%$ of clusters have no direct exposure, and about $29.10\%$ have
exposure at most one.

The aggregate curve is a mixture over stage heads, and its staircase shape
reflects that. The measured mass is exactly zero at exposures 9 and 11
through 15: no measured cluster in this run produced those counts. The
isolated spike at exposure 10 is contributed by the head-5 stage, in which
every measured cluster has exposure exactly 10. The block of mass at
exposures 16 and 17 is contributed by the head-3 stage. The stages with
larger heads contribute the smooth low-exposure rise. The aggregate curve
therefore mixes very different per-head exposure scales rather than sampling
one common law.

The average and population standard deviation are computed from the same
counts. The histogram is not only used for the CDF; it also determines the
summary table:

```math
\begin{aligned}
\bar H
&=
\frac{1}{T}\sum_h hC_h
&&\text{[Weighted Mean]}\\
\sigma_H
&=
\sqrt{\frac{1}{T}\sum_h C_h(h-\bar H)^2}
\quad\blacksquare
&&\text{[Population Standard Deviation]}
\end{aligned}
```

Applying these formulas to all measured exposure counts gives the exposure
summary below.

The measured prefix exposure statistics are:

| Statistic | Value |
|---|---:|
| Minimum exposure | 0 |
| Maximum exposure | 17 |
| Average exposure | 5.78254 |
| Standard deviation | 5.89357 |

The measured direct and effective survival statistics are:

| Statistic | Direct survival | Effective survival |
|---|---:|---:|
| Minimum | 0.32 | 0.32 |
| Maximum | 1.00 | 1.00 |
| Average | 0.768698 | 0.768698 |
| Standard deviation | 0.235743 | 0.235743 |

The fixed-seed random baseline has exposure average 5.74491 and standard
deviation 6.11429. The averages are close in this run, as expected from a
baseline preserving the marginal $2/p$ scale. The remaining information is in
the shape of the distribution and in its extinction tail.

## 6. Extinction Frontier Under Aggression

To turn the exposure curve into an extinction frontier, keep the cluster list
fixed and make the companion filter more aggressive. For aggression factor
$\alpha\ge0$, the random companion hit probability is the ordinary rate
$2/p$ multiplied by $\alpha$, capped at one:

```math
\begin{aligned}
\pi_\alpha(p)
&=
\min\left(1,\alpha\frac{2}{p}\right)
\quad\blacksquare
&&\text{[Aggressive Companion Hit Rate]}.
\end{aligned}
```

For each cluster $W$ with $N$ candidates, the companion exposure is sampled
from the binomial law with that hit probability:

```math
\begin{aligned}
H_{p,\alpha}^{rand}(W)
&\sim
\operatorname{Binomial}(N,\pi_\alpha(p))
&&\text{[Independent Companion Hits]}.
\end{aligned}
```

The cluster's own stage head $p$ determines the hit probability. Once the
simulated exposure is known, the simulated survival rate is the unhit portion
of the cluster:

```math
\begin{aligned}
R_{\alpha}^{rand}(W)
&=
\frac{N-H_{p,\alpha}^{rand}(W)}{N}
\quad\blacksquare
&&\text{[Simulated Survival Rate]}.
\end{aligned}
```

A cluster is extinct when the simulated exposure reaches the full cluster
size. Since every candidate has been hit, the local companion population has
no remaining 2-gap candidates:

```math
\begin{aligned}
H_{p,\alpha}^{rand}(W)
&\ge
N
\quad\blacksquare
&&\text{[Extinction Condition]}.
\end{aligned}
```

The extinction rate is the fraction of clusters satisfying that condition.

For a fixed aggression value $\alpha$, the sweep repeats the same arithmetic
over all $T=54056$ clusters. If $e_j(\alpha)$ is the simulated exposure for
cluster $j$, and each cluster has size $25$, then each plotted point is
computed by averaging row-level survival and row-level extinction indicators:

```math
\begin{aligned}
\overline R_\alpha
&=
\frac{1}{T}
\sum_{j=1}^{T}
\frac{25-e_j(\alpha)}{25}
&&\text{[Average Simulated Survival]}\\
X_\alpha
&=
\frac{1}{T}
\sum_{j=1}^{T}
\mathbf 1[e_j(\alpha)\ge25]
\quad\blacksquare
&&\text{[Average Extinction Indicator]}
\end{aligned}
```

Here $\overline R_\alpha$ is the average simulated survival rate and
$X_\alpha$ is the extinction rate. Thus every point on the aggression plot is
one pass through the same cluster list with a different hit-probability scale.

![Aggression sweep for random companion extinction](/Users/thiagomata/github/thiagomata/prime-numbers/data/candidates/cluster-exposure-aggression.svg)

In the first run, aggression $1$ is the ordinary random baseline. The sweep
then increases $\alpha$ to $20$ in 40 evenly spaced steps. The first sampled
factor with extinction rate at least $1/2$ is:

```math
\alpha=8.79487.
```

At aggression $20$, the average simulated survival rate is

```math
0.0784061,
```

and the extinction rate is

```math
0.728578.
```

Those two numbers come directly from the final sweep row. That row first gives
the average exposure:

```math
\begin{aligned}
\overline H_{20}
&=
23.0398475655
&&\text{[Final Sweep Row]}.
\end{aligned}
```

Since every cluster has size $25$, the corresponding average survival is:

```math
\begin{aligned}
\overline R_{20}
&=
\frac{25-\overline H_{20}}{25}
&&\text{[Average Survival From Average Exposure]}\\
&=
\frac{25-23.0398475655}{25}
&&\text{[Substitution]}\\
&=
0.0784060974
\quad\blacksquare
&&\text{[Q.E.D.]}
\end{aligned}
```

This is the plotted survival value at the last aggression point.

The extinction rate $0.728578$ is an integer count over the fixed cluster
list. Multiplying the rate by the total recovers that count exactly:

```math
\begin{aligned}
54056\cdot0.7285777712
&=
39384
&&\text{[Convert Rate To Cluster Count]}
\end{aligned}
```

So exactly 39384 simulated clusters had all 25 candidates hit at aggression
$20$.

This separates marginal exposure from extinction. Matching the ordinary
$2/p$ rate leaves most clusters alive in this experiment. Making local
extinction common requires a much stronger companion filter. Even at twenty
times the baseline hit rate, the simulated run does not extinguish every
cluster.

## 7. Density And Neighbor Interference

The first effective-survival measurement suggests that merge side effects did
not change aggregate survival inside these prefix cluster spans. This should
not be read as a general absence theorem. Merge effects can only matter when
the local geometry gives them room to act.

A natural density statistic for a cluster is the average start spacing between
neighboring candidate 2-gaps. It compares the span from the first 2-gap start
to the last against the number of intervals between starts:

```math
\begin{aligned}
D(W)
&=
\frac{x_N-x_1}{N-1}
\quad(N>1)
\quad\blacksquare
&&\text{[Average Start Spacing]}.
\end{aligned}
```

The neighbor-interference regime is expected to become visible when this
spacing is small relative to the incoming filter:

```math
\begin{aligned}
D(W)
&<
p
\quad\blacksquare
&&\text{[Dense Relative To Filter]}.
\end{aligned}
```

In that regime, many candidate 2-gaps occupy a value window shorter than one
filter period per neighbor. Close endpoint shots and merge side effects have
more opportunity to overlap. In the sparse regime $D(W)\ge p$, candidates are
locally farther apart relative to the active modulus, so the tree-level
approximation should be harder to falsify by local merges alone.

This gives the next empirical refinement: stratify the exposure and extinction
curves by $D(W)/p$. The present article does not include that stratification,
but the definitions above make the missing measurement precise.

## 8. Reproducibility

The measurement is implemented in
[`sieve_sequence.cluster_exposure`](../../../python/src/sieve_sequence/cluster_exposure.py)
with a command-line entry point in
[`sieve_sequence.cluster_exposure_cli`](../../../python/src/sieve_sequence/cluster_exposure_cli.py).
It reads
[`first_gaps_per_seq.csv`](../../../data/sieve-sequence/first_gaps_per_seq.csv)
and writes:

- [`cluster-exposure-curve.csv`](../../../data/candidates/cluster-exposure-curve.csv);
- [`cluster-exposure-summary.csv`](../../../data/candidates/cluster-exposure-summary.csv);
- [`cluster-exposure-curve.svg`](../../../data/candidates/cluster-exposure-curve.svg);
- [`cluster-exposure-aggression.csv`](../../../data/candidates/cluster-exposure-aggression.csv); and
- [`cluster-exposure-aggression.svg`](../../../data/candidates/cluster-exposure-aggression.svg).

The run reported here used:

```bash
PYTHONPATH=python/src python/.venv/bin/python -m sieve_sequence.cluster_exposure_cli \
  --max-stages 20 \
  --prefix-len 10000 \
  --cluster-size 25 \
  --stride 1 \
  --seed 1 \
  --aggression-max 20 \
  --aggression-steps 40
```

The Python regression gate after adding the cluster-exposure code was:

```bash
python/.venv/bin/python -m pytest \
  python/tests/test_cluster_exposure.py \
  python/tests/test_window.py \
  python/tests/test_generate_gaps.py
```

with result:

```text
35 passed
```

## 9. Limitations

This article measures generated prefixes, not complete periods. It therefore
does not identify the asymptotic distribution of cluster exposures in the real
sieve.

The cluster list uses stride 1, so consecutive clusters share 24 of their 25
candidates. The 54056 measured clusters are heavily overlapping sliding
windows rather than independent samples, and the effective sample size behind
the empirical CDF is much smaller than the row count. The curve should be
read as a description of the measured prefixes, not as an estimate built from
54056 independent trials.

The random baseline treats candidate hits independently. That makes it useful
as a clean companion, but the real endpoint offsets are rigid and arithmetical.
The baseline should be read as a calibration scale, not as a claim that the
real filter chooses independent local hits.

The aggression sweep is also a companion experiment. It answers the question
"how strong would a random local filter need to be before extinction becomes
common under this cluster construction?" It does not prove that the real sieve
has or lacks such aggression.

The first effective-survival metric recounts 2-gaps only inside each cluster's
original value span. Boundary effects at the span edges and cyclic wrap effects
are not fully modeled here.

Finally, the article does not yet stratify clusters by local density. That is
the most important next measurement if the goal is to isolate where neighbor
interference can matter.

## 10. Conclusion

The tree-level survival companion remains useful because it preserves the
exact two-shot marginal rate. Local extinction, however, is a population-level
event. For extinction, the mean hit rate is not enough; the distribution tail
and the cluster density matter.

The first prefix experiment shows that the measured aggregate exposure and the
fixed-seed random baseline have similar mean scale, while the aggression sweep
needs roughly an order-of-magnitude stronger filter before half the clusters
are extinct. This suggests a practical way to discuss adversarial behavior:
not as a label, but as an extinction frontier measured against the random
$2/p$ baseline.

The next useful refinement is to split clusters by average spacing relative to
$p$. If neighbor interference is the missing local effect, it should become
visible first in dense clusters where nearby 2-gaps sit inside a window whose
average spacing is less than the active filter.
