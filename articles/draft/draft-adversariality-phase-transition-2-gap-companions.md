# Survival Frontiers in Balanced 2-Gap Companion Processes

**Author:** Mata, T. H.<br>
Independent Researcher<br>
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)<br>
**GitHub:** [@thiagomata](https://github.com/thiagomata)

**Status:** Draft (2026-08-15). The companion-process identities are proved
exactly; the asymptotic theorems are conditional on the premises stated with
each result (see §1.1). Stainless verification is pending. No result is
claimed for the real sieve.

## Abstract

<div align="justify">
<p style="text-align: justify">

This article examines companion processes that reproduce the exact global
growth of 2-gaps but change where each filter removes them. Every parent
produces $r$ copies and exactly two are removed, as in the sieve sequence. The
companion may place those two removals randomly, protect a chosen target, or
direct them toward it.
This construction separates the number of surviving 2-gaps from their
location near the head.

A filter's local destruction fraction $f_r$ is compared with the random rate
$2/r$ through $w_r=rf_r/2$. The cumulative product proves that every fixed
finite value of $w_r$ preserves square-window 2-gaps and, with the stated
availability and mixing conditions, produces head 2-gaps infinitely often.
The first boundary occurs when $w_r=1+c\log r$: square windows survive for
$c < 1$, while head recurrence survives for $c < 1/2$. Under the same spatial
premises, exact-quota companions give the same frontiers when their normalized
quotas satisfy the CRT-rate cumulative sum and summable finite-population error
conditions derived below. Retaining one CRT strike count alone is insufficient.
None of the spatial, availability, or mixing premises used by these
conditional theorems is proved for the real sieve.
Therefore, proving that the real sieve remains below the head frontier,
together with persistent availability and the deterministic discrepancy bound
stated in §10, would establish the twin-prime conjecture.
</p>
</div>

## 1. Introduction

Begin with the positive integers and remove multiples of prime numbers one
prime at a time. At a stage headed by the prime $p$, the accepted values are
precisely the integers not divisible by any prime smaller than $p$. These
survivors repeat periodically. If $e_i$ and $e_{i+1}$ are consecutive
survivors, then $e_{i+1}-e_i$ is their gap; the gaps across one complete period
form a finite cycle.

This periodic accepted-value object is the **Sieve Sequence**, introduced and
formally verified in [Formal Verification of Sieve Sequence Stages and Their
Transitions](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md) [[1]](#ref1); its finite gap cycle is the
representation used throughout this article.

After multiples of $2$ have been removed, every survivor is odd. Every gap is
therefore even, and $2$ is the smallest possible gap. A **2-gap** is a pair of
consecutive survivors $x$ and $x+2$. At the stage headed by a prime $Q$, all
primes below $Q$ have been installed as filters. A surviving 2-gap whose
endpoints lie in the square-safe window $[Q,Q^2)$ is therefore a twin-prime
pair: any composite number below $Q^2$ has a prime divisor below $Q$ and would
already have been removed.

When the sieve later reaches the stage headed by $x$, the same pair appears as
the first gap after the head. Infinitely many such head 2-gaps would give
infinitely many twin-prime pairs. But survival can be asked at three different
spatial scales:

1. some 2-gap exists somewhere in the complete period at every layer;
2. a 2-gap occurs in each sufficiently large square-safe window; or
3. the first gap after the distinguished head equals $2$ infinitely often.

The first statement is global and purely combinatorial. The second is local
but benefits from a window whose length grows quadratically. The third concerns
one position and therefore has no window-size reserve. Mixing these meanings
hides the actual threshold.

The following two empirical views make the distinction visible in the
deterministic Sieve Sequence. They use the same 200 stages and the same
2-focused compression: every 2-gap receives its own green cell, while each
maximal run of consecutive non-2 gaps is collapsed into one colored cell equal
to its sum. An internal colored cell therefore measures the total distance
between two consecutive 2-gaps. Both views display $1{,}400$ compressed units
from every row; they differ only in where those rows are placed horizontally.

**View A — independent compressed snapshots.** Every row begins at column zero,
so its horizontal coordinate counts compressed units from that stage's own
head. This is the original view. It honestly shows the texture within each
stage, but its curved or noisy-looking vertical drift must not be read as a
2-gap changing before the square boundary: equal columns in adjacent rows need
not represent the same surviving values.

![Independent 2-focused snapshots of 200 Sieve Sequence stages: every row restarts at its own head](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/gap-heatmap-2focused.svg)

**View B — shared-safe-2 alignment.** For each pair of adjacent rows, let $h$ be
the previous stage's head. A safe anchor is a 2-gap with the same raw starting
value in both rows and with both endpoints strictly below $h^2$. The alignment
calculation compares the compressed indices of every such shared safe 2-gap
and shifts the later row by their common difference. Across the 199 observed
transitions, the 200-stage dataset exhibits 118 differences of zero and 81 of
one; every safe anchor within each transition agrees with that row's difference.
Accumulating those differences produces the alternative view below.

![Shared-safe-2 aligned compression of 200 Sieve Sequence stages: unchanged pre-square 2-gaps form vertical green lines](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/gap-heatmap-2focused-aligned.svg)

The left white wedge is intentional padding created by the cumulative offsets.
A zero shift occurs when advancing the head merely shortens the leading
collapsed non-2 run; a one-cell shift occurs when that step removes an entire
compressed run or a standalone 2-gap cell. Thus the straight green lines in
View B and the curved texture in View A describe the same data under different
coordinates.

The sieve does not rotate this compressed row as an atomic list. Within the
safe prefix, it advances the head through one raw gap; only afterward does the
visualization collapse the remaining consecutive non-2 gaps. Thus a raw prefix
$[4,6,8,2,\ldots]$ appears over successive rows as
$[18,2,\ldots] \to [14,2,\ldots] \to [8,2,\ldots] \to [2,\ldots]$. The long
blue feature is not one unchanged merged gap reused in several sequences; it is
the decreasing suffix of one raw run. Rotating one compressed cell per row
would show that block only once, but it would define a different dynamics from
the Sieve Sequence.

| View | Horizontal coordinate | What vertical comparison supports |
|---|---|---|
| Independent snapshots | Compressed units from each row's own head | Within-stage density and spacing texture; not cell-by-cell lineage |
| Shared-safe-2 aligned | Cumulative columns fixed by shared 2-gaps below the previous $h^2$ | Exact alignment of the observed safe prefix; not full lineage beyond it |

These figures provide empirical context for the placement problem; neither is
evidence for the companion-model survival thresholds derived below. They are
generated by the [gap-heatmap calculation](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/gap_heatmap.py) from a dataset containing the
[first 100,000 gaps of each stage](https://github.com/thiagomata/prime-numbers/blob/master/data/sieve-sequence/first_gaps_per_seq.csv).

The central question is therefore not what fixed percentage of behavior may be
called adversarial. It is how large the realized local destruction may be
relative to the random benchmark $2/r$, and how that damage is allocated near
the head.

The balanced companions are designed to separate them. They retain the real
sieve's exact number of descendants but replace the arithmetic rule selecting
which descendants die. This makes global survival identical in every companion
while allowing local behavior to range from maximally protective, through
position-blind random, to maximally hostile.

We establish:

- the exact allocation-independent global recurrence $N_{k+1}=(r_k-2)N_k$;
- the cumulative local-hazard law $P(Q)=e^{-D(Q)}$ and its fixed-factor and
  logarithmic survival frontiers;
- the distinct square-window and head thresholds for adversarial/random and adversarial/protective
  mixtures;
- sharp finite allocation bounds separating adversarial-label budget from positional
  information; and
- exact-quota and biased exact-quota companions that preserve CRT strike counts
  while randomizing their locations.

### 1.1 Scope and Evidence

We prove exact identities for the finite companion processes and conditional
theorems for their asymptotic local behavior. Whenever a result needs spatial
uniformity, head availability, or cross-layer mixing, we state that premise in
the property itself before using it. The comparison with the real sieve then
shows what additional arithmetic information would transfer the companion
result.

The companion theorems below are proved mathematically under their stated
premises; Stainless verification remains pending and is outside this article's
scope.

## 2. Preliminaries and Companion Models

Let $\mathcal G_k$ be the 2-gap descendants before installing prime $r$. Each
parent $g\in\mathcal G_k$ produces the indexed copies

```math
(g,0),(g,1),\ldots,(g,r-1).
```

Exactly two distinct indices are harmful. Each parent receives one of three
policies. A **random parent** draws the harmful pair uniformly from the
two-element subsets of $\mathbb Z/r\mathbb Z$. An **adversarial parent** places
a deletion on its target child whenever possible. A **protective parent**,
defined fully in §5.2, places both deletions away from the target whenever
possible.

Every policy leaves exactly $r-2$ children. The companions therefore change
the location of the deletions, not the population size.

For example, let $r=5$ and suppose child index $1$ is the target. A random
parent may remove any pair, such as $\{0,4\}$. An adversarial parent chooses a
pair containing $1$, such as $\{1,4\}$. A protective parent chooses both
indices outside the target, again allowing $\{0,4\}$. The three parents make
different local choices, but each leaves exactly three children. This simple
example is the distinction used throughout the article: global reproduction
is fixed, while local placement changes.

The random, adversarial, and protective companion definitions above are the
definitions used throughout this article. The corresponding real modular pair
is derived in [Gap Dynamics §6.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#61-one-new-prime-forbids-two-copy-classes) [[2]](#ref2).

### 2.1 Notation

We use the following notation throughout:

| Symbol | Meaning |
|---|---|
| $r$ | incoming filter prime |
| $Q$ | target prime head |
| $N_k$ | complete-period 2-gap population at layer $k$ |
| $f_r$ | fraction of a tracked local population destroyed at filter $r$ |
| $w_r=rf_r/2$ | destruction relative to the random benchmark $2/r$ |
| $D(Q)=\sum_{r < Q}-\log(1-f_r)$ | cumulative local hazard |
| $\alpha_r$ | scheduled absolute adversarial share in a mixture |
| $A(Q)=\sum_{r < Q}-\log(1-\alpha_r)$ | cumulative adversarial-share hazard |
| $J_r/N_r=u_r$ | exact-quota strike fraction |
| $\beta_r$ | raw endpoint preference in a biased quota |
| $\kappa_r$ | effective destruction skew, equal to $w_r$ when measured from $f_r$ |

All products and sums over $r < Q$ are over prime filters unless stated
otherwise. Square-window conclusions use a population of order $Q^2$; head
conclusions concern one distinguished position.

For the prime-indexed head events $H_Q$, define

```math
S(X):=
\sum_{\substack{Q\le X\\Q\text{ prime}}}\Pr(H_Q).
```

Throughout this article, **adequate cross-layer mixing** means that whenever
$S(X)\longrightarrow\infty$,

```math
\sum_{\substack{P,Q\le X\\P,Q\text{ prime}}}
\Pr(H_P\cap H_Q)
=
(1+o(1))S(X)^2.
```

Mutual independence is a sufficient special case: its diagonal correction is
$O(S(X))=o(S(X)^2)$. The Kochen--Stone form of the second Borel--Cantelli lemma
then gives $\Pr(H_Q\text{ infinitely often})=1$ [[3]](#ref3). When $S(X)$ converges, the
first Borel--Cantelli lemma gives only finitely many head events without any
mixing premise.

Square-window applications use one further named premise. **Blind placement**
means that the surviving starts are placed in the window so that the
empty-window bound

```math
\Pr(X_Q=0)\le e^{-\lambda_Q}
```

holds, where $\lambda_Q$ is the expected surviving population of that window
(for example $\lambda_Q^{\mathrm{mix}}$ in §4.1). This is an assumption about
the joint placement distribution: it holds for independent uniform placement
and is not derived in this article for dependent allocators such as exact
quotas, whole-filter coins, or block balance. Whenever a square-window result
uses it, the result says so; the same caveat as §9 applies — allocators with
different dependence structures cannot inherit one another's almost-sure
conclusions.

### 2.2 Mathematical Foundation

The companion construction uses three exact sieve-sequence results proved in
[Gap Dynamics](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md) [[2]](#ref2):

- the [exact complete-period 2-gap count](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#52-exact-non-recursive-global-count);
- the [two harmful copy-index classes](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#61-one-new-prime-forbids-two-copy-classes); and
- the [exact accepted-strike count](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#91-exact-accepted-strikes).

The relative local-damage normalization is defined directly in §3.2, and its
allocation refinement is defined in §6.2.

## 3. Relative Hazard and Survival Frontiers

### 3.1 Global Persistence Is Independent of Allocation

We begin with the property shared by every balanced companion. No choice of the
harmful pair changes the number of surviving descendants: random,
adversarial, protective, and mixed parents all leave the same global
population. Local extinction must therefore come from placement rather than
from exhausting the complete-period supply.

Let $N_k=|\mathcal G_k|$ and assume $N_0>0$. Installing $r_k$ gives

```math
\begin{aligned}
N_{k+1}
&=\sum_{g\in\mathcal G_k}(r_k-2)
&&[\text{Exactly Two Copies Removed Per Parent}]\\
&=(r_k-2)N_k.
&&[\text{Simplification}]
\end{aligned}
```

Consequently,

```math
\begin{aligned}
N_k
&=N_0\prod_{i < k}(r_i-2)
&&[\text{Iteration}]\\
& > 0
&&[N_0>0;\ r_i\ge5]\\
&\longrightarrow\infty.
&&[\text{Every Factor Is At Least }3]
\end{aligned}
```

Thus

```math
\text{global 2-gap persistence holds for every adversarial schedule.}
\qquad[\text{Q.E.D.}]
```

The complete proof record appears in [Appendix A.1](#appendix-a1). The
corresponding real-sieve count is proved in [Gap Dynamics §5.2](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#52-exact-non-recursive-global-count) [[2]](#ref2).

### 3.2 Local Destruction Relative to Random

The primary quantity is the realized fraction of the target segment's 2-gaps
destroyed by filter $r$. If $L_r > 0$ gaps are present before the filter and
$H_r$ are destroyed, define

```math
f_r:=\frac{H_r}{L_r}.
```

Balanced random selection has benchmark destruction rate

```math
d_r:=\frac2r.
```

The dimensionless worse-than-random factor is

```math
w_r
:=\frac{f_r}{d_r}
=\frac{rf_r}{2}.
```

This is the meaningful adversariality scale because the benchmark itself
shrinks as filters grow:

```math
\begin{aligned}
w_r=0
&\Longleftrightarrow f_r=0
&&[\text{Protective Endpoint}],\\
w_r=1
&\Longleftrightarrow f_r=2/r
&&[\text{Random Benchmark}],\\
w_r=r/2
&\Longleftrightarrow f_r=1
&&[\text{Complete Local Destruction}].
\end{aligned}
```

The range $0\le w_r\le r/2$ compares realized damage, not intent. A random
filter may fluctuate above one, and a nominal adversary with poor positional
information may fall below one. Allocation determines $H_r$; $w_r$ records the
result after allocation.

#### Absolute Adversarial/Random Share as a Specialization

Fix a target: either a square-safe window or one distinguished head position.
At filter $r$, let

```math
0\le \alpha_r\le 1
```

be the adversarial share. The remaining share $1-\alpha_r$ uses the balanced
random choice.

This can be interpreted parent by parent or as a marginal mixture for one
locally relevant lineage. For the cumulative product studied below, mixture
choices for a tracked lineage are independent from one filter to the next.
The one-lineage calculation at each filter is then the same:

- under adversarial selection, its target child is destroyed;
- under balanced random selection, that child survives with probability
  $1-2/r$.

The model therefore assumes that the adversarial branch is strong enough to
identify and kill the locally relevant child. That is exactly what makes it an
adversarial comparison rather than a description of the real filter.

Its total local destruction rate and relative factor are

```math
\begin{aligned}
f_r
&=\alpha_r+(1-\alpha_r)\frac2r,\\
w_r
&=\frac r2f_r\\
&=1+\frac{r-2}{2}\alpha_r.
\end{aligned}
```

Thus a fixed absolute share $\alpha_r=\alpha > 0$ does not represent a fixed
amount worse than random. It makes $w_r$ grow linearly like $\alpha r/2$.
This is why the fixed-share model is asymptotically fatal for an essentially
trivial reason; the nontrivial question is how rapidly $w_r$ itself may grow.

### 3.3 The General Cumulative Local-Hazard Law

We now follow one local population through successive filters. Its survival is
determined by the total realized destruction
fraction $f_r$, regardless of whether that fraction arose from random choice,
adversarial labels, targeting, or another allocation mechanism. Multiplying
the one-step survival factors gives an exact cumulative law. The later window
and head applications add their own abundance and mixing premises.

```math
s_r=1-f_r=1-\frac{2w_r}{r}.
```

Assume $f_r < 1$ for every filter in the tracked chain. Define the cumulative
local hazard

```math
D(Q)
:=\sum_{r < Q}-\log(1-f_r)
=\sum_{r < Q}-\log\left(1-\frac{2w_r}{r}\right).
```

The complete survival factor is exactly

```math
\begin{aligned}
P(Q)
&=\prod_{r < Q}(1-f_r)
&&[\text{Survive Every Filter}]\\
&=\exp\left(\sum_{r < Q}\log(1-f_r)\right)
&&[\text{Product To Sum}]\\
&=e^{-D(Q)}.
&&[\text{Definition Of }D(Q)]
\end{aligned}
\qquad[\text{Q.E.D.}]
```

The Prime Number Theorem, the prime harmonic estimate, and their
partial-summation consequences used here and below are classical; we use Hardy
and Wright [[4]](#ref4).

For the random benchmark $w_r=1$,

```math
\begin{aligned}
D_{\mathrm{random}}(Q)
&=\sum_{r < Q}-\log\left(1-\frac2r\right)\\
&=2\log\log Q+O(1),
\end{aligned}
```

and therefore

```math
P_{\mathrm{random}}(Q)
\asymp\frac{C}{(\log Q)^2}.
```

The absolute adversarial/random mixture from §3.2 is recovered because

```math
1-f_r
=(1-\alpha_r)\left(1-\frac2r\right).
```

If

```math
A(Q):=\sum_{r < Q}-\log(1-\alpha_r),
```

then

```math
\begin{aligned}
D_{\mathrm{adversarial/random}}(Q)
&=D_{\mathrm{random}}(Q)+A(Q),\\
P_{\mathrm{adversarial/random}}(Q)
&\asymp\frac{C}{(\log Q)^2}e^{-A(Q)}.
\end{aligned}
```

Thus the earlier $A(Q)$ is an excess hazard created by one particular policy
mixture. The primary quantity is $D(Q)$, which also applies when no policy label
$\alpha_r$ exists.

If one filter has $f_r=1$, local extinction is immediate and the cumulative
hazard is infinite from that point.

The complete proof record appears in [Appendix A.2](#appendix-a2).

### 3.4 Every Fixed Finite Worsening Factor Survives

The random destruction rate shrinks like $2/r$. We first ask what happens when
the local filter is a fixed number of times worse than that benchmark. With a
quadratic supply of eligible starts and blind placement, every fixed factor
still leaves occupied square windows. If head candidates remain available and
successive layers mix adequately, the head also returns to a 2-gap infinitely
often.

Let $w\ge 0$ be fixed and suppose

```math
f_r=\frac{2w}{r}
```

for all sufficiently large filters. A finite prefix is absorbed into a positive
constant. Since the quadratic error terms are summable over primes,

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

For a square window with $B(Q)\asymp C_0Q^2$ eligible lineages,

```math
\lambda_w(Q)
\asymp
C_0\frac{Q^2}{(\log Q)^{2w}}
\longrightarrow\infty
```

for every finite $w$. The growth is strong enough to make the standard
empty-window bound summable, so only finitely many square windows are empty
almost surely under the blind-placement premise.

For a distinguished head with baseline availability bounded below,

```math
\Pr(H_Q)\asymp\frac{C_w}{(\log Q)^{2w}}.
```

The sum of this probability over prime heads diverges for every finite $w$.
Under adequate mixing, head 2-gaps therefore recur infinitely often almost
surely.

Thus

```math
\text{there is no finite constant-factor maximum worse than random.}
\qquad[\text{Q.E.D.}]
```

A filter that is twice, ten times, or one million times worse than the random
rate still lies in the same asymptotic survival class once $r$ is sufficiently
large. The nontrivial transition begins only when $w_r$ grows with $r$.

The complete proof record appears in [Appendix A.3](#appendix-a3).

The fixed-factor conclusion is not only asymptotic; it is visible in the
square-window occupancy itself. The figure below plots
$\log_{10}\lambda_w(Q)$ against $\log_{10}Q$ for the fixed factors
$w=1,3,6,10$, a constant $1\%$ adversarial share, and the $c=1$ frontier
$w_r=1+\log r$. Every fixed finite $w$ climbs without bound -- $w=6$ and
$w=10$ visibly dip first, because $Q^2$ must first outgrow $(\log Q)^{2w}$ --
while the constant share collapses rapidly and the exact $c=1$ boundary
declines only logarithmically: $\lambda_1(Q)\asymp C/(\log Q)^2\to0$. This is
the failure-side boundary derived in §3.5, not a surviving curve.

![Square-window expected occupancy log10(lambda(Q)) on a log scale: every fixed relative-hazard factor w=1,3,6,10 eventually climbs without bound, a constant 1% adversarial share collapses rapidly, and the exact c=1 boundary declines slowly to zero](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/phase-transition-window.svg)

### 3.5 Logarithmically Growing Worsening Has Two Thresholds

The first genuine transition appears when the worsening factor grows with the
filter. Using the same supply, availability, and mixing premises as §3.4, we
let the factor grow logarithmically and compare the reserve supplied by a
square window with the much thinner reserve at one distinguished head.

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

The random contribution supplies the first term, while the second is the
growing excess. Prime summation gives

```math
\begin{aligned}
D_c(Q)
&=\sum_{r < Q}-\log(1-f_r)
&&[\text{Definition Of }D(Q)]\\
&=2\sum_{r < Q}\frac1r
&\quad+2c\sum_{r < Q}\frac{\log r}{r}+O(1)
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
\qquad[\text{Exponentiation And Simplification}]
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

For the head,

```math
\Pr(H_Q)
\asymp
\frac{C_c}{Q^{2c}(\log Q)^2}.
```

Summing over prime heads has the same convergence behavior as

```math
\int^\infty
\frac{dx}{x^{2c}(\log x)^3}.
```

Thus

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

The threshold is the Borel-Cantelli decision rule for the head, and the figure
below evaluates it directly. It plots the cumulative sum of $\Pr(H_Q)$ over
real enumerated primes up to $Q$, for $w_r=1+c\log r$ at
$c=0.0,0.1,0.3,0.5,0.7,1.0$. Below the threshold the sum keeps climbing --
$c=0.0$ and $c=0.1$ clearly, $c=0.3$ more slowly but provably -- so there are
infinitely many head events with mixing. At and above the threshold the sum
flattens: $c=0.5$ only very slowly (it is the boundary itself), $c=0.7$ and
$c=1.0$ quickly -- so there are only finitely many, almost surely.

![Cumulative sum of Pr(head is a 2-gap) over enumerated primes, log scale: c=0.0 and c=0.1 climb the whole way, c=0.3 climbs slowly, c=0.5 flattens only very slowly at the boundary, and c=0.7 and c=1.0 flatten quickly -- the c=1/2 Borel-Cantelli threshold](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/phase-transition-head.svg)

Equivalently, the robust relative-factor regimes are

```math
\begin{aligned}
w_r& < (1-\varepsilon)\log r
&&[\text{Square-Window Survival}],\\
w_r& < \left(\frac12-\varepsilon\right)\log r
&&[\text{Head Recurrence}],
\end{aligned}
```

up to the asymptotically negligible additive random baseline. In terms of the
total segment destruction fraction,

```math
\begin{aligned}
f_r& < (2-\varepsilon)\frac{\log r}{r}
&&[\text{Square-Window Survival}],\\
f_r& < (1-\varepsilon)\frac{\log r}{r}
&&[\text{Head Recurrence}].
\end{aligned}
\qquad[\text{Q.E.D.}]
```

These are cumulative asymptotic regimes, not pointwise allowances that reset
at each filter. Irregular schedules must be evaluated through $D(Q)$.

The complete proof record appears in [Appendix A.4](#appendix-a4).

### 3.6 Relative-to-Random Phase Diagram

The answer is not a maximum fixed percentage. It is a growth-rate boundary for
the realized local damage relative to the random benchmark.

| Realized relative factor | Total local destruction | Square windows | Head 2-gaps |
|---|---:|---|---|
| $w_r=1$ | $2/r$ | Eventually nonempty almost surely | Infinitely often with mixing |
| Any fixed finite $w_r=w$ | $2w/r$ | Eventually nonempty almost surely | Infinitely often with mixing |
| $w_r=1+c\log r$, $0\le c < 1/2$ | $2/r+2c\log r/r$ | Eventually nonempty almost surely | Infinitely often with mixing |
| $w_r=1+c\log r$, $1/2\le c < 1$ | $2/r+2c\log r/r$ | Eventually nonempty almost surely | Only finitely often almost surely |
| $w_r=1+c\log r$, $c\ge1$ | $2/r+2c\log r/r$ | Expected population tends to zero | Only finitely often almost surely |
| $f_r=1$ at any tracked step | $1$ | Immediate local extinction | Immediate local extinction |

Consequently, there is **no largest finite constant multiple of random**. For
square-window survival, the filter may become almost $\log r$ times worse than
random; for infinitely recurring head 2-gaps, it may become almost
$\tfrac12\log r$ times worse. In total local-destruction terms, the robust
sufficient regimes are respectively

```math
f_r < (2-\varepsilon)\frac{\log r}{r}
\qquad\text{and}\qquad
f_r < (1-\varepsilon)\frac{\log r}{r}.
```

These conclusions concern damage realized inside the tracked segment. A small
global adversarial budget can still cause $f_r=1$ if it is allocated with enough target
information; the allocation theorem in §5 isolates that second
axis.

## 4. Absolute-Share Mixtures

### 4.1 Adversarial/Random Parent Square-Window Boundary

We now express the general hazard result through an explicit mixture. Each
parent is adversarial with share $\alpha_r$ and otherwise random. When the
surviving starts follow the spatial-uniformity model of the balanced random
companion, a square-safe window has length

```math
L_Q\asymp Q^2.
```

The expected mixed population is

```math
\begin{aligned}
\lambda_Q^{\mathrm{mix}}
&=L_Q\delta_Q^{\mathrm{mix}}
&&[\text{Expected Uniform Occupancy}]\\
&\asymp
C\frac{Q^2}{(\log Q)^2}e^{-A(Q)}.
&&[\text{Substitution}]
\end{aligned}
```

Taking logarithms exposes the threshold:

```math
\begin{aligned}
\log\lambda_Q^{\mathrm{mix}}
&=2\log Q-2\log\log Q-A(Q)+O(1).
&&[\text{Logarithm}]
\end{aligned}
```

Therefore, for every fixed $\varepsilon > 0$,

```math
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,
&&[\text{Subcritical Adversarial Budget}]\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow0.
&&[\text{Supercritical Adversarial Budget}]
\end{aligned}
```

The boundary $A(Q)=2\log Q+o(\log Q)$ requires its lower-order terms; the
$-2\log\log Q$ contribution cannot be discarded there.

Under uniform placement, an empty-window estimate has the usual form

```math
\Pr(X_Q=0)\le e^{-\lambda_Q^{\mathrm{mix}}}.
```

Whenever

```math
\sum_{Q\text{ prime}}e^{-\lambda_Q^{\mathrm{mix}}} < \infty,
```

the first Borel-Cantelli lemma gives only finitely many empty square windows
almost surely. A convenient sufficient condition is

```math
\lambda_Q^{\mathrm{mix}}\ge(1+\varepsilon)\log Q
\qquad[\text{Q.E.D.}]
```

for all sufficiently large $Q$. This is stronger than merely requiring
$\lambda_Q^{\mathrm{mix}}\to\infty$ and prevents a slow divergent expectation
from being mistaken for an eventual-survival theorem.

This proves eventual safe-window occupancy inside the spatially uniform mixed
companion. Section 8 states the separate conditions needed to transfer the
result to the real sieve.

The complete proof record appears in [Appendix A.5](#appendix-a5).

### 4.2 Why a Constant Absolute Adversarial Share Is Locally Fatal

A constant adversarial share sounds mild, but it adds the same positive loss
at every filter while the random benchmark keeps shrinking. We therefore
expect it to overwhelm local survival. Let one fixed share
$0 < \alpha < 1$ be adversarial at every filter. Then

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

Since $Q/\log Q$ grows faster than $\log Q$, this lies far above the
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

Thus

```math
\text{every fixed positive per-filter adversarial share is locally fatal}
\qquad[\text{Q.E.D.}]
```

in the repeated-mixture model, even though the complete-period
population continues to grow without bound.

This is different from applying one adversarial dilution after all random
filters have finished. A one-time dilution multiplies the final count by
$1-\alpha$ once; the repeated model multiplies it once per prime. Confusing
these two experiments reverses the asymptotic conclusion.

### 4.3 Two Decaying Absolute-Share Families

The useful question is therefore not “what fixed percentage is tolerable?”
The useful question is how quickly $\alpha_r$ must decay.

#### Reciprocal Decay: $\alpha_r\sim c/r$

For fixed $c > 0$ and sufficiently large primes,

```math
\begin{aligned}
A(Q)
&\sim c\sum_{r < Q}\frac1r
&&[-\log(1-x)\sim x]\\
&\sim c\log\log Q.
&&[\text{Prime Harmonic Sum}]
\end{aligned}
```

Therefore

```math
e^{-A(Q)}\asymp\frac1{(\log Q)^c}
```

and

```math
\lambda_Q^{\mathrm{mix}}
\asymp
C\frac{Q^2}{(\log Q)^{2+c}}\longrightarrow\infty.
```

The window population grows polynomially faster than its logarithmic losses,
so the empty-window probabilities are summable under the spatial model.

#### Logarithmic-Over-Linear Decay: $\alpha_r\sim c\log r/r$

For a finite initial prefix, define the shares separately so that they remain
in $[0,1]$; this changes only the final constant. On the asymptotic tail,

```math
\begin{aligned}
A(Q)
&\sim c\sum_{r < Q}\frac{\log r}{r}
&&[-\log(1-x)\sim x]\\
&\sim c\log Q.
&&[\text{Prime Number Theorem By Partial Summation}]
\end{aligned}
```

Consequently,

```math
\begin{aligned}
e^{-A(Q)}&\asymp Q^{-c},\\
\lambda_Q^{\mathrm{mix}}
&\asymp C\frac{Q^{2-c}}{(\log Q)^2}.
\end{aligned}
```

The square-window phase diagram is therefore

```math
\begin{aligned}
c < 2&\Longrightarrow\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,\\
c\ge 2&\Longrightarrow\lambda_Q^{\mathrm{mix}}\longrightarrow0.
\end{aligned}
```

For $c < 2$, the divergence is polynomial, so the empty-window bound is
summable and every sufficiently large square window is nonempty almost surely
under the spatial-uniformity premise.

### 4.4 Adversarial/Random Parent Head Boundary

The head contains only one distinguished position, so it receives no
quadratic window reserve. Under uniform head marginals, its occurrence
probability is the surviving local density itself. To turn a divergent sum of
these probabilities into almost-sure recurrence, we also require independence
or a sufficiently strong weak-mixing substitute.

```math
\Pr(H_Q)
\asymp
\delta_Q^{\mathrm{mix}}
\asymp
\frac{C}{(\log Q)^2}e^{-A(Q)}.
```

Under adequate cross-layer mixing, the second Borel-Cantelli lemma gives

```math
\sum_{Q\text{ prime}}\Pr(H_Q)=\infty
\Longrightarrow
H_Q\text{ occurs infinitely often almost surely}.
```

For $\alpha_r\sim c/r$,

```math
\Pr(H_Q)\asymp\frac{C}{(\log Q)^{2+c}},
```

and the sum over prime $Q$ diverges for every fixed $c$. Reciprocal decay is
therefore compatible with infinitely many head events under mixing.

For $\alpha_r\sim c\log r/r$,

```math
\Pr(H_Q)\asymp\frac{C}{Q^c(\log Q)^2}.
```

Using prime density $dQ/\log Q$, the corresponding series has the same
convergence behavior as

```math
\int^\infty\frac{dx}{x^c(\log x)^3}.
```

Therefore

```math
\begin{aligned}
c < 1
&\Longrightarrow
\sum_{Q\text{ prime}}\Pr(H_Q)=\infty,\\
c\ge 1
&\Longrightarrow
\sum_{Q\text{ prime}}\Pr(H_Q) < \infty.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

For $c < 1$, adequate mixing implies infinitely many head events almost surely.
For $c\ge 1$, the first Borel-Cantelli lemma implies only finitely many head
events almost surely; no independence assumption is needed for that convergent
direction.

The head threshold $c=1$ is stricter than the safe-window threshold $c=2$.
There is an intermediate regime

```math
1\le c < 2
```

in which square-safe windows remain populated almost surely under the spatial
model, while head recurrence fails almost surely in the mixed companion.

### 4.5 Adversarial/Random Parent Phase Diagram

For the representative schedule $\alpha_r\sim c\log r/r$, the companion
separates into three regimes:

| Adversarial scale | Global 2-gaps | Square-safe windows | Head recurrence |
|---|---:|---:|---:|
| $0\le c < 1$ | Persist and grow | Eventually nonempty almost surely | Infinite almost surely, with mixing |
| $1\le c < 2$ | Persist and grow | Eventually nonempty almost surely | Only finitely many almost surely |
| $c\ge 2$ | Persist and grow | Mixed expectation tends to zero | Only finitely many almost surely |
| Fixed $\alpha > 0$ | Persist and grow | Mixed expectation tends to zero | Only finitely many almost surely |

The table's last two columns are statements inside the spatial
model. The global column is unconditional for every balanced companion.

### 4.6 Why a Fixed Absolute Percentage Gives the Wrong Maximum

Within position-blind repeated mixtures, percentages that do not change with
the filter prime have a blunt but secondary answer. If the same absolute adversarial
share $\alpha$ is applied at every filter, every $\alpha > 0$ is eventually fatal
to the local mixed baseline. In that restricted normalization,

```math
\text{maximum sustainable fixed absolute adversarial share}=0\%.
```

This is not the meaningful answer to “how much worse than random can the
filter be?” Random destruction itself shrinks as $2/r$, while fixed
$\alpha > 0$ adds a positive floor and makes the relative factor
$w_r=1+(r-2)\alpha/2$ diverge linearly. The primary answer from §3.6 is instead
that every fixed finite $w$ survives the companion model defined above, with the first
transition only when $w_r$ grows on the order of $\log r$.

The zero-percent statement concerns safe-window and head survival under this
fixed absolute-share policy. It does not concern the global population, which
survives even under $100\%$ adversarial selection.

Nonzero adversariality remains supportable when its share decreases with $r$.
For a fixed margin $\varepsilon > 0$, the representative sufficient schedules
are

```math
\begin{aligned}
\alpha_r
&\le(2-\varepsilon)\frac{\log r}{r}
&&[\text{Square-Window Regime}],\\
\alpha_r
&\le(1-\varepsilon)\frac{\log r}{r}
&&[\text{Head-Recurrence Regime, With Mixing}].
\end{aligned}
```

Ignoring the required strict margin only to display the boundary curves, these
become

```math
\begin{aligned}
\text{square-window boundary percentage}
&=200\frac{\log r}{r}\%,\\
\text{head-recurrence boundary percentage}
&=100\frac{\log r}{r}\%.
\end{aligned}
```

Here $\log$ is the natural logarithm. Representative values are:

| Filter prime $r$ | Square-window boundary | Head-recurrence boundary |
|---:|---:|---:|
| $101$ | $9.14\%$ | $4.57\%$ |
| $1{,}000$ | $1.38\%$ | $0.691\%$ |
| $19{,}000$ | $0.104\%$ | $0.0519\%$ |
| $100{,}003$ | $0.0230\%$ | $0.0115\%$ |

These entries are asymptotic boundary values, not independent allowances that
reset at each filter. A schedule may temporarily cross a displayed value and
remain viable if it spent less adversarial budget earlier; it may also fail
despite staying below isolated entries if its cumulative behavior is worse on
other filters. The governing quantities remain

```math
A(Q)=\sum_{r < Q}-\log(1-\alpha_r)
```

for square windows and

```math
\sum_{Q\text{ prime}}
\frac{e^{-A(Q)}}{(\log Q)^2}
```

for head recurrence.

### 4.7 What “Percentage Adversarial” Must Specify

There is no unique mixture until we specify what receives the adversarial
label.

| Mixture | Choice made | Consequence |
|---|---|---|
| Parent level | Each parent is adversarial with probability $\alpha_r$ | Independent branching interpretation |
| Whole filter | The complete filter is adversarial with probability $\alpha_r$ | Same one-lineage marginal, stronger dependence between parents |
| One-time final | One adversarial dilution is applied after random filtering | One factor $1-\alpha$; no cumulative phase transition |

The calculations in §§3--4 concern a repeated share at every filter. Their
expectations apply to the first two interpretations because one lineage has
the same marginal survival probability. Their almost-sure conclusions do not
transfer automatically: a whole-filter choice coordinates all parents and
therefore needs its own spatial or mixing argument. The one-time model answers
a different question because it applies the loss only once.

## 5. Allocation and the Protective Parent

### 5.1 The Same Adversarial Percentage Can Produce Different Outcomes

This property is a capacity comparison. Suppose $K$ parents may use the
adversarial policy and $L$ parents contribute a child to the target window. A
target-aware allocator can clear the window exactly when its budget covers all
the relevant parents:

```math
K\ge L.
```

For a fixed adversarial share $\alpha=K/N>0$, if the relevant fraction
$L/N\longrightarrow0$, then eventually

```math
\alpha\ge\frac LN,
```

which is the same condition as $K\ge L$. Thus a fixed adversarial percentage
may be enough to suppress the head early and, after the target population
becomes sparse enough, remove every 2-gap from the tracked window. The result
depends on allocation: a position-blind allocator with the same percentage
does not automatically select all $L$ relevant parents.

We now derive the complete finite range. The target window is shorter than the
old period, so each parent contributes at most one child to it. Let

- $N$ be the total number of parents;
- $R$ be the set of parents with a child in target region $W$;
- $L=|R|$;
- $\mathcal A$ be the set of adversarial parents; and
- $K=|\mathcal A|$.

The number of target children destroyed is

```math
H=|\mathcal A\cap R|,
```

and the number surviving is

```math
S=L-H.
```

The intersection size obeys the sharp bounds

```math
\begin{aligned}
H
&\le\min(K,L)
&&[\text{Intersection Cannot Exceed Either Set}],\\
H
&\ge\max(0,K-(N-L))
&&[\text{Only }N-L\text{ Irrelevant Parents Exist}].
\end{aligned}
```

Substituting into $S=L-H$ gives

```math
\max(0,L-K)
\le S\le
\min(L,N-K).
```

Both endpoints are attainable. A target-aware allocator spends its budget on
$R$ first:

```math
S_{\mathrm{targeted}}=\max(0,L-K).
```

A protective allocator spends the same budget on the $N-L$ irrelevant parents
first:

```math
S_{\mathrm{protective}}=\min(L,N-K).
```

Between these endpoints, a position-blind allocator chooses a uniformly random
size-$K$ subset of the $N$ parents. Then

```math
H\sim\text{Hypergeometric}(N,L,K)
```

and

```math
\begin{aligned}
\mathbb E[H]&=\frac{KL}{N},\\
\mathbb E[S]&=L\left(1-\frac KN\right).
\end{aligned}
```

When $K\ge L$, the exact probability of total local destruction is

```math
\Pr(S=0)
=
\frac{\binom{N-L}{K-L}}{\binom NK}
=
\frac{\binom KL}{\binom NL}.
```

Thus the same budget can produce complete protection, average proportional
loss, or total local destruction. In particular,

```math
S_{\mathrm{targeted}}=0
\Longleftrightarrow
K\ge L
\Longleftrightarrow
\alpha\ge\frac LN.
\qquad[\text{Q.E.D.}]
```

The three scales should not be confused. At the head, $L=1$, so one correctly
allocated adversarial parent kills the current head candidate. In a sparse
tracked window, a fixed share clears the whole window once $K\ge L$. Neither
statement erases the complete-period 2-gap population: every targeted parent
still leaves $r-2$ other descendants outside the target, so the global
recurrence from §3.1 continues to grow. Preventing future head or window 2-gaps
therefore requires the allocator to repeat the targeted choice at later
filters.

The complete finite proof appears in [Appendix A.6](#appendix-a6).

### 5.2 The Protective Parent Policy

The protective parent policy is the local opposite of the adversarial parent
policy. It preserves a parent's target child whenever the exact-two deletion
rule permits that choice. It does not create extra descendants and cannot
change the global recurrence.

For parent $g$, let $T_g(W)$ be the indices of its children in target region
$W$. In the post-crossover regime,

```math
|T_g(W)|\le1.
```

Because $r\ge5$, at least $r-1\ge4$ child indices lie outside $T_g(W)$. The
protective parent policy may therefore choose a harmful pair

```math
K_{g,r}^{\mathrm{protective}}
\subseteq
(\mathbb Z/r\mathbb Z)\setminus T_g(W),
\qquad
|K_{g,r}^{\mathrm{protective}}|=2.
```

The adversarial parent policy instead chooses a pair containing the target
index whenever $T_g(W)$ is nonempty. Both policies remove exactly two children,
so both leave $r-2$ descendants globally. Their only difference is local
placement:

```math
\begin{aligned}
T_g(W)\ne\varnothing
&\Longrightarrow
\text{the protective parent preserves the target child},\\
T_g(W)\ne\varnothing
&\Longrightarrow
\text{the adversarial parent destroys the target child}.
\end{aligned}
```

The protective parent is an oracle comparison, not a plausible random filter.
It is allowed to see the chosen target and place its two deletions elsewhere.
Its purpose is to define the protective endpoint of the same balanced family
in which the adversarial parent defines the pessimistic endpoint.

### 5.3 Fixed-Cohort Survival Under Adversarial/Protective Parent Mixing

We next alternate the two target-aware endpoint policies without letting the
allocator inspect current positions. Consider $N_0$ locally relevant lineages
followed through a fixed finite chain
of filters. At filter $r$, every surviving lineage independently becomes an
adversarial parent with probability $\alpha_r$ or a protective parent with
probability $1-\alpha_r$. The adversarial policy destroys its target child;
the protective policy preserves it. The calculation changes if the allocator
may first observe which parents are locally relevant.

One lineage survives the complete chain with probability

```math
\begin{aligned}
P_Q
&=\prod_{r < Q}(1-\alpha_r)
&&[\text{Survive Every Independent Filter Label}]\\
&=e^{-A(Q)}.
&&[\text{Definition Of }A(Q)]
\end{aligned}
```

Independence between parent lineages then gives

```math
X_Q\sim\text{Binomial}(N_0,P_Q),
```

so

```math
\begin{aligned}
\mathbb E[X_Q]&=N_0e^{-A(Q)},\\
\Pr(X_Q > 0)&=1-\left(1-e^{-A(Q)}\right)^{N_0}.
\end{aligned}
```

For one filter this reduces to

```math
X_{k+1}\mid X_k=N
\sim
\text{Binomial}(N,1-\alpha_r),
```

with immediate wipeout probability $\alpha_r^N$. Population redundancy is
therefore useful under blind parent assignment: every relevant lineage must
become an adversarial parent in the same transition to erase the cohort.

If $\alpha_r=\alpha > 0$ is constant, then

```math
P_Q=(1-\alpha)^{\pi(Q)+O(1)}\longrightarrow0.
```

Every one of the finite $N_0$ lineages eventually becomes an adversarial parent
with probability one. Hence the fixed cohort becomes extinct almost surely even
though every lineage continues to have $r-2$ descendants elsewhere in the
complete period.

Compared with the adversarial/random mixture, the adversarial/protective law removes the random
factor $1-2/r$:

```math
\begin{aligned}
s_r^{\mathrm{adversarial/random}}
&=(1-\alpha_r)\left(1-\frac2r\right),\\
s_r^{\mathrm{adversarial/protective}}
&=1-\alpha_r.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

This improvement is local. It does not overcome a fixed positive adversarial
share repeated through infinitely many filters.

### 5.4 Growing Square Windows Under Adversarial/Protective Parent Mixing

The protective policy removes the balanced-random density penalty by
preserving every eligible target child. Suppose the fully protective model
supplies $B(Q)\asymp C_0Q^2$ eligible lineages in the square window, while
adversarial assignments remain independent and position-blind. The cumulative
adversarial-label probability $e^{-A(Q)}$ is then the only local loss.

From §5.3, each of the $B(Q)$ eligible lineages survives with probability
$e^{-A(Q)}$. Therefore

```math
X_Q^{\mathrm{adversarial/protective}}
\sim
\text{Binomial}\left(B(Q),e^{-A(Q)}\right)
```

and

```math
\begin{aligned}
\lambda_Q^{\mathrm{adversarial/protective}}
&:=\mathbb E[X_Q^{\mathrm{adversarial/protective}}]\\
&=B(Q)e^{-A(Q)}\\
&\asymp C_0Q^2e^{-A(Q)}.
\end{aligned}
```

The empty-window probability satisfies

```math
\begin{aligned}
\Pr(X_Q^{\mathrm{adversarial/protective}}=0)
&=\left(1-e^{-A(Q)}\right)^{B(Q)}\\
&\le e^{-\lambda_Q^{\mathrm{adversarial/protective}}}.
&&[1-x\le e^{-x}]
\end{aligned}
```

Taking logarithms gives the phase boundary

```math
\log\lambda_Q^{\mathrm{adversarial/protective}}
=2\log Q-A(Q)+O(1).
```

Hence, for every fixed $\varepsilon > 0$,

```math
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{adversarial/protective}}\longrightarrow\infty,\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{adversarial/protective}}\longrightarrow0.
\end{aligned}
```

In the first regime the expectation grows polynomially, the empty-window
probabilities are summable, and the first Borel-Cantelli lemma gives only
finitely many empty square windows almost surely.

For the representative schedule

```math
\alpha_r\sim c\frac{\log r}{r},
```

we have $A(Q)\sim c\log Q$ and therefore

```math
\lambda_Q^{\mathrm{adversarial/protective}}\asymp C_0Q^{2-c}.
```

Thus

```math
\begin{aligned}
c < 2
&\Longrightarrow
\text{eventually nonempty square windows almost surely},\\
c=2
&\Longrightarrow
\text{critical order-one expected population},\\
c > 2
&\Longrightarrow
\text{expected population tends to zero}.
\end{aligned}
```

The leading threshold $c=2$ matches the adversarial/random companion, but the boundary
term differs:

```math
\begin{aligned}
\lambda_Q^{\mathrm{adversarial/random}}
&\asymp C\frac{Q^{2-c}}{(\log Q)^2},\\
\lambda_Q^{\mathrm{adversarial/protective}}
&\asymp C_0Q^{2-c}.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

At $c=2$, the random mixture tends to zero while the protective mixture retains only
an order-one expectation, still insufficient for eventual almost-sure
nonemptiness.

### 5.5 Head Recurrence Under Adversarial/Protective Parent Mixing

At the head, the protective policy can preserve an eligible lineage but cannot
create one. Let $b_Q$ be its availability probability and suppose
$b_Q\ge b > 0$ for all sufficiently large $Q$. Conditional on availability,
the lineage must avoid every adversarial assignment in its chain. Independence
or adequate weak mixing between head events then supplies the recurrence step.

```math
\Pr(H_Q)=b_Qe^{-A(Q)}.
```

The lower bound on $b_Q$ makes the recurrence criterion equivalent, up to
positive constants, to

```math
\sum_{Q\text{ prime}}e^{-A(Q)}.
```

Under adequate cross-layer mixing, the second Borel-Cantelli lemma gives

```math
\sum_{Q\text{ prime}}e^{-A(Q)}=\infty
\Longrightarrow
H_Q\text{ occurs infinitely often almost surely}.
```

If the series converges, the first Borel-Cantelli lemma gives only finitely many
head events almost surely without any independence premise.

For

```math
\alpha_r\sim c\frac{\log r}{r},
```

we have $e^{-A(Q)}\asymp Q^{-c}$. The prime-head series therefore behaves like

```math
\sum_{Q\text{ prime}}\frac1{Q^c}.
```

The prime harmonic series diverges at $c=1$, while the series converges for
$c > 1$. Hence

```math
\begin{aligned}
c\le1
&\Longrightarrow
\text{infinitely many head events almost surely, with mixing},\\
c > 1
&\Longrightarrow
\text{only finitely many head events almost surely}.
\end{aligned}
```

The boundary differs from adversarial/random mixing. There the balanced-random head
density contributes $(\log Q)^{-2}$:

```math
\begin{aligned}
\Pr(H_Q^{\mathrm{adversarial/random}})
&\asymp\frac1{Q^c(\log Q)^2},\\
\Pr(H_Q^{\mathrm{adversarial/protective}})
&\asymp\frac{b_Q}{Q^c}.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

At $c=1$, the adversarial/random prime series converges, while the adversarial/protective series
diverges. Thus the protective parent policy changes the inclusion of the critical boundary,
even though both mixtures have the same leading threshold scale.

For the gentler schedule $\alpha_r\sim c/r$, the occurrence probability is
comparable to $(\log Q)^{-c}$ and the sum over prime heads diverges for every
fixed finite $c$.

### 5.6 Parent-Mixture Comparison

Under their respective spatial premises, the two position-blind mixtures have
the following asymptotic behavior:

| Adversarial schedule | Adversarial/random square window | Adversarial/protective square window | Adversarial/random head | Adversarial/protective head |
|---|---:|---:|---:|---:|
| Fixed $\alpha > 0$ | Expectation tends to zero | Expectation tends to zero | Finitely many almost surely | Finitely many almost surely |
| $\alpha_r\sim c/r$ | Eventually nonempty almost surely | Eventually nonempty almost surely | Infinite with mixing | Infinite with mixing |
| $\alpha_r\sim c\log r/r$, $c < 1$ | Eventually nonempty almost surely | Eventually nonempty almost surely | Infinite with mixing | Infinite with mixing |
| $\alpha_r\sim c\log r/r$, $c=1$ | Eventually nonempty almost surely | Eventually nonempty almost surely | Finitely many almost surely | Infinite with mixing |
| $\alpha_r\sim c\log r/r$, $1 < c < 2$ | Eventually nonempty almost surely | Eventually nonempty almost surely | Finitely many almost surely | Finitely many almost surely |
| $\alpha_r\sim c\log r/r$, $c=2$ | Expectation tends to zero | Order-one expectation | Finitely many almost surely | Finitely many almost surely |
| $\alpha_r\sim c\log r/r$, $c > 2$ | Expectation tends to zero | Expectation tends to zero | Finitely many almost surely | Finitely many almost surely |

The protective parent policy removes the balanced-random $(\log Q)^{-2}$ loss. This does
not change the leading square-window threshold $c=2$, because the quadratic
window dominates logarithmic factors away from the boundary. It does change
the boundary behavior and, most visibly, includes $c=1$ on the recurrent side
of the head transition.

Every entry assumes position-blind adversarial labels. A target-aware allocator
is governed by §5.1 instead and may erase the head with one correctly placed
adversarial label regardless of this table's percentage regime.

## 6. Allocation Mechanisms and Local Damage

### 6.1 Mechanism Families

An adversarial share becomes meaningful only after we say how policies are
assigned to parents. A useful comparison begins with a position-blind
allocator and then adds positional information in controlled steps. We write
$P$ for a protective parent and $A$ for an adversarial parent.

| Mechanism | Adversarial share | Position information | What it measures |
|---|---:|---:|---|
| Independent parent coin | Random around $\alpha_r$ | None | Simplest branching law |
| Exact-quota shuffle | Exactly $K/N$ | None | Canonical finite-population baseline |
| Shuffled alternation, $P,A,P,A,\ldots$ | Fixed by pattern | None | Balanced deterministic labels after shuffling |
| Block-balanced shuffle | Fixed inside each block | None | Sensitivity to local clustering |
| Random cyclic mask | Fixed by pattern | None | Sensitivity to periodic allocation |
| Position-blind hash | Random around $\alpha_r$ | None | Reproducible parent coins |
| Delayed adversary | Exactly $K/N$ | Previous layer | Persistence of positional information |
| Noisy ranking | Exactly $K/N$ | Tunable | Transition from blind to targeted allocation |
| Perfect adversary | Exactly $K/N$ | Current layer | Worst-case endpoint |

The exact-quota shuffle is the primary null model because it fixes the budget
without using position. Shuffled patterns and block balance test whether local
clustering changes the result. A delayed allocator can use only the previous
layer, while noisy ranking assigns weight $e^{-\beta d_g}$ to a parent at
distance $d_g$ from the target. Thus $\beta=0$ is uniform allocation and large
$\beta$ approaches the perfect adversary.

Every mechanism assigns one policy to a parent; the chosen policy still removes
exactly two of that parent's children. Alternating labels cannot restore a
target child destroyed at an earlier filter, and an unshuffled periodic pattern
may lock to the sieve geometry. We therefore compare mechanisms through their
realized local damage and targeting strength rather than through the scheduled
percentage alone.

### 6.2 Targeting and Local Hazard

The primary observed state space has two coordinates:

```math
(w_r,\theta_r)
=
(\text{damage relative to random},\text{realized targeting strength}).
```

The first says how much total damage the tracked segment actually received.
The second says how concentrated the controllable adversarial-label budget was relative
to the locally relevant parents. The scheduled share $\alpha_r=K_r/N_r$
remains an experimental input, but it is not itself the local damage.

#### Normalized Targeting Strength

For one nondegenerate transition, retain the notation from §5.1 and define

```math
\begin{aligned}
H_{\min}&=\max(0,K-(N-L)),\\
H_0&=\frac{KL}{N},\\
H_{\max}&=\min(K,L).
\end{aligned}
```

These are the protective minimum, uniform-random mean, and adversarial maximum
numbers of locally relevant parents hit. When
$H_{\min} < H_0 < H_{\max}$, normalize the realized hit count $H$ by

```math
\theta(H)=
\begin{cases}
\dfrac{H-H_0}{H_0-H_{\min}},&H\le H_0,\\[8pt]
\dfrac{H-H_0}{H_{\max}-H_0},&H\ge H_0.
\end{cases}
```

Then

```math
\begin{aligned}
\theta=-1&\Longleftrightarrow H=H_{\min}
&&[\text{Protective Endpoint}],\\
\theta=0&\Longleftrightarrow H=H_0
&&[\text{Uniform Benchmark}],\\
\theta=1&\Longleftrightarrow H=H_{\max}
&&[\text{Targeted Endpoint}].
\end{aligned}
```

The center $H_0$ is an expectation and need not be an integer, so a finite
realization need not attain $\theta=0$ exactly. It remains the neutral reference
point.

Degenerate cases with a zero denominator should report the raw tuple
$(N,L,K,H)$ instead of assigning a synthetic score. In every case the local
survivor count remains the exact observable

```math
S=L-H.
```

The score measures realized placement, not hostile intent. A random shuffle
may occasionally produce positive $\theta$, and a nominal adversary with poor
information may produce negative $\theta$.

#### Realized Local Hazard

Let $T_r$ be the total number of locally relevant target children destroyed by
the complete filter, including both random-baseline and adversarial-label destruction.
Define

```math
f_r^{\mathrm{local}}=\frac{T_r}{L_r},
\qquad
w_r^{\mathrm{local}}=\frac{rT_r}{2L_r},
\qquad L_r > 0.
```

In the pure adversarial/protective assignment, an adversarial label destroys
its target and a protective label preserves it, so $T_r=H_r$. In the
adversarial/random assignment, $T_r$ also contains the random branch's $2/r$
baseline. For blind adversarial/random labels,

```math
\mathbb E[f_r^{\mathrm{local}}]
\approx
\alpha_r+(1-\alpha_r)\frac2r.
```

A perfect adversary can make $f_r^{\mathrm{local}}=1$ even when the global
budget $\alpha_r=K_r/N_r$ is tiny, provided its budget and information cover
the local target.

The cumulative local hazard from §3.3 is

```math
D(Q)
=
\sum_{r < Q}-\log\left(1-f_r^{\mathrm{local}}\right),
```

whenever every factor is positive. If one transition has
$f_r^{\mathrm{local}}=1$, the tracked local cohort is extinct and $D(Q)$ is
effectively infinite from that point. This diagnostic generalizes $A(Q)$ and
includes the random baseline rather than counting only the excess adversarial-label
loss. The separation between scheduled $\alpha_r$, realized
$w_r^{\mathrm{local}}$, and targeting score $\theta_r$ measures respectively
policy budget, total relative damage, and the value of positional information.

When the locally relevant population is redefined at every transition rather
than following one cohort, $D(Q)$ is only a cumulative diagnostic; it is not an
exact survival exponent for a single population.

We can therefore read the earlier phase calculations with three
levels of input:

- $A(Q)$ is the scheduled budget under the blind-allocation model;
- $D(Q)$ is the realized total local damage after allocation; and
- $\theta_r$ records how strongly the controllable budget targeted the segment.

Only the first has a closed form from $\alpha_r$ alone. The general survival
law and relative phase diagram use $D(Q)$ or $w_r^{\mathrm{local}}$ directly.

### 6.3 Comparing the Allocation Mechanisms

The mechanisms differ in how much they know about the target, so we compare
them with the same strike budget and the same target region. Uniform shuffling
is the neutral reference. Block balance and delayed information show whether
dependence alone changes the result. Noisy ranking moves continuously toward
the perfectly targeted endpoint.

| Allocation | Information about the target | Role in the comparison |
|---|---|---|
| Uniform exact quota | None | Random baseline |
| Block-balanced quota | None, but locally dependent | Clustering test |
| Delayed allocation | Previous layer only | Memory test |
| Noisy ranking | Partial current information | Intermediate targeting |
| Perfect allocation | Complete current information | Adversarial endpoint |

For each transition, the essential observation is the tuple

```math
(N_r,L_r,K_r,H_r,T_r,w_r^{\mathrm{local}},\theta_r).
```

It records the total and locally relevant parents, the available adversarial
budget, the number of relevant parents selected, the total local destruction,
the damage relative to random, and the targeting score. Exact-quota companions
also retain $J_r$, $u_r=J_r/N_r^{\mathrm{strike}}$, and the cumulative sums

```math
\sum_{r < Q}u_r
\qquad\text{and}\qquad
\sum_{r < Q}\left(u_r^2+\frac{u_r}{N_r^{\mathrm{strike}}}\right),
```

because matching one finite strike count does not establish the cumulative
conditions used in §7.1.

The real modular filter has no assigned parent policy, but the same local
observations still apply. Its hit count can be compared with the protective
minimum, uniform mean, and adversarial maximum from §6.2. Across successive
heads, $D(Q)$ then shows whether the arithmetic placement remains near the
random companion or accumulates damage like an informed allocator. This is a
comparison of behavior, not an attribution of intent.

## 7. Exact-Quota Companion Processes

### 7.1 Exact CRT Quotas With Random Locations

The random parent model fixes two harmful copy indices per parent. A closer
statistical companion can instead retain the exact number of accepted strikes
supplied by a chosen CRT population and randomize only their locations. This
preserves the real count while removing the arithmetic targeting information.
Exact quotas create dependence within one layer, but they do not change the
one-position survival scale when allocated uniformly. The head result also
uses persistent availability and cross-layer mixing, while the square-window
result uses blind placement and a quadratic eligible supply.

At filter $r$, let $U_r$ contain $N_r$ eligible values and let the CRT quota be
$J_r$, with $0\le J_r\le N_r-2$. The exact-quota random parent model chooses one
uniformly random size-$J_r$ subset of $U_r$ as its strike set. For a specified
2-gap whose two endpoints belong to $U_r$, both endpoints survive precisely
when every strike is selected from the other $N_r-2$ values. Therefore

```math
\begin{aligned}
s_r
&=\frac{\binom{N_r-2}{J_r}}{\binom{N_r}{J_r}}
&&[\text{Uniform Exact-Quota Choice}]\\
&=\frac{(N_r-J_r)(N_r-J_r-1)}{N_r(N_r-1)}.
&&[\text{Factorial Simplification}]
\end{aligned}
```

Write the strike fraction as

```math
u_r:=\frac{J_r}{N_r}.
```

The exact formula gives

```math
\log s_r
=-2u_r+O\left(u_r^2+\frac{u_r}{N_r}\right).
```

This separates the exact finite quota from the cumulative condition needed for
recurrence. Assume that along the conditioned chain to head $Q$,

```math
\begin{aligned}
\sum_{r < Q}u_r
&=\log\log Q+O(1),
&&[\text{CRT-Rate Cumulative Quota}]\\
\sum_{r < Q}
\left(u_r^2+\frac{u_r}{N_r}\right)
&=O(1).
&&[\text{Summable Finite-Population Error}]
\end{aligned}
```

The complete-period CRT benchmark $u_r=1/r$ satisfies these conditions. A
different local CRT quota must be checked against them; preserving a numerical
strike count alone does not make the conclusion automatic.

Multiplying the exact without-replacement factors gives

```math
\begin{aligned}
P_{\mathrm{quota}}(Q)
&=\prod_{r < Q}s_r
&&[\text{Survive Every Filter}]\\
&=\exp\left(\sum_{r < Q}\log s_r\right)
&&[\text{Product To Sum}]\\
&=\exp\left(-2\sum_{r < Q}u_r+O(1)\right)
&&[\text{Summable Error}]\\
&\asymp\frac{C}{(\log Q)^2}.
&&[\text{Cumulative Quota Condition}]
\end{aligned}
```

Thus the exact-quota companion has the same one-head survival order as the
random parent model. It is not an independent Bernoulli filter inside one
layer; it is a uniform shuffle conditioned on the exact CRT strike count.

Suppose the distinguished head candidate is eligible with conditional
probability at least $b_0 > 0$, uniformly for all sufficiently large prime heads,
and that this availability is compatible with the quota-survival experiment.
Then

```math
\begin{aligned}
b_0P_{\mathrm{quota}}(Q)
&\le\Pr(H_Q)\le P_{\mathrm{quota}}(Q),
&&[\text{Uniform Availability Bounds}]\\
\Pr(H_Q)
&\asymp\frac{1}{(\log Q)^2}.
&&[\text{Quota Survival Asymptotic}]
\end{aligned}
```

Consequently,

```math
\begin{aligned}
\sum_{Q\text{ prime}}\Pr(H_Q)
&\asymp
\sum_{Q\text{ prime}}\frac{1}{(\log Q)^2}\\
&=\infty.
&&[\text{Prime Number Theorem}]
\end{aligned}
```

Under independence or an adequate cross-layer mixing condition, the second
Borel-Cantelli lemma yields

```math
\Pr(H_Q\text{ occurs infinitely often})=1.
\qquad[\text{Q.E.D.}]
```

This is an almost-sure theorem, not a guarantee for every random realization.
The set of realizations with only finitely many head hits has probability zero,
but it is not logically empty.

For square-safe windows, assume $B(Q)\asymp C_0Q^2$ eligible starts and the
same blind-placement empty-window premise used by the random parent model.
Then

```math
\begin{aligned}
\lambda_{\mathrm{quota}}(Q)
&=B(Q)P_{\mathrm{quota}}(Q)
&&[\text{Expected Surviving Starts}]\\
&\asymp
C_0\frac{Q^2}{(\log Q)^2}
\longrightarrow\infty.
&&[\text{Quadratic Supply Dominates}]
\end{aligned}
```

If

```math
\Pr(W_Q\text{ is empty})
\le e^{-\lambda_{\mathrm{quota}}(Q)},
```

the empty probabilities are summable over prime $Q$. The first Borel-Cantelli
lemma then gives only finitely many empty square windows almost surely. This
eventual-window statement is stronger than the twin-prime-style target: an
unbounded sequence of successful windows, or infinitely many head hits, is
already sufficient for infinitely many distinct certificates.

For consecutive primes $p < q$, the real accepted-strike count in the next safe
window is proved in [Gap Dynamics §9.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#91-exact-accepted-strikes) [[2]](#ref2):

```math
A(p,q)
=
\pi\left(\left\lfloor\frac{q^2-1}{p}\right\rfloor\right)
-\pi(p-1).
```

Using this local quota as $J_r=A(p,q)$ in the random-location companion is well
defined, but its fractions $u_r=J_r/N_r$ must still satisfy the displayed
cumulative conditions for the head proof above. The
[complete-period count](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#52-exact-non-recursive-global-count) [[2]](#ref2) supplies the
global density; neither exact count determines local placement in the real
sieve.

### 7.2 Biased Exact Quotas and the Logarithmic Skew Frontier

The neutral exact-quota companion treats every eligible value symmetrically.
We now keep the same quota $J_r$ while making
2-gap endpoints proportionally more likely to receive a harmful strike. This
asks how much positional preference the quota can carry before the almost-sure
head conclusion changes. We use a group-exchangeable allocation law, assume
double strikes on one endpoint pair have quadratic order, and retain the
availability, placement, and mixing premises of §§3.5 and 7.1.

Let $E_r\subseteq U_r$ be the eligible values that are endpoints of locally
relevant 2-gaps, and define

```math
x_r:=\frac{|E_r|}{N_r},
\qquad
u_r:=\frac{J_r}{N_r}.
```

Stipulate a group-exchangeable size-$J_r$ allocation law in which every
endpoint has marginal inclusion probability $p_r^{E}$, every ordinary value
has marginal inclusion probability $p_r^{O}$, and the endpoint preference
ratio is

```math
\beta_r:=\frac{p_r^{E}}{p_r^{O}}\ge1.
```

The fixed quota forces the average marginal inclusion probability to equal
$u_r$. Therefore

```math
\begin{aligned}
x_rp_r^{E}+(1-x_r)p_r^{O}
&=u_r
&&[\text{Exact Quota}]\\
p_r^{O}
&=\frac{u_r}{1+(\beta_r-1)x_r}
&&[\text{Substitution}]\\
p_r^{E}
&=\frac{\beta_ru_r}{1+(\beta_r-1)x_r}.
&&[\text{Simplification}]
\end{aligned}
```

Define the quota-normalized preference

```math
\kappa_r^{\mathrm{eff}}
:=
\frac{\beta_r}{1+(\beta_r-1)x_r}.
```

For one 2-gap, assume the probability that both endpoints are struck is
$O((p_r^{E})^2)$. Its destruction fraction then satisfies

```math
\begin{aligned}
f_r
&=2p_r^{E}-\Pr(\text{both endpoints are struck})
&&[\text{Inclusion-Exclusion}]\\
&=2u_r\kappa_r^{\mathrm{eff}}
+O\left((u_r\kappa_r^{\mathrm{eff}})^2\right).
&&[\text{Normalized Preference}]
\end{aligned}
```

The raw weight $\beta_r$ and the effective destruction skew are not identical:
the exact quota must take probability away from ordinary values when it gives
more probability to endpoints. In the complete-period density regime,

```math
x_r\asymp\frac{C}{(\log r)^2}.
```

Consequently, if $\beta_r=O(\log r)$,

```math
\kappa_r^{\mathrm{eff}}
=\beta_r\left(1+O\left(\frac1{\log r}\right)\right).
```

They have the same leading logarithmic coefficient, although their lower-order
terms can differ at the exact boundary.

For the phase theorem, measure skew by the realized effective factor

```math
\kappa_r
:=\frac{f_r}{2/r}.
```

This is the same quantity called $w_r$ in the general hazard analysis. Its
cumulative survival is defined once $2\kappa_r < r$. Every regime below satisfies
this inequality for all sufficiently large filters; the finite prefix is
absorbed into a positive constant. Thus

```math
P_{\kappa}(Q)
=
\prod_{r < Q}\left(1-\frac{2\kappa_r}{r}\right)
=e^{-D_{\kappa}(Q)},
```

where

```math
D_{\kappa}(Q)
:=
\sum_{r < Q}-\log\left(1-\frac{2\kappa_r}{r}\right).
```

If $\kappa_r=\kappa < \infty$ is fixed, then

```math
\begin{aligned}
D_{\kappa}(Q)
&=2\kappa\log\log Q+O(1)
&&[\text{Prime Harmonic Sum}]\\
P_{\kappa}(Q)
&\asymp\frac{C_{\kappa}}{(\log Q)^{2\kappa}}.
&&[\text{Exponentiation}]
\end{aligned}
```

The sum of this probability over prime heads diverges for every finite
$\kappa$. With persistent head availability and adequate cross-layer mixing,

```math
\text{every fixed finite proportional skew gives infinitely many head hits almost surely.}
```

Thus there is no finite constant-skew maximum.

The first transition appears when effective skew grows logarithmically. Set

```math
\kappa_r=1+c\log r,
\qquad c\ge0.
```

Then

```math
\begin{aligned}
D_c(Q)
&=2\log\log Q+2c\log Q+O(1)
&&[\text{Prime-Sum Asymptotics}]\\
P_c(Q)
&\asymp\frac{C_c}{Q^{2c}(\log Q)^2}.
&&[\text{Exponentiation}]
\end{aligned}
```

For prime heads, the occurrence series has the same convergence behavior as

```math
\int^\infty\frac{dx}{x^{2c}(\log x)^3}.
```

Therefore

```math
\begin{aligned}
c < \frac12
&\Longrightarrow
\text{infinitely many head hits almost surely, with mixing},\\
c\ge\frac12
&\Longrightarrow
\text{only finitely many head hits almost surely}.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

In this explicitly normalized family, the equality $c=1/2$ is on the failure
side because the remaining factor $(\log Q)^{-2}$ makes the boundary prime
series converge. If $\beta_r$, rather than effective $\kappa_r$, is specified
at its raw equality boundary, quota normalization changes lower-order terms and
the cumulative series $D_{\kappa}(Q)$ must be evaluated directly.

The robust head-safe frontier is therefore

```math
\kappa_r
\le
1+\left(\frac12-\varepsilon\right)\log r
\quad\Longrightarrow\quad
\text{head recurrence almost surely, with mixing}.
```

For square windows, quadratic supply gives the larger robust frontier

```math
\kappa_r
\le
1+(1-\varepsilon)\log r
\quad\Longrightarrow\quad
\text{eventual square-window occupancy almost surely}.
```

Hence the intermediate range between approximately $(1/2)\log r$ and
$\log r$ preserves square windows but not infinitely recurring head hits. The
window statement is stronger than necessary: the twin-prime-style conclusion
needs only infinitely many successful windows.

For an irregular skew schedule, the head criterion is

```math
\sum_{Q\text{ prime}}e^{-D_{\kappa}(Q)}=\infty,
```

together with persistent availability and adequate mixing. A pointwise skew
percentage cannot replace this cumulative test.

## 8. Relation to the Real Sieve

For a real 2-gap $(a,a+2)$ and incoming prime $r$, the harmful copies are not
chosen freely. They are fixed by

```math
K_{a,r}^{\mathrm{real}}
=
\{-aM^{-1},-(a+2)M^{-1}\}\pmod r.
```

Different parents are coupled through this single arithmetic rule. The real
filter has neither independent policy coins nor freely allocated protective and
adversarial labels. It nevertheless has directly measurable local destruction $f_r$, a
relative factor $w_r=rf_r/2$, and cumulative hazard $D(Q)$. Assigning it an
effective policy share $\alpha_r$ requires an additional declared companion
benchmark, while assessing its positional concentration requires the separate
hit count and targeting normalization from §6.2.

The relative factor defined in §3.2 provides a finite-transition destruction
normalization. Section 6.2 adds the allocation question: for the same global
destruction budget, how close is the realized local hit count to the uniform
mean or targeted maximum?

The companion diagrams identify what a transfer theorem would need to control:

- the realized relative damage $w_r$ and cumulative hazard $D(Q)$;
- the exact-quota fractions $u_r$ and their cumulative deviation from
  $\sum_{r < Q}1/r$;
- raw endpoint preference $\beta_r$, quota-normalized effective skew
  $\kappa_r^{\mathrm{eff}}$, and cumulative skew hazard $D_{\kappa}(Q)$;
- any scheduled or effective policy budget $A(Q)$ used for a particular
  companion specialization;
- the availability and abundance premises for the chosen target; and
- a deterministic discrepancy bound comparing the real head indicators $I_Q$
  with the divergent companion reference weights $\rho_Q$, as formalized in
  §10.

### 8.1 Finite Empirical Comparison With Random

We can compare the real sieve with the random companion at two square-window
scales. The first comparison counts the 2-gaps already present in each
sequence's own window. For head $h$, let $G_{\mathrm{real}}(h)$ be the number
of real 2-gap starts in $[h,h^2)$. The random companion expectation is

```math
E_{\mathrm{random}}(h)
=(h^2-h)\frac12
\prod_{3\le r < h}\left(1-\frac2r\right).
```

The $c=1$ square-window frontier adds the logarithmic excess hazard from §3.5:

```math
E_{c=1}(h)
=E_{\mathrm{random}}(h)
\prod_{7\le r < h}
\left(1-\frac{2\log r}{r-2}\right).
```

The figure compares these two expectations with the real count in every fully
covered sequence window. Across 188 heads from $3$ through $1129$, the mean
ratio $G_{\mathrm{real}}/E_{\mathrm{random}}$ is $0.967$. At the largest
covered head it is $0.947$: the real window contains $10{,}056$ 2-gaps,
compared with a random expectation of $10{,}616$. The corresponding $c=1$
frontier expectation is only $0.0845$. Over this finite range, the real
square-window population follows the random scale and remains far above the
square-window failure frontier.

![Real per-sequence square-window 2-gap counts compared with the random expectation and the c=1 square-window frontier](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/per-sequence-frontier.svg)

The figure is generated by the [per-sequence frontier calculation](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/per_sequence_frontier_chart.py)
from the [per-sequence survivor data](https://github.com/thiagomata/prime-numbers/blob/master/data/sieve-sequence/first_gaps_per_seq.csv).

The second comparison isolates one transition. For consecutive primes $p<q$,
let $G_p$ be the pre-filter 2-gap population in $[q,q^2)$ and let $H_p$ be the
number destroyed when filter $p$ is installed. The observed fraction and its
relative factor are

```math
f_p^{\mathrm{real}}:=\frac{H_p}{G_p},
\qquad
w_p^{\mathrm{real}}:=\frac{pf_p^{\mathrm{real}}}{2}.
```

The chart compares $f_p^{\mathrm{real}}$ with the random rate $2/p$ and the
$c=1$ square-window boundary $2(1+\log p)/p$. Among 187 distinct measured
transitions from $p=3$ through $p=19{,}429$, 186 lie below the random rate and
the remaining transition, $p=3$, equals it. Ninety-five transitions destroy no
2-gap in the measured window. From $p\ge1000$, the largest observed relative
factor is

```math
w_p^{\mathrm{real}}=0.0523.
```

Thus the measured real transition is not slightly more destructive than the
random filter; on these windows it is substantially less destructive.

![Real per-transition square-window 2-gap destruction compared with the random rate and the c=1 square-window boundary](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/frontier-comparison-stages.svg)

The figure is generated by the [per-transition frontier calculation](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/frontier_comparison_stages_chart.py)
from the [dense](https://github.com/thiagomata/prime-numbers/blob/master/data/candidates/window-measurements.csv) and
[sparse](https://github.com/thiagomata/prime-numbers/blob/master/data/candidates/window-measurements-sparse.csv) transition data.
Zero-destruction transitions are displayed on the chart's $10^{-7}$ floor so
that they remain visible on a logarithmic axis.

The two findings are compatible. The first chart measures the population left
after all earlier filters; the second isolates the next filter acting on a new
window. Neither dataset follows one fixed cohort through every filter below a
single head, so their changing-window fractions cannot be multiplied into one
cumulative hazard.

The complete modular cycle supplies an exact reference in two complementary
views. The first is local to one filter: it asks what fraction of the expanded
cyclic population that filter destroys. The second is cumulative: it asks how
much of a normalized starting population remains after those one-filter
fractions are compounded. The two figures below deliberately mirror these two
steps of the calculation.

#### Exact Per-Filter Destruction

If $T$ old cyclic 2-gaps are expanded through a new prime $r$, there are $rT$
copies and exactly two harmful copy indices per parent. Consequently,

```math
\begin{aligned}
H_r^{\mathrm{cycle}}
&=2T
&&[\text{Two Harmful Copy Classes}],\\
f_r^{\mathrm{cycle}}
&=\frac{H_r^{\mathrm{cycle}}}{rT}
=\frac2r
&&[\text{Substitution}],\\
w_r^{\mathrm{cycle}}
&=1,
&&[\text{By Definition}],\\
D_{\mathrm{cycle}}(R)-D_{\mathrm{random}}(R)
&=0.
&&[\text{Termwise Equality; Q.E.D.}]
\end{aligned}
```

Thus the full-cycle destruction fraction equals the neutral benchmark as a
count identity. This does not say that the harmful positions are independently
random. The figure below makes the identity visible alongside the $c=1$
reference on the valid range $29\le r\le251$. Its simplicity is the point:
the overlap between the exact-cycle and neutral curves is the graphical form
of the algebra above, while the separated $c=1$ curve shows the scale of the
hypothetical logarithmic worsening. The chart is strong precisely because the
reader can verify the stated relationship without additional interpretation.

![Exact full-cycle 2-gap destruction fraction compared with the neutral rate and the c=1 reference](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/full-cycle-destruction.svg)

The figure is generated by the [full-cycle destruction calculation](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/full_cycle_destruction_chart.py).
The underlying two-class result is proved in [Gap Dynamics §6.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#61-one-new-prime-forbids-two-copy-classes) [[2]](#ref2).

#### Cumulative Survival Consequence

The first diagram makes the proved one-filter equality visible. Compounding
those same factors gives the normalized complete-cycle survival reference

```math
\begin{aligned}
P_{\mathrm{cycle}}(29,R)
&=\prod_{29\le p\le R}\left(1-\frac2p\right),\\
P_{c=1}(29,R)
&=\prod_{29\le p\le R}
\left(1-\frac{2(1+\log p)}p\right).
\end{aligned}
```

At $R=251$, these normalized products are $0.3733$ and $0.003676$,
respectively, a ratio of about $102$. The second figure therefore shows the
cumulative consequence that the first figure cannot show by itself: the
repeated per-filter separation from the $c=1$ schedule compounds into a
separation of more than two orders of magnitude over the plotted range. The anchor $29$ is
the first plotted prime and keeps every $c=1$ factor in $(0,1)$; changing a
finite anchor changes the normalizing constants, not the asymptotic exponents.
This is a reference comparison, not evidence of head recurrence.

![Normalized full-cycle 2-gap survival under the exact per-filter law compared with the c=1 schedule](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/full-cycle-survival.svg)

The figure is generated by the [full-cycle survival calculation](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/full_cycle_survival_chart.py).

Read together, the two full-cycle figures give a direct progression from the
one-filter identity to its cumulative effect. A separate fixed-cohort
experiment then asks the next question: what remains true when a finite window
cuts through partial cycles? It follows every 2-gap start initially present
in $[Q,Q^2)$ through all filters $r<Q$. Exact set comparisons at $Q=17$ and
$Q=101$ confirm that this explicit cohort agrees layer by layer with the
maintained Reading A lineage. For

```math
c_{\mathrm{eff}}(r)
:=\frac{D_{\mathrm{real}}(r)-D_{\mathrm{random}}(r)}{2\log r},
```

the four runs $Q\in\{17,101,251,503\}$ give signed values between $-0.0353$
and $0.00908$. The largest positive value is $0.00907$ at $Q=251$; among the
two larger runs, all absolute values are at most $0.00908$. Because the
complete-cycle excess is exactly zero, these small positive and negative
deviations measure how the fixed interval cuts partial cycles. They are finite
window-boundary effects, not a structural excess or deficit of the sieve.

![Cumulative hazard of fixed-window 2-gap cohorts for four finite Q values](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/fixed-lineage-hazard.svg)

The figure is generated by the [fixed-lineage hazard calculation](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/fixed_lineage_hazard_chart.py)
from the dedicated fixed-cohort CSVs. Its value is a robustness check: even in
non-aligned finite windows the boundary deviations are small relative to the
$c=1/2$ and $c=1$ comparison scales.

None of these measurements follows the distinguished pair at the head.
Transferring the head phase diagram still requires an arithmetic theorem that
controls coherent CRT-coupled placement together with persistent availability
and cross-layer dependence.

## 9. Limitations

The balanced companions track descendants of existing 2-gaps rather than a
coherent randomized sequence of integers. They do not model non-2 gaps, gap
mergers, or shared endpoint effects. Their adversary is stronger than the real
filter because it may select harmful copies separately for each parent. The
protective parent policy is also an oracle: it knows the current target and moves both
deletions elsewhere. Neither endpoint is a description of the real filter.

The adversarial/random window theorem assumes spatial uniformity. The adversarial/protective window
theorem instead assumes a quadratic protective supply $B(Q)$. Its head theorem
assumes an eligible protective-parent head lineage with availability bounded below.
None of these premises follows from the exact-two choice alone.

The exact-CRT-quota/random-location theorem preserves strike counts but discards
their deterministic arithmetic locations. Its recurrence conclusion requires
the cumulative quota conditions in §7.1, persistent head availability,
and cross-layer mixing. The exact local formula $A(p,q)$ does not establish
those premises merely by being exact.

The biased-quota theorem additionally assumes a group-exchangeable allocation
law and quadratic-order double hits on one endpoint pair. Its raw weight
$\beta_r$ is not the same as effective destruction skew $\kappa_r$: exact-quota
normalization changes lower-order terms. Their leading logarithmic coefficients
agree in the stated sparse-density regime, but a raw equality case must be
decided through $D_{\kappa}(Q)$ rather than by coefficient alone.

The use of expected population also has a strict boundary. An expectation
tending to infinity does not alone prove nonempty windows; the summable
empty-window bound supplies that step under uniform placement. Likewise, a
divergent head-event series does not alone prove infinite recurrence; adequate
cross-layer independence or mixing is required. Exact quotas, whole-filter
coins, block balance, delayed information, and noisy ranking create different
dependencies and cannot inherit one another's almost-sure conclusions merely
because they share the same marginal budget or destruction rate.

The empirical comparison in §8.1 is finite. Two datasets use a different
square window at each measured stage; the fixed-cohort dataset instead follows
all initial 2-gap starts in one $[Q,Q^2)$ window. The latter yields a coherent
window hazard, but its deviation from the exact full-cycle rate is a boundary
effect and the cohort is not the distinguished head pair. None of the data
therefore substitutes for persistent availability, cross-layer mixing, or an
arithmetic proof below the $c=1/2$ head frontier.

We have therefore proved a phase diagram for the defined companions. The
remaining question is whether the real sieve occupies one of these regimes.

## 10. Conclusion

Balanced 2-gap companions make global persistence deliberately uninformative:
every parent always leaves $r-2$ children, so the complete-period population
grows under protective, random, adversarial, and mixed selection alike. The
local distinction is carried by realized destruction relative to random, its
cumulative hazard, and allocation.

The proof begins with the exact global recurrence and then replaces population
counting by cumulative local hazard:

```math
\begin{aligned}
N_{k+1}&=(r_k-2)N_k,\\
w_r&=\frac{rf_r}{2},\\
D(Q)&=\sum_{r < Q}-\log(1-f_r),\\
P(Q)&=e^{-D(Q)}.
\end{aligned}
```

The main answer is that there is no maximum finite constant factor worse than
random. If $w_r=w < \infty$, local survival decays only as
$(\log Q)^{-2w}$; quadratic square-window supply still dominates, and the head
probability series still diverges. Under the stated spatial and
mixing premises, square windows are eventually nonempty and head 2-gaps recur
infinitely often for every fixed finite $w$.

The first nontrivial boundary occurs when worsening grows with the filter.
Under §7.1's cumulative quota/error conditions and the relevant spatial
premises, the neutral exact-quota companion recovers the random survival scale.
The biased exact-quota companion recovers the following general-hazard
frontiers when its realized effective skew follows the displayed schedule and
its placement, availability, and mixing premises hold:

```math
\begin{aligned}
w_r=1+c\log r,\quad c < 1
&\Longrightarrow
\text{eventual square-window occupancy},\\
w_r=1+c\log r,\quad c < \frac12
&\Longrightarrow
\text{infinitely recurring head 2-gaps, with mixing}.
\end{aligned}
```

The allocation theorem explains why a percentage alone cannot locate a
process in this phase diagram. Uniform, protective, and targeted allocation
can apply the same adversarial budget and produce different local damage. The
quantity that enters the theorem is therefore the realized local hazard, not
the policy label by itself.

The complete-period comparison is exact: every new filter destroys the
fraction $2/r$ of expanded cyclic 2-gaps, so its cumulative excess over the
neutral benchmark is zero. The two full-cycle diagrams expose the two parts of
this statement separately. The destruction diagram makes the per-filter
identity immediate; the survival diagram shows what compounding that identity
does and how strongly it separates from the $c=1$ schedule. Neither diagram is
weakened by being a direct rendering of the calculation: their value is that
the local equality and cumulative consequence can each be checked visually in
the representation best suited to it.

The finite square-window measurements then describe the remaining localization
question. Through head $1129$, the observed population
has mean ratio $0.967$ to the random expectation, and the measured one-step
window rates through filter $19{,}429$ are at or below $2/r$. Fixed cohorts for
$Q=17,101,251,503$ have signed effective coefficients between $-0.0353$ and
$0.00908$; these deviations are boundary effects around the exact cycle law.
The measurements remain far from the $c=1$ window-failure scale, but they do
not locate the distinguished head pair relative to the $c=1/2$ recurrence
frontier.

The real sieve question is now expressible as a cumulative comparison rather
than a vague claim of random or adversarial behavior: measure the total local
destruction $f_r$ generated by the CRT-coupled harmful indices, normalize it by
the random rate to obtain $w_r$, measure where the controllable damage lands
relative to the head, and compare the resulting cumulative hazard with the
companion thresholds above.

For a precise deterministic transfer criterion, let $I_Q\in\{0,1\}$ indicate
that the real sieve has a 2-gap at prime head $Q$. Let $\rho_Q>0$ be the
companion reference weight obtained from the below-frontier cumulative hazard
and the stated availability bound, and define

```math
R(X):=\sum_{\substack{Q\le X\\Q\text{ prime}}}\rho_Q.
```

Assume

```math
\begin{aligned}
R(X)&\longrightarrow\infty,
&&[\text{Divergent Reference Mass}]\\
\sum_{\substack{Q\le X\\Q\text{ prime}}}(I_Q-\rho_Q)
&=o(R(X)).
&&[\text{Deterministic Discrepancy Bound}]
\end{aligned}
```

Then

```math
\sum_{\substack{Q\le X\\Q\text{ prime}}}I_Q
=R(X)+o(R(X))
\longrightarrow\infty.
\qquad[\text{Q.E.D.}]
```

This discrepancy condition is the precise deterministic substitute for the
stochastic mixing premise. It is not proved here for the real CRT sieve. The
frontier is cumulative: the reference mass must diverge, rather than every
individual filter satisfying one pointwise bound. “Infinitely often” does not
mean that every sufficiently large head is a 2-gap. Proving this discrepancy
bound for the real CRT filter would prove infinitely many head 2-gaps and
therefore the twin-prime conjecture. We have identified the sufficient
frontier and the remaining transfer premise.

## 11. Future Work

The companion theorems reduce the real-sieve question to measurable arithmetic
inputs. The first direction is to estimate the real local hazard
$D_{\kappa}(Q)$ from CRT-coupled filter locations and compare it with the head
frontier without assigning hostile intent to individual filters. The second is
to replace the stochastic mixing premise with a deterministic decorrelation or
discrepancy theorem strong enough to transfer a divergent head-event sum to the
real sequence. The third is to test exact-quota, delayed, block-balanced, and
noisy-ranking companions on the same transitions, reporting both raw endpoint
preference and quota-normalized effective skew.

These directions are deliberately separate. A finite experiment can identify
which companion resembles the observed sieve, but it cannot establish the
infinite transfer theorem. Conversely, a discrepancy theorem must control
where the real CRT strikes land, not only how many strikes or global 2-gaps
exist.

## 12. References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). *Formal Verification of Sieve Sequence Stages and Their
Transitions*. [Local article](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md).

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Structural Properties and Open Boundaries of 2-Gaps in
Sieve Sequences*. [Local article](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md).

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Kochen, S. and Stone, C. (1964). [A note on the Borel--Cantelli lemma](
https://doi.org/10.1215/ijm/1256059668). *Illinois Journal of Mathematics*,
8(2), 248--251.

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Hardy, G. H. and Wright, E. M.; revised by Heath-Brown, D. R. and Silverman,
J. H. (2008). [*An Introduction to the Theory of Numbers*](
https://doi.org/10.1093/oso/9780199219858.001.0001), 6th edition. Oxford
University Press.

## Appendix A. Selected Companion Proof Records

The body develops every result in its mathematical context. This appendix
collects six core companion-process proof records with their premises and
conclusions; it is a selected reference, not a complete catalog of the body.

<a id="appendix-a1"></a>

### A.1 Global Persistence Is Independent of Allocation

Once the initial population is nonzero, this result is unconditional with
respect to allocation inside every balanced companion. Let
$N_k=|\mathcal G_k|$ be the complete-period 2-gap population before installing
prime $r_k$, with $N_0>0$. Every parent produces $r_k$ copies and loses exactly
two, regardless of where those two removals occur. Therefore

```math
\begin{aligned}
N_{k+1}
&=\sum_{g\in\mathcal G_k}(r_k-2)
&&[\text{Exactly Two Copies Removed Per Parent}]\\
&=(r_k-2)N_k.
&&[\text{Simplification}]
\end{aligned}
```

Iterating the recurrence gives

```math
\begin{aligned}
N_k
&=N_0\prod_{i < k}(r_i-2)
&&[\text{Iteration}]\\
&>0
&&[N_0>0;\ r_i\ge5]\\
&\longrightarrow\infty.
&&[\text{Every Factor Is At Least }3]
\end{aligned}
\qquad[\text{Q.E.D.}]
```

Thus allocation may eliminate 2-gaps from the head or a tracked window, but it
cannot exhaust the complete-period population while the exact-two removal rule
is preserved.

<a id="appendix-a2"></a>

### A.2 Cumulative Local-Hazard Law

Follow one local cohort through successive filters. Let $f_r$ be the fraction
destroyed at filter $r$, and assume $0\le f_r < 1$ throughout the tracked
chain. Define

```math
w_r:=\frac{rf_r}{2},
\qquad
D(Q):=\sum_{r < Q}-\log(1-f_r).
```

The cohort survives filter $r$ by the factor $1-f_r$. Multiplying these exact
one-step factors gives

```math
\begin{aligned}
P(Q)
&=\prod_{r < Q}(1-f_r)
&&[\text{Survive Every Filter}]\\
&=\exp\left(\sum_{r < Q}\log(1-f_r)\right)
&&[\text{Product To Sum}]\\
&=e^{-D(Q)}.
&&[\text{Definition Of }D(Q)]
\end{aligned}
\qquad[\text{Q.E.D.}]
```

For the random benchmark $w_r=1$, the prime harmonic sum gives

```math
\begin{aligned}
D_{\mathrm{random}}(Q)
&=\sum_{r < Q}-\log\left(1-\frac2r\right)\\
&=2\log\log Q+O(1),\\
P_{\mathrm{random}}(Q)
&\asymp\frac{C}{(\log Q)^2}.
\end{aligned}
```

This identity determines survival once the realized sequence $(f_r)$ is known.
It does not supply window abundance, head availability, or cross-layer mixing.
If one filter has $f_r=1$, the cohort becomes extinct immediately and its
cumulative hazard is infinite from that point.

<a id="appendix-a3"></a>

### A.3 Every Fixed Finite Worsening Factor Survives

Let $w\ge0$ be fixed and suppose $f_r=2w/r$ for all sufficiently large
filters. A finite prefix changes only the positive leading constant. Since the
quadratic Taylor remainder is summable over primes, Appendix A.2 gives

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

Assume first that a square window supplies
$B(Q)\asymp C_0Q^2$ eligible lineages and that their placement satisfies the
blind empty-window bound. Its expected surviving population is

```math
\lambda_w(Q)
\asymp
C_0\frac{Q^2}{(\log Q)^{2w}}
\longrightarrow\infty.
```

This polynomial growth makes the empty-window probabilities summable, so only
finitely many square windows are empty almost surely. For a distinguished head
whose baseline availability is bounded below,

```math
\Pr(H_Q)\asymp\frac{C_w}{(\log Q)^{2w}}.
```

The sum over prime heads diverges for every finite $w$. With adequate
cross-layer mixing, head 2-gaps therefore recur infinitely often almost surely.
Hence there is no finite constant-factor maximum worse than random.
$\blacksquare$

<a id="appendix-a4"></a>

### A.4 Logarithmically Growing Worsening Has Two Thresholds

Retain the supply, availability, placement, and mixing premises of Appendix
A.3, and set

```math
w_r=1+c\log r,
\qquad c\ge0.
```

Then $f_r=2/r+2c\log r/r$. Prime summation and the summable Taylor remainder
give

```math
\begin{aligned}
D_c(Q)
&=\sum_{r < Q}-\log(1-f_r)
&&[\text{Definition Of }D(Q)]\\
&=2\sum_{r < Q}\frac1r
+2c\sum_{r < Q}\frac{\log r}{r}+O(1)
&&[\text{Substitution; Summable Remainder}]\\
&=2\log\log Q+2c\log Q+O(1).
&&[\text{Prime-Sum Asymptotics}]
\end{aligned}
```

Consequently,

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

Thus $c < 1$ gives eventual square-window occupancy almost surely under the
blind-placement premise, while $c\ge1$ makes the expected population tend to
zero. For the head, the prime occurrence series has the same convergence
behavior as

```math
\int^\infty\frac{dx}{x^{2c}(\log x)^3}.
```

The integral diverges for $c < 1/2$ and converges for $c\ge1/2$. Therefore

```math
\begin{aligned}
c < 1
&\Longrightarrow
\text{eventual square-window occupancy almost surely},\\
c < \frac12
&\Longrightarrow
\text{infinitely recurring head 2-gaps almost surely, with mixing}.
\end{aligned}
\qquad[\text{Q.E.D.}]
```

The intermediate range $1/2\le c < 1$ preserves square windows but not
infinitely recurring head events. Irregular schedules must be evaluated by the
cumulative hazard $D(Q)$ rather than by isolated pointwise values.

<a id="appendix-a5"></a>

### A.5 Adversarial/Random Square-Window Boundary

At filter $r$, let a parent be adversarial with share $\alpha_r$ and random
otherwise. For one locally relevant lineage,

```math
1-f_r
=(1-\alpha_r)\left(1-\frac2r\right).
```

Define the cumulative adversarial-share hazard

```math
A(Q):=\sum_{r < Q}-\log(1-\alpha_r).
```

The random survival density contributes $(\log Q)^{-2}$, while the repeated
adversarial share contributes $e^{-A(Q)}$. If the square-safe window has
length $L_Q\asymp Q^2$ and surviving starts obey the spatial-uniformity model,
then

```math
\begin{aligned}
\lambda_Q^{\mathrm{mix}}
&=L_Q\delta_Q^{\mathrm{mix}}
&&[\text{Expected Uniform Occupancy}]\\
&\asymp
C\frac{Q^2}{(\log Q)^2}e^{-A(Q)}.
&&[\text{Cumulative Survival}]
\end{aligned}
```

Taking logarithms gives

```math
\log\lambda_Q^{\mathrm{mix}}
=2\log Q-2\log\log Q-A(Q)+O(1).
```

Therefore, for every fixed $\varepsilon>0$,

```math
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,
&&[\text{Subcritical Budget}]\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow0.
&&[\text{Supercritical Budget}]
\end{aligned}
```

At the exact boundary, the term $-2\log\log Q$ must be retained. Under uniform
placement,

```math
\Pr(X_Q=0)\le e^{-\lambda_Q^{\mathrm{mix}}}.
```

Hence the summability condition

```math
\sum_{Q\text{ prime}}e^{-\lambda_Q^{\mathrm{mix}}}<\infty
```

implies that only finitely many square windows are empty almost surely. A
convenient sufficient condition is
$\lambda_Q^{\mathrm{mix}}\ge(1+\varepsilon)\log Q$ for all sufficiently large
$Q$. $\blacksquare$

<a id="appendix-a6"></a>

### A.6 Local Survivor Allocation Range

Consider a target window shorter than the old period, so each parent
contributes at most one target child. Let $N$ be the number of parents, let
$R$ be the set of $L$ relevant parents, and let $\mathcal A$ be the size-$K$
set receiving adversarial treatment. The number of target children destroyed
and surviving are

```math
H=|\mathcal A\cap R|,
\qquad
S=L-H.
```

The intersection cannot exceed either set, and at most $N-L$ adversarial
labels can be placed outside $R$. Hence

```math
\begin{aligned}
H
&\le\min(K,L),
&&[\text{Intersection Upper Bound}]\\
H
&\ge\max(0,K-(N-L)).
&&[\text{Irrelevant-Parent Capacity}]
\end{aligned}
```

Substitution into $S=L-H$ gives the sharp survivor range

```math
\max(0,L-K)
\le S\le
\min(L,N-K).
```

Both endpoints are attainable. A target-aware allocator selects relevant
parents first, while a protective allocator assigns the adversarial labels to
irrelevant parents first:

```math
\begin{aligned}
S_{\mathrm{targeted}}&=\max(0,L-K),\\
S_{\mathrm{protective}}&=\min(L,N-K).
\end{aligned}
```

If $\mathcal A$ is instead a uniformly random size-$K$ subset, then

```math
H\sim\text{Hypergeometric}(N,L,K),
```

so

```math
\begin{aligned}
\mathbb E[H]&=\frac{KL}{N},\\
\mathbb E[S]&=L\left(1-\frac KN\right).
\end{aligned}
```

When $K\ge L$, uniform allocation clears the target with probability

```math
\Pr(S=0)
=\frac{\binom{N-L}{K-L}}{\binom NK}
=\frac{\binom KL}{\binom NL}.
```

Writing $\alpha=K/N$, the targeted endpoint becomes

```math
S_{\mathrm{targeted}}=0
\Longleftrightarrow
K\ge L
\Longleftrightarrow
\alpha\ge\frac LN.
\qquad[\text{Q.E.D.}]
```

At the head, $L=1$, so one correctly placed adversarial label destroys the
current candidate. If $L/N\longrightarrow0$ in a tracked window, every fixed
$\alpha>0$ eventually has enough capacity to clear that window. Appendix A.1
still applies: the targeted parents leave $r-2$ descendants outside the
window, so complete-period growth continues.
