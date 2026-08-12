# Relative Hazard And Allocation Phase Transitions In Balanced 2-Gap Companions

*How Much Worse Than Random Can A Local Filter Be While 2-Gaps Still Survive?*

**Status:** Draft mathematical analysis. The companion-process identities are
proved from their definitions. Safe-window and head conclusions are conditional
on the spatial-uniformity, optimistic-supply, head-availability, and cross-layer
mixing premises stated below. No new Scala/Stainless verification accompanies
the asymptotic results.

**Author:** Mata, T. H.  
Independent Researcher

## Abstract

The complete-period 2-gap population in a sieve sequence has a simple global
law: when filter prime $r$ is installed, every old 2-gap has $r$ copies and
exactly two are destroyed. Balanced companion processes preserve that law but
change how the two harmful copy indices are selected. The random sister chooses
them uniformly, the bad sister targets a prescribed local region, and the good
sister protects that region whenever the exact-two rule permits.

This article measures the realized fraction $f_r$ of a tracked local segment
destroyed at filter $r$. Random filtering has benchmark $2/r$, so
$w_r=rf_r/2$ is the factor by which the filter is worse than random and

```math
D(Q)=\sum_{r<Q}-\log(1-f_r)
```

is its cumulative local hazard. The tracked survival factor is exactly
$e^{-D(Q)}$. Under the stated quadratic-supply, availability, and mixing
premises, there is no largest finite constant multiple of random: every fixed
$w_r=w<\infty$ retains eventual square-window occupancy and infinitely many
head events. The first nontrivial transition occurs when $w_r$ grows like
$\log r$. For $w_r=1+c\log r$, square-window survival holds for $c<1$, while
head recurrence holds for $c<1/2$; at and beyond the respective boundaries the
corresponding local conclusion fails in the stipulated model.

Bad/random and bad/good mixtures are then studied as specializations. A fixed
absolute bad share $\alpha>0$ is fatal for the trivial reason that it makes
$w_r\sim\alpha r/2$, rather than keeping damage a fixed amount worse than the
shrinking random benchmark. Decaying absolute shares recover the previously
derived window and head transitions.

An exact-CRT-quota/random-location sister retains the chosen population's
exact number of filter shots but allocates them uniformly without replacement.
If its cumulative quota fractions match the CRT rate, its one-head survival is
again of order $(\log Q)^{-2}$. Persistent head availability and cross-layer
mixing then imply infinitely many head hits almost surely; the corresponding
blind-placement square-window model is eventually nonempty almost surely.
Exact shot counts alone do not imply either conclusion.

Biasing that exact quota toward 2-gap endpoints recovers the same frontier as
the general relative-hazard model. Every fixed finite effective preference
still gives infinitely many head hits almost surely with mixing. For effective
skew $\kappa_r=1+c\log r$, the head coefficient is $c=1/2$ and the square-window
coefficient is $c=1$. This agreement shows that the boundary comes from the
cumulative supply-versus-hazard balance rather than one particular random
companion definition.

Percentage is nevertheless only one axis. For $N$ parents, $L$ locally
relevant parents, and $K$ bad labels, the exact local survivor interval is
$\max(0,L-K)\le S\le\min(L,N-K)$. A perfectly informed bad sister can suppress
one head candidate with one label, whereas uniform allocation kills it only
with probability $K/N$. The article therefore separates bad-label budget from
targeting strength and proposes reproducible blind, delayed, and noisy-ranking
experiments.

These are results about constructed companion processes, not the real modular
filter. Their value is to isolate the missing question: how the real filter's
CRT-coupled harmful indices compare with the shrinking random destruction rate,
their cumulative local hazard, and their realized targeting score.

## 1. The Question That Needs Three Meanings Of Survival

Saying that “2-gaps survive” can mean three different things:

1. some 2-gap exists somewhere in the complete period at every layer;
2. a 2-gap occurs in each sufficiently large square-safe window; or
3. the distinguished head is a 2-gap infinitely often.

The first statement is global and purely combinatorial. The second is local
but benefits from a window whose length grows quadratically. The third concerns
one position and therefore has no window-size reserve. Mixing these meanings
hides the actual threshold.

The central question is therefore not what fixed percentage of behavior may be
called adversarial. It is how large the realized local destruction may be
relative to the random benchmark $2/r$, and how that damage is allocated near
the head.

The balanced companions are designed to separate them. They retain the real
sieve's exact number of descendants but replace the arithmetic rule selecting
which descendants die. This makes global survival identical in every companion
while allowing local behavior to range from maximally protective, through
position-blind random, to maximally hostile.

### 1.1 Evidence Status And Scope

This draft uses three levels of evidence:

- **Exact companion identity:** follows directly from the constructed process.
- **Conditional probability theorem:** mathematically proved after explicitly
  assuming spatial uniformity or cross-layer mixing.
- **Real-sieve comparison:** an open interpretation, not a theorem.

The asymptotic prime sums use standard prime-distribution inputs. They are not
encoded in Stainless. Consequently, the mathematical derivations below have
no third, Scala-verification representation yet. Each property is marked
**Draft — mathematically proved under its stated premises; Stainless
verification pending or outside the current verifier scope.**

## 2. Balanced Good, Random, And Adversarial Companions

Let $\mathcal G_k$ be the 2-gap descendants before installing prime $r$. Each
parent $g\in\mathcal G_k$ produces the indexed copies

```math
(g,0),(g,1),\ldots,(g,r-1).
```

Exactly two distinct indices are harmful. The balanced random companion draws
the harmful pair uniformly from the two-element subsets of $\mathbb Z/r\mathbb
Z$. The balanced adversarial companion instead spends its two deletions on
children in a chosen target region whenever possible.

The balanced good companion, defined fully in §13, spends both deletions away
from the target whenever possible.

In both cases every parent leaves exactly $r-2$ children. The companions
therefore randomize or optimize location, not population size.

The definitions and their precise limitations are maintained in
[Balanced Randomized 2-Gap Companion Process](
../../candidates/balanced-randomized-2-gap-companion-process.md) and
[Balanced Adversarial 2-Gap Companion Process](
../../candidates/balanced-adversarial-2-gap-companion-process.md). The real
modular pair is derived in [Copy-Index Filter Frequency](
../../properties/sieve-sequence/copy-index-filter-frequency.md).

## 3. Property I: Global Persistence Is Independent Of Adversariality

**Status:** **Mathematically proved by definition. Stainless verification is
not supplied in this draft.** The corresponding real-sieve complete-period
count has separate maintained source evidence.

No choice of the harmful pair can change the number of surviving descendants.
Random, adversarial, friendly, and mixed companions all have the same global
population. This matters because any later local extinction cannot be blamed
on exhausting the complete-period supply.

Let $N_k=|\mathcal G_k|$. Installing $r_k$ gives

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
&>0
&&[r_i\ge5]\\
&\longrightarrow\infty.
&&[\text{Every Factor Is At Least }3]
\end{aligned}
```

Thus

```math
\boxed{
\text{global 2-gap persistence holds for every adversarial schedule.}
}
\qquad[\text{Q.E.D.}]
```

The real-sieve analogue is documented in [Exact Global 2-Gap Count](
../../properties/sieve-sequence/exact-global-two-gap-count.md). This article
does not add a new `.holds` implementation for the companion recurrence.

## 4. Measuring Local Destruction Relative To Random

The primary quantity is the realized fraction of the target segment's 2-gaps
destroyed by filter $r$. If $L_r>0$ gaps are present before the filter and
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
\boxed{
w_r
:=\frac{f_r}{d_r}
=\frac{rf_r}{2}.
}
```

This is the meaningful adversariality scale because the benchmark itself
shrinks as filters grow:

```math
\begin{aligned}
w_r=0
&\Longleftrightarrow f_r=0
&&[\text{Good Endpoint}],\\
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

### 4.1 Absolute Bad/Random Share As A Specialization

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

Thus a fixed absolute share $\alpha_r=\alpha>0$ does not represent a fixed
amount worse than random. It makes $w_r$ grow linearly like $\alpha r/2$.
This is why the fixed-share model is asymptotically fatal for an essentially
trivial reason; the nontrivial question is how rapidly $w_r$ itself may grow.

## 5. Property II: The General Cumulative Local-Hazard Law

**Status:** **Mathematically proved for a tracked companion lineage. Stainless
verification pending.** Spatial window and head conclusions require the
additional abundance and mixing premises introduced later.

The filter's local effect is determined by the total realized destruction
fraction $f_r$, regardless of whether that fraction arose from random choice,
bad labels, targeting, or another allocation mechanism. The one-step survival
factor is

```math
s_r=1-f_r=1-\frac{2w_r}{r}.
```

Assume $f_r<1$ for every filter in the tracked chain. Define the cumulative
local hazard

```math
\boxed{
D(Q)
:=\sum_{r < Q}-\log(1-f_r)
=\sum_{r < Q}-\log\left(1-\frac{2w_r}{r}\right).
}
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
```

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

The absolute bad/random mixture from §4.1 is recovered because

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
D_{\mathrm{bad/random}}(Q)
&=D_{\mathrm{random}}(Q)+A(Q),\\
P_{\mathrm{bad/random}}(Q)
&\asymp\frac{C}{(\log Q)^2}e^{-A(Q)}.
\end{aligned}
```

Thus the earlier $A(Q)$ is an excess hazard created by one particular policy
mixture. The primary quantity is $D(Q)$, which also applies when no policy label
$\alpha_r$ exists.

If one filter has $f_r=1$, local extinction is immediate and the cumulative
hazard is infinite from that point.

No Scala/Stainless theorem currently encodes this stochastic product or its
analytic asymptotics.

### 5.1 Property III: Every Fixed Finite Worsening Factor Survives The Model

**Status:** **Conditional mathematical theorem. Stainless verification
pending.** Square-window survival assumes quadratic eligible supply and blind
placement; head recurrence additionally assumes availability bounded below and
adequate cross-layer mixing.

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
\boxed{
P_w(Q)\asymp\frac{C_w}{(\log Q)^{2w}}.
}
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
\boxed{
\text{there is no finite constant-factor maximum worse than random.}
}
\qquad[\text{Q.E.D.}]
```

A filter that is twice, ten times, or one million times worse than the random
rate still lies in the same asymptotic survival class once $r$ is sufficiently
large. The nontrivial transition begins only when $w_r$ grows with $r$.

No Scala/Stainless theorem currently encodes the fixed-factor asymptotic or its
conditional probability consequences.

### 5.2 Property IV: Logarithmically Growing Worsening Has Two Thresholds

**Status:** **Conditional mathematical theorem. Stainless verification
pending.** It uses the same quadratic-supply, availability, and mixing premises
as §5.1.

To measure a filter that becomes progressively worse than random while still
respecting the shrinking benchmark, set

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
&=2\sum_{r<Q}\frac1r
&\quad+2c\sum_{r<Q}\frac{\log r}{r}+O(1)
&&[\text{Substitution; Summable Remainder}]\\
&=2\log\log Q+2c\log Q+O(1).
&&[\text{Prime-Sum Asymptotics}]
\end{aligned}
```

Hence

```math
\boxed{
P_c(Q)
\asymp
\frac{C_c}{Q^{2c}(\log Q)^2}.
}
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
\boxed{
\begin{aligned}
c < 1
&\Longrightarrow
\text{eventually nonempty square windows almost surely},\\
c\ge1
&\Longrightarrow
\text{square-window expectation tends to zero}.
\end{aligned}
}
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
\boxed{
\begin{aligned}
c < \frac12
&\Longrightarrow
\text{infinitely many head events almost surely, with mixing},\\
c\ge\frac12
&\Longrightarrow
\text{only finitely many head events almost surely}.
\end{aligned}
}
```

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

These are cumulative asymptotic regimes, not pointwise allowances that reset
at each filter. Irregular schedules must be evaluated through $D(Q)$.

No Scala/Stainless theorem currently encodes these relative-factor phase
boundaries.

### 5.3 Relative-To-Random Phase Diagram

The answer is not a maximum fixed percentage. It is a growth-rate boundary for
the realized local damage relative to the random benchmark.

| Realized relative factor | Total local destruction | Square windows | Head 2-gaps |
|---|---:|---|---|
| $w_r=1$ | $2/r$ | Eventually nonempty almost surely | Infinitely often with mixing |
| Any fixed finite $w_r=w$ | $2w/r$ | Eventually nonempty almost surely | Infinitely often with mixing |
| $w_r=1+c\log r$, $0\le c<1/2$ | $2/r+2c\log r/r$ | Eventually nonempty almost surely | Infinitely often with mixing |
| $w_r=1+c\log r$, $1/2\le c<1$ | $2/r+2c\log r/r$ | Eventually nonempty almost surely | Only finitely often almost surely |
| $w_r=1+c\log r$, $c\ge1$ | $2/r+2c\log r/r$ | Expected population tends to zero | Only finitely often almost surely |
| $f_r=1$ at any tracked step | $1$ | Immediate local extinction | Immediate local extinction |

Consequently, there is **no largest finite constant multiple of random**. For
square-window survival, the filter may become almost $\log r$ times worse than
random; for infinitely recurring head 2-gaps, it may become almost
$\tfrac12\log r$ times worse. In total local-destruction terms, the robust
sufficient regimes are respectively

```math
f_r<(2-\varepsilon)\frac{\log r}{r}
\qquad\text{and}\qquad
f_r<(1-\varepsilon)\frac{\log r}{r}.
```

These conclusions concern damage realized inside the tracked segment. A small
global bad budget can still cause $f_r=1$ if it is allocated with enough target
information; the allocation theorem later in the article isolates that second
axis.

## 6. Property V: The Absolute-Share Bad/Random Square-Window Boundary

**Status:** **Conditional mathematical theorem. Stainless verification
pending.** Assume the mixed surviving starts obey the spatial-uniformity model
used by the balanced random companion.

Let the square-safe window have length

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

Therefore, for every fixed $\varepsilon>0$,

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
\sum_{Q\text{ prime}}e^{-\lambda_Q^{\mathrm{mix}}}<\infty,
```

the first Borel-Cantelli lemma gives only finitely many empty square windows
almost surely. A convenient sufficient condition is

```math
\lambda_Q^{\mathrm{mix}}\ge(1+\varepsilon)\log Q
```

for all sufficiently large $Q$. This is stronger than merely requiring
$\lambda_Q^{\mathrm{mix}}\to\infty$ and prevents a slow divergent expectation
from being mistaken for an eventual-survival theorem.

The safe-window conclusion is not claimed for the real sieve. It is a theorem
inside the spatially uniform mixed companion.

## 7. Why A Constant Absolute Bad Share Is Trivially Fatal Locally

**Status:** **Conditional mathematical consequence of §6. Stainless
verification pending.**

Suppose one fixed share $0 < \alpha < 1$ is adversarial at every filter. Then

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
\boxed{
\text{every fixed positive per-filter adversarial share is locally fatal}
}
```

for the repeated-mixture projection, even though the complete-period
population continues to grow without bound.

This is different from applying one adversarial dilution after all random
filters have finished. A one-time dilution multiplies the final count by
$1-\alpha$ once; the repeated model multiplies it once per prime. Confusing
these two experiments reverses the asymptotic conclusion.

## 8. Two Absolute-Share Decay Specializations

The useful question is therefore not “what fixed percentage is tolerable?”
The useful question is how quickly $\alpha_r$ must decay.

### 8.1 Reciprocal Decay: $\alpha_r\sim c/r$

For fixed $c>0$ and sufficiently large primes,

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

### 8.2 Logarithmic-Over-Linear Decay: $\alpha_r\sim c\log r/r$

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
\boxed{
\begin{aligned}
c < 2&\Longrightarrow\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,\\
c\ge 2&\Longrightarrow\lambda_Q^{\mathrm{mix}}\longrightarrow0.
\end{aligned}
}
```

For $c < 2$, the divergence is polynomial, so the empty-window bound is
summable and every sufficiently large square window is nonempty almost surely
under the spatial-uniformity premise.

## 9. Property VI: The Absolute-Share Bad/Random Head Boundary

**Status:** **Conditional mathematical theorem. Stainless verification
pending.** Assume uniform head marginals. Almost-sure infinite recurrence also
requires independence or a sufficiently strong weak-mixing substitute.

A head is one location, so there is no factor $Q^2$. Its mixed occurrence
probability is

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
\boxed{
\begin{aligned}
c < 1
&\Longrightarrow
\sum_{Q\text{ prime}}\Pr(H_Q)=\infty,\\
c\ge 1
&\Longrightarrow
\sum_{Q\text{ prime}}\Pr(H_Q)<\infty.
\end{aligned}
}
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
model, while head recurrence fails almost surely in the mixed projection.

## 10. Absolute-Share Bad/Random Phase Diagram

For the representative schedule $\alpha_r\sim c\log r/r$, the companion
separates into three regimes:

| Adversarial scale | Global 2-gaps | Square-safe windows | Head recurrence |
|---|---:|---:|---:|
| $0\le c < 1$ | Persist and grow | Eventually nonempty almost surely | Infinite almost surely, with mixing |
| $1\le c < 2$ | Persist and grow | Eventually nonempty almost surely | Only finitely many almost surely |
| $c\ge 2$ | Persist and grow | Mixed expectation tends to zero | Only finitely many almost surely |
| Fixed $\alpha > 0$ | Persist and grow | Mixed expectation tends to zero | Only finitely many almost surely |

The table's last two columns are statements inside the stipulated spatial
model. The global column is unconditional for every balanced companion.

### 10.1 Why A Fixed Absolute Percentage Gives The Wrong Maximum

Within position-blind repeated mixtures, percentages that do not change with
the filter prime have a blunt but secondary answer. If the same absolute bad
share $\alpha$ is applied at every filter, every $\alpha>0$ is eventually fatal
to the local mixed baseline. In that restricted normalization,

```math
\boxed{
\text{maximum sustainable fixed absolute bad share}=0\%.
}
```

This is not the meaningful answer to “how much worse than random can the
filter be?” Random destruction itself shrinks as $2/r$, while fixed
$\alpha>0$ adds a positive floor and makes the relative factor
$w_r=1+(r-2)\alpha/2$ diverge linearly. The primary answer from §5.3 is instead
that every fixed finite $w$ survives the stipulated model, with the first
transition only when $w_r$ grows on the order of $\log r$.

The zero-percent statement concerns safe-window and head survival under this
fixed absolute-share policy. It does not concern the global population, which
survives even under $100\%$ adversarial selection.

Nonzero adversariality remains supportable when its share decreases with $r$.
For a fixed margin $\varepsilon>0$, the representative sufficient schedules
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
other filters. The authoritative quantities remain

```math
A(Q)=\sum_{r < Q}-\log(1-\alpha_r)
```

for square windows and

```math
\sum_{Q\text{ prime}}
\frac{e^{-A(Q)}}{(\log Q)^2}
```

for head recurrence.

## 11. What “Percentage Adversarial” Must Specify

There is no unique mixture until its sampling unit is stated.

### Parent-Level Mixture

Each parent independently uses adversarial selection with probability
$\alpha_r$. This gives the cleanest branching interpretation and the marginal
factor derived above.

### Whole-Filter Mixture

The entire filter is adversarial with probability $\alpha_r$. A single
adversarial filter may coordinate its attack across every local parent. The
one-lineage marginal factor is unchanged when the whole-filter choices remain
independent across filters, but dependencies between parents become much
stronger, so the spatial and almost-sure positive results require a separate
mixing proof.

### One-Time Final Mixture

After ordinary random filtering, one final adversarial operation removes an
$\alpha$ share. This produces only the factor $1-\alpha$ and does not describe
repeated mixed filtering. It has no cumulative phase transition and must not be
used to answer the per-filter question.

The calculations in §§5--10 concern repeated per-filter marginal shares. Their
expectations apply to either of the first two interpretations, but their
almost-sure conclusions require the spatial and dependence premises stated for
each theorem.

## 12. Property VII: Allocation Is A Second Independent Axis

**Status:** **Mathematically proved for the balanced companion. Stainless
verification pending.** The proof assumes that every parent has at most one
child in the target region, the post-crossover geometry established for
windows shorter than the old period.

An adversarial percentage says how many parents receive bad treatment, but it
does not say which parents they are. That missing choice can move the local
outcome across its entire feasible range. Consequently, no percentage-only
threshold applies simultaneously to a position-blind mixture and a perfectly
targeted adversary.

At one filter, let

- $N$ be the total number of parents;
- $R$ be the set of parents with a child in target region $W$;
- $L=|R|$;
- $B$ be the set of parents assigned bad behavior; and
- $K=|B|$.

Because each relevant parent contributes at most one target child, the number
of target children destroyed is

```math
H=|B\cap R|,
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
\boxed{
\max(0,L-K)
\le S\le
\min(L,N-K).
}
```

Both endpoints are attainable. A target-aware bad sister selects members of
$R$ first and gives

```math
S_{\mathrm{targeted}}=\max(0,L-K).
```

An optimistic allocator spends bad labels on the $N-L$ irrelevant parents
first and gives

```math
S_{\mathrm{optimistic}}=\min(L,N-K).
```

If $B$ is instead a uniformly random size-$K$ subset of the $N$ parents, then

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

Thus

```math
\boxed{
\text{bad percentage does not determine local survival without an allocation law.}
}
\qquad[\text{Q.E.D.}]
```

The head makes the distinction extreme. There $L=1$. A target-aware
adversary kills the unique head candidate whenever $K\ge1$, requiring only
the global share $1/N$. Uniform allocation kills it with probability $K/N$,
while optimistic allocation preserves it whenever $K\le N-1$.

The window geometry and targeted endpoint are maintained in [Balanced
Adversarial 2-Gap Companion Process](
../../candidates/balanced-adversarial-2-gap-companion-process.md). No
Scala/Stainless theorem currently encodes the finite-set allocation bounds.

## 13. The Balanced Good Sister

The good sister is the local opposite of the bad sister. It preserves a
parent's target child whenever the exact-two deletion rule permits that choice.
It does not create extra descendants and cannot change the global recurrence.

For parent $g$, let $T_g(W)$ be the indices of its children in target region
$W$. In the post-crossover regime,

```math
|T_g(W)|\le1.
```

Because $r\ge5$, at least $r-1\ge4$ child indices lie outside $T_g(W)$. The
good sister may therefore choose a harmful pair

```math
K_{g,r}^{\mathrm{good}}
\subseteq
(\mathbb Z/r\mathbb Z)\setminus T_g(W),
\qquad
|K_{g,r}^{\mathrm{good}}|=2.
```

The bad sister instead chooses a pair containing the target index whenever
$T_g(W)$ is nonempty. Both policies remove exactly two children, so both leave
$r-2$ descendants globally. Their only difference is local placement:

```math
\begin{aligned}
T_g(W)\ne\varnothing
&\Longrightarrow
\text{good preserves the target child},\\
T_g(W)\ne\varnothing
&\Longrightarrow
\text{bad destroys the target child}.
\end{aligned}
```

The good sister is an oracle comparison, not a plausible random filter. It is
allowed to see the chosen target and place its two deletions elsewhere. Its
purpose is to define the optimistic endpoint of the same balanced family in
which the adversarial sister defines the pessimistic endpoint.

No Scala/Stainless implementation currently represents this target-aware
companion policy.

## 14. Property VIII: Fixed-Cohort Survival Under Bad/Good Mixing

**Status:** **Mathematically proved for independent, position-blind parent
labels. Stainless verification pending.** This property does not apply when
the bad sister chooses parents after observing their positions.

Consider $N_0$ locally relevant lineages followed through a fixed finite chain
of filters. At filter $r$, every surviving lineage independently receives bad
behavior with probability $\alpha_r$ and good behavior with probability
$1-\alpha_r$. A bad label destroys its target child; a good label preserves it.

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
\boxed{
\begin{aligned}
\mathbb E[X_Q]&=N_0e^{-A(Q)},\\
\Pr(X_Q>0)&=1-\left(1-e^{-A(Q)}\right)^{N_0}.
\end{aligned}
}
```

For one filter this reduces to

```math
X_{k+1}\mid X_k=N
\sim
\text{Binomial}(N,1-\alpha_r),
```

with immediate wipeout probability $\alpha_r^N$. Population redundancy is
therefore useful under blind parent assignment: the bad sister must happen to
receive every relevant parent in the same transition to erase the cohort.

If $\alpha_r=\alpha>0$ is constant, then

```math
P_Q=(1-\alpha)^{\pi(Q)+O(1)}\longrightarrow0.
```

Every one of the finite $N_0$ lineages eventually receives a bad label with
probability one. Hence the fixed cohort becomes extinct almost surely even
though every lineage continues to have $r-2$ descendants elsewhere in the
complete period.

Compared with the bad/random mixture, the bad/good law removes the random
factor $1-2/r$:

```math
\begin{aligned}
s_r^{\mathrm{bad/random}}
&=(1-\alpha_r)\left(1-\frac2r\right),\\
s_r^{\mathrm{bad/good}}
&=1-\alpha_r.
\end{aligned}
```

This improvement is local. It does not overcome a fixed positive adversarial
share repeated through infinitely many filters.

No Scala/Stainless theorem currently represents the probability law above.

## 15. Property IX: Growing Square Windows Under Bad/Good Mixing

**Status:** **Conditional mathematical theorem. Stainless verification
pending.** Assume that the fully good companion supplies
$B(Q)\asymp C_0Q^2$ eligible target lineages in the square window and that bad
labels are independent and position-blind across those lineages and filters.

The good sister removes the balanced-random density penalty because it protects
every eligible target child. The only remaining local loss is the cumulative
bad-label probability $e^{-A(Q)}$.

From §14, each of the $B(Q)$ eligible lineages survives with probability
$e^{-A(Q)}$. Therefore

```math
X_Q^{\mathrm{bad/good}}
\sim
\text{Binomial}\left(B(Q),e^{-A(Q)}\right)
```

and

```math
\begin{aligned}
\lambda_Q^{\mathrm{bad/good}}
&:=\mathbb E[X_Q^{\mathrm{bad/good}}]\\
&=B(Q)e^{-A(Q)}\\
&\asymp C_0Q^2e^{-A(Q)}.
\end{aligned}
```

The empty-window probability satisfies

```math
\begin{aligned}
\Pr(X_Q^{\mathrm{bad/good}}=0)
&=\left(1-e^{-A(Q)}\right)^{B(Q)}\\
&\le e^{-\lambda_Q^{\mathrm{bad/good}}}.
&&[1-x\le e^{-x}]
\end{aligned}
```

Taking logarithms gives the phase boundary

```math
\log\lambda_Q^{\mathrm{bad/good}}
=2\log Q-A(Q)+O(1).
```

Hence, for every fixed $\varepsilon>0$,

```math
\boxed{
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{bad/good}}\longrightarrow\infty,\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{bad/good}}\longrightarrow0.
\end{aligned}
}
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
\lambda_Q^{\mathrm{bad/good}}\asymp C_0Q^{2-c}.
```

Thus

```math
\boxed{
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
}
```

The leading threshold $c=2$ matches the bad/random companion, but the boundary
term differs:

```math
\begin{aligned}
\lambda_Q^{\mathrm{bad/random}}
&\asymp C\frac{Q^{2-c}}{(\log Q)^2},\\
\lambda_Q^{\mathrm{bad/good}}
&\asymp C_0Q^{2-c}.
\end{aligned}
```

At $c=2$, the random mixture tends to zero while the good mixture retains only
an order-one expectation, still insufficient for eventual almost-sure
nonemptiness.

No Scala/Stainless theorem currently represents the optimistic-supply premise
or the probability bounds above.

## 16. Property X: Head Recurrence Under Bad/Good Mixing

**Status:** **Conditional mathematical theorem. Stainless verification
pending.** Assume the fully good companion has an eligible head lineage at
prime stage $Q$ with probability $b_Q$, where $b_Q\ge b>0$ for all sufficiently
large $Q$. Infinite recurrence additionally requires independence or adequate
weak mixing between head events.

The good sister can preserve an eligible head lineage, but it cannot create one
when none is available. The factor $b_Q$ records that distinction. Conditional
on availability, the lineage must avoid every bad label in its chain, giving

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
$c>1$. Hence

```math
\boxed{
\begin{aligned}
c\le1
&\Longrightarrow
\text{infinitely many head events almost surely, with mixing},\\
c>1
&\Longrightarrow
\text{only finitely many head events almost surely}.
\end{aligned}
}
```

The boundary differs from bad/random mixing. There the balanced-random head
density contributes $(\log Q)^{-2}$:

```math
\begin{aligned}
\Pr(H_Q^{\mathrm{bad/random}})
&\asymp\frac1{Q^c(\log Q)^2},\\
\Pr(H_Q^{\mathrm{bad/good}})
&\asymp\frac{b_Q}{Q^c}.
\end{aligned}
```

At $c=1$, the bad/random prime series converges, while the bad/good series
diverges. Thus the good sister changes the inclusion of the critical boundary,
even though both mixtures have the same leading threshold scale.

For the gentler schedule $\alpha_r\sim c/r$, the occurrence probability is
comparable to $(\log Q)^{-c}$ and the sum over prime heads diverges for every
fixed finite $c$.

No Scala/Stainless theorem currently represents the optimistic head-availability
or mixing premises.

### 16.1 Bad/Random And Bad/Good Phase Comparison

Under their respective spatial premises, the two position-blind mixtures have
the following asymptotic behavior:

| Adversarial schedule | Bad/random square window | Bad/good square window | Bad/random head | Bad/good head |
|---|---:|---:|---:|---:|
| Fixed $\alpha>0$ | Expectation tends to zero | Expectation tends to zero | Finitely many almost surely | Finitely many almost surely |
| $\alpha_r\sim c/r$ | Eventually nonempty almost surely | Eventually nonempty almost surely | Infinite with mixing | Infinite with mixing |
| $\alpha_r\sim c\log r/r$, $c < 1$ | Eventually nonempty almost surely | Eventually nonempty almost surely | Infinite with mixing | Infinite with mixing |
| $\alpha_r\sim c\log r/r$, $c=1$ | Eventually nonempty almost surely | Eventually nonempty almost surely | Finitely many almost surely | Infinite with mixing |
| $\alpha_r\sim c\log r/r$, $1 < c < 2$ | Eventually nonempty almost surely | Eventually nonempty almost surely | Finitely many almost surely | Finitely many almost surely |
| $\alpha_r\sim c\log r/r$, $c=2$ | Expectation tends to zero | Order-one expectation | Finitely many almost surely | Finitely many almost surely |
| $\alpha_r\sim c\log r/r$, $c>2$ | Expectation tends to zero | Expectation tends to zero | Finitely many almost surely | Finitely many almost surely |

The good sister removes the balanced-random $(\log Q)^{-2}$ loss. This does
not change the leading square-window threshold $c=2$, because the quadratic
window dominates logarithmic factors away from the boundary. It does change
the boundary behavior and, most visibly, includes $c=1$ on the recurrent side
of the head transition.

Every entry assumes position-blind bad labels. A target-aware allocator is
governed by §12 instead and may erase the head with one correctly placed bad
label regardless of this table's percentage regime.

## 17. Position-Blind And Limited-Targeting Assignment Mechanisms

The policy choice belongs to a parent, not to each child independently. A child
level coin could destroy an arbitrary number of one parent's copies and would
break the exact-two reproduction law. Every mechanism below first assigns a
good or bad policy to each parent; that policy then chooses exactly two harmful
copy indices.

### 17.1 Independent Parent Coin

Each parent independently receives a bad label with probability $\alpha_r$.
This is the simplest stochastic model and leads directly to the binomial law
in §14. Its realized bad percentage fluctuates around $\alpha_r$.

The label must be drawn without using the parent's coordinate, copy index, or
distance from the head. Otherwise the coin is only nominally random and may
encode hidden targeting.

### 17.2 Exact-Quota Uniform Shuffle

Uniformly shuffle all $N$ parent identities, label exactly

```math
K=\lfloor\alpha_rN\rfloor
```

parents bad, and label the rest good. Positions are revealed only after the
assignment. This guarantees the requested realized percentage and gives the
hypergeometric local law from §12.

This is the recommended primary null model: it is position-blind, has an exact
budget, preserves global reproduction, and admits exact finite-population
probability calculations.

### 17.3 Shuffled Alternation And Round-Robin Labels

For a half-and-half experiment, shuffle the parents and assign

```math
G,B,G,B,\ldots
```

through the shuffled order. A new shuffle and reversed starting label may be
used at the next filter. More general periodic words implement other rational
shares.

Alternation balances label counts, but it does not undo past damage. A target
child killed on a bad round is not restored when the same lineage later
receives a good label. Reusing an unshuffled ordering is also dangerous because
lineage parity or spatial order may lock to the label pattern.

### 17.4 Block-Balanced Shuffle

Partition the ordered parents into blocks of size $b$ and assign exactly
$\lfloor\alpha_rb\rfloor$ bad labels uniformly inside each block. This prevents
all bad assignments from clustering in one long positional region while
retaining randomness inside each block.

Block balance is not a neutral model of unrestricted randomness. It is a
controlled anti-clustering model and should be reported as such. Varying $b$
tests how much the outcome depends on the spatial scale at which balance is
enforced.

### 17.5 Random Cyclic Mask

Choose a fixed balanced word such as

```math
G,G,G,B,G,G,G,B,\ldots
```

and apply a uniformly random cyclic offset at each filter. This is inexpensive,
reproducible, and keeps short-range bad spacing controlled. Different word
lengths and offsets are necessary because one periodic mask could resonate with
the sieve's own periodic geometry.

### 17.6 Position-Blind Hash Assignment

Let a seeded hash of lineage identity and filter prime determine the label:

```math
B_g
=
\mathbf 1\{h(\text{lineage}(g),r,\text{seed})<\alpha_r\}.
```

The hash must exclude current head distance and other positional observables.
This model behaves like a parent coin while making every run exactly
reproducible from its seed.

### 17.7 Delayed Adversary

Allow the bad sister to inspect the previous layer but not the current layer.
It ranks parents using stale head distances and spends its exact budget on the
previously closest lineages. This tests whether proximity persists strongly
enough across one transition to make partial information dangerous.

The delayed adversary lies between blind assignment and a current-position
oracle. Its effectiveness is itself evidence about cross-layer positional
memory.

### 17.8 Noisy Adversarial Ranking

Let $d_g$ be a normalized current distance from parent $g$'s closest child to
the target. Assign bad labels without replacement using weights

```math
w_g(\beta)=e^{-\beta d_g}.
```

The parameter $\beta$ controls targeting intelligence:

```math
\begin{aligned}
\beta=0
&\Longrightarrow\text{uniform exact-quota shuffle},\\
0<\beta<\infty
&\Longrightarrow\text{partial preference for near-head parents},\\
\beta\longrightarrow\infty
&\Longrightarrow\text{closest-parent-first adversary}.
\end{aligned}
```

This family turns the qualitative phrase “somewhat adversarial” into two
separate quantities: the budget $\alpha_r$ and the information strength
$\beta$. It is the most useful stress-test family once the position-blind null
model is established.

### 17.9 Recommended Order Of Use

| Mechanism | Realized bad share | Current positional knowledge | Primary purpose |
|---|---:|---:|---|
| Independent parent coin | Random around $\alpha_r$ | None | Simplest probability law |
| Exact-quota shuffle | Exactly $K/N$ | None | Canonical null model |
| Block-balanced shuffle | Locally constrained | None | Anti-clustering sensitivity |
| Delayed adversary | Exactly $K/N$ | Previous layer | Positional-memory test |
| Noisy ranking | Exactly $K/N$ | Tunable | Targeting phase transition |
| Perfect adversary | Exactly $K/N$ | Complete | Worst-case endpoint |

The exact-quota shuffle should be the baseline. Other mechanisms answer
different questions and should not be pooled into one undifferentiated
“percentage adversarial” curve.

## 18. A Two-Axis Phase Diagram And Experimental Program

The primary observed state space has two coordinates:

```math
(w_r,\theta_r)
=
(\text{damage relative to random},\text{realized targeting strength}).
```

The first says how much total damage the tracked segment actually received.
The second says how concentrated the controllable bad-label budget was relative
to the locally relevant parents. The scheduled share $\alpha_r=K_r/N_r$
remains an experimental input, but it is not itself the local damage.

### 18.1 Normalized Targeting Strength

For one nondegenerate transition, retain the notation from §12 and define

```math
\begin{aligned}
H_{\min}&=\max(0,K-(N-L)),\\
H_0&=\frac{KL}{N},\\
H_{\max}&=\min(K,L).
\end{aligned}
```

These are the optimistic minimum, uniform-random mean, and adversarial maximum
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
&&[\text{Optimistic Endpoint}],\\
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

### 18.2 Realized Local Hazard

Let $T_r$ be the total number of locally relevant target children destroyed by
the complete filter, including both random-baseline and bad-label destruction.
Define

```math
f_r^{\mathrm{local}}=\frac{T_r}{L_r},
\qquad
w_r^{\mathrm{local}}=\frac{rT_r}{2L_r},
\qquad L_r>0.
```

In the pure bad/good assignment, a bad label destroys its target and a good
label preserves it, so $T_r=H_r$. In the bad/random assignment, $T_r$ also
contains the random branch's $2/r$ baseline. For blind bad/random labels,

```math
\mathbb E[f_r^{\mathrm{local}}]
\approx
\alpha_r+(1-\alpha_r)\frac2r.
```

A perfect adversary can make $f_r^{\mathrm{local}}=1$ even when the global
budget $\alpha_r=K_r/N_r$ is tiny, provided its budget and information cover
the local target.

The cumulative local hazard from §5 is

```math
D(Q)
=
\sum_{r < Q}-\log\left(1-f_r^{\mathrm{local}}\right),
```

whenever every factor is positive. If one transition has
$f_r^{\mathrm{local}}=1$, the tracked local cohort is extinct and $D(Q)$ is
effectively infinite from that point. This diagnostic generalizes $A(Q)$ and
includes the random baseline rather than counting only the excess bad-label
loss. The separation between scheduled $\alpha_r$, realized
$w_r^{\mathrm{local}}$, and targeting score $\theta_r$ measures respectively
policy budget, total relative damage, and the value of positional information.

When the locally relevant population is redefined at every transition rather
than following one cohort, $D(Q)$ is only a cumulative diagnostic; it is not an
exact survival exponent for a single population.

The phase calculations earlier in the article can therefore be read with three
levels of input:

- $A(Q)$ is the scheduled budget under the blind-allocation model;
- $D(Q)$ is the realized total local damage after allocation; and
- $\theta_r$ records how strongly the controllable budget targeted the segment.

Only the first has a closed form from $\alpha_r$ alone. The general survival
law and relative phase diagram use $D(Q)$ or $w_r^{\mathrm{local}}$ directly.

### 18.3 Experiment Grid

For each filter schedule, run the following allocation mechanisms over many
seeds:

| Budget schedule | Uniform quota | Block balanced | Delayed adversary | Noisy ranking | Perfect endpoints |
|---|---:|---:|---:|---:|---:|
| Exact local CRT quota $J_r$ | Canonical | Sensitivity test | Sensitivity test | Several $\beta$ | Comparison only |
| Exact quota with endpoint weight $\beta_r$ | Neutral at $1$ | Several weights | Delayed weights | Dense grid near effective $c=1/2,1$ | Perfect-target limit |
| Target fixed $w$ | Yes | Yes | Yes | Several $\beta$ | Good and bad |
| Target $w_r=1+c\log r$ | Yes | Yes | Yes | Dense grid near $c=1/2,1$ | Good and bad |
| Constant $\alpha$ | Yes | Yes | Yes | Several $\beta$ | Good and bad |
| $\alpha_r=c/r$ | Yes | Yes | Yes | Several $\beta$ | Good and bad |
| $\alpha_r=c\log r/r$ | Yes | Yes | Yes | Dense grid near $c=1,2$ | Good and bad |

Relative-factor schedules should be implemented by calibrating the available
bad-label budget and then recording the realized $w_r$; exact realization may
be impossible for small finite populations. The $1+c\log r$ family should
sample both sides of $c=1/2$ and $c=1$. The absolute-share $c\log r/r$ family
should sample both sides of its derived $c=1$ and $c=2$ boundaries. No run
should extend a fixed window past its physical certification boundary.

### 18.4 Required Per-Transition Measurements

Each row should record at least:

- filter prime $r$ and target head $Q$;
- total parents $N_r$ and locally relevant parents $L_r$;
- exact CRT shot quota $J_r$, eligible-value population $N_r^{\mathrm{shot}}$,
  and quota fraction $u_r=J_r/N_r^{\mathrm{shot}}$;
- endpoint fraction $x_r$, raw preference $\beta_r$, and effective skew
  $\kappa_r^{\mathrm{eff}}$ for biased-quota runs;
- bad budget $K_r$ and global share $\alpha_r=K_r/N_r$;
- bad-label hits $H_r$ and allocation survivors $S_r=L_r-H_r$;
- total destroyed local target children $T_r$;
- normalized targeting $\theta_r$ when defined;
- realized local hazard $f_r^{\mathrm{local}}$, relative factor
  $w_r^{\mathrm{local}}$, and cumulative $D(Q)$;
- closest surviving distance to the head;
- safe-window nonemptiness and head-hit indicators; and
- global 2-gap count, which must continue to match exact $r-2$ reproduction.

Exact-quota runs should additionally report the partial sums

```math
\sum_{r<Q}u_r
\qquad\text{and}\qquad
\sum_{r<Q}\left(u_r^2+\frac{u_r}{N_r^{\mathrm{shot}}}\right),
```

because preserving each finite shot count does not by itself verify the
cumulative hypotheses in Property XI.

Counts and reciprocal-spacing charts must be derived from the same rows so
that zero count and infinite implied spacing remain exactly equivalent.

### 18.5 Comparison With The Real Filter

Apply the same observables to the deterministic modular filter. It has no
chosen $K_r$ policy label, but its realized local hit count $H_r$ can still be
compared with the feasible interval $[H_{\min},H_{\max}]$ and the uniform
benchmark $H_0$ after selecting the matching global destruction budget.

The informative comparison is not merely whether the real filter kills more
than the random mean at one transition. It is whether its realized targeting
scores and cumulative local hazard persistently track the random, delayed,
noisy, or perfect-adversarial companions across growing heads.

This program does not infer intent from the score. It measures how much the
real arithmetic placement behaves as though it had access to positional
information.

## 19. Property XI: Exact CRT Quotas With Random Locations Recur At The Head

**Status:** **Conditional mathematical theorem. Stainless verification
pending.** The exact one-filter probability follows from uniform sampling
without replacement. Infinite head recurrence additionally assumes persistent
head availability and independence or adequate mixing across layers. The
square-window conclusion assumes blind placement and quadratic eligible
supply. None of those stochastic premises is asserted for the real sieve.

The balanced random sister fixes two harmful copy indices per parent. A closer
statistical sister can instead retain the exact number of shots supplied by a
chosen CRT population and randomize only their locations. This preserves the
real quota while removing the arithmetic targeting information. Exact quotas
create dependence within one layer, but they do not change the one-position
survival scale when allocated uniformly.

At filter $r$, let $U_r$ contain $N_r$ eligible values and let the CRT quota be
$J_r$, with $0\le J_r\le N_r-2$. The exact-quota random sister chooses one
uniformly random size-$J_r$ subset of $U_r$ as its shot set. For a specified
2-gap whose two endpoints belong to $U_r$, both endpoints survive precisely
when every shot is selected from the other $N_r-2$ values. Therefore

```math
\begin{aligned}
s_r
&=\frac{\binom{N_r-2}{J_r}}{\binom{N_r}{J_r}}
&&[\text{Uniform Exact-Quota Choice}]\\
&=\frac{(N_r-J_r)(N_r-J_r-1)}{N_r(N_r-1)}.
&&[\text{Factorial Simplification}]
\end{aligned}
```

Write the shot fraction as

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
\sum_{r<Q}u_r
&=\log\log Q+O(1),
&&[\text{CRT-Rate Cumulative Quota}]\\
\sum_{r<Q}
\left(u_r^2+\frac{u_r}{N_r}\right)
&=O(1).
&&[\text{Summable Finite-Population Error}]
\end{aligned}
```

The complete-period CRT benchmark $u_r=1/r$ satisfies these conditions. A
different local CRT quota must be checked against them; preserving a numerical
shot count alone does not make the conclusion automatic.

Multiplying the exact without-replacement factors gives

```math
\begin{aligned}
P_{\mathrm{quota}}(Q)
&=\prod_{r<Q}s_r
&&[\text{Survive Every Filter}]\\
&=\exp\left(\sum_{r<Q}\log s_r\right)
&&[\text{Product To Sum}]\\
&=\exp\left(-2\sum_{r<Q}u_r+O(1)\right)
&&[\text{Summable Error}]\\
&\asymp\frac{C}{(\log Q)^2}.
&&[\text{Cumulative Quota Condition}]
\end{aligned}
```

Thus the exact-quota sister has the same one-head survival order as the
balanced random sister. It is not an independent Bernoulli filter inside one
layer; it is a uniform shuffle conditioned on the exact CRT shot count.

Suppose the distinguished head candidate is eligible with conditional
probability at least $b_0>0$, uniformly for all sufficiently large prime heads,
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
\boxed{
\Pr(H_Q\text{ occurs infinitely often})=1.
}
\qquad[\text{Q.E.D.}]
```

This is an almost-sure theorem, not a guarantee for every random realization.
The set of realizations with only finitely many head hits has probability zero,
but it is not logically empty.

For square-safe windows, assume $B(Q)\asymp C_0Q^2$ eligible starts and the
same blind-placement empty-window premise used by the balanced random sister.
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

For consecutive primes $p<q$, the real accepted-shot quota in the next safe
window is maintained in [Exact Accepted Filter Strikes](
../../properties/sieve-sequence/exact-accepted-local-filter-strikes.md):

```math
A(p,q)
=
\pi\left(\left\lfloor\frac{q^2-1}{p}\right\rfloor\right)
-\pi(p-1).
```

Using this local quota as $J_r=A(p,q)$ in the random-location sister is well
defined, but its fractions $u_r=J_r/N_r$ must still satisfy the displayed
cumulative conditions for the head proof above. The [Exact Global 2-Gap Count](
../../properties/sieve-sequence/exact-global-two-gap-count.md) supplies the
complete-period density; neither exact count determines local placement in the
real sieve.

No Scala/Stainless theorem currently encodes exact-quota random sampling,
Borel-Cantelli recurrence, or the cumulative quota asymptotic.

## 20. Property XII: Biased Exact Quotas Have A Logarithmic Skew Frontier

**Status:** **Conditional mathematical theorem. Stainless verification
pending.** The marginal normalization follows from the stipulated
group-exchangeable exact-quota law. Translating endpoint marginals into 2-gap
destruction assumes that double hits on one pair have the stated quadratic
order. Head recurrence and square-window conclusions retain the availability,
blind-placement, and cross-layer mixing premises of Properties IV and XI.

The neutral exact-quota sister treats every eligible value symmetrically. A
bad-sister perturbation can keep the same quota $J_r$ while making 2-gap
endpoints proportionally more likely to receive a shot. This asks how much
positional preference the quota can carry before the almost-sure head
conclusion changes.

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

For one 2-gap, assume the probability that both endpoints are shot is
$O((p_r^{E})^2)$. Its destruction fraction then satisfies

```math
\begin{aligned}
f_r
&=2p_r^{E}-\Pr(\text{both endpoints are shot})
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
cumulative survival is defined once $2\kappa_r<r$. Every regime below satisfies
this inequality for all sufficiently large filters; the finite prefix is
absorbed into a positive constant. Thus

```math
P_{\kappa}(Q)
=
\prod_{r<Q}\left(1-\frac{2\kappa_r}{r}\right)
=e^{-D_{\kappa}(Q)},
```

where

```math
D_{\kappa}(Q)
:=
\sum_{r<Q}-\log\left(1-\frac{2\kappa_r}{r}\right).
```

If $\kappa_r=\kappa<\infty$ is fixed, then

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
\boxed{
\text{every fixed finite proportional skew gives infinitely many head hits almost surely.}
}
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
\boxed{
\begin{aligned}
c<\frac12
&\Longrightarrow
\text{infinitely many head hits almost surely, with mixing},\\
c\ge\frac12
&\Longrightarrow
\text{only finitely many head hits almost surely}.
\end{aligned}
}
\qquad[\text{Q.E.D.}]
```

In this explicitly normalized family, the equality $c=1/2$ is on the failure
side because the remaining factor $(\log Q)^{-2}$ makes the boundary prime
series converge. If $\beta_r$, rather than effective $\kappa_r$, is specified
at its raw equality boundary, quota normalization changes lower-order terms and
the cumulative series $D_{\kappa}(Q)$ must be evaluated directly.

The robust head-safe frontier is therefore

```math
\boxed{
\kappa_r
\le
1+\left(\frac12-\varepsilon\right)\log r
\quad\Longrightarrow\quad
\text{head recurrence almost surely, with mixing}.
}
```

For square windows, quadratic supply gives the larger robust frontier

```math
\boxed{
\kappa_r
\le
1+(1-\varepsilon)\log r
\quad\Longrightarrow\quad
\text{eventual square-window occupancy almost surely}.
}
```

Hence the intermediate range between approximately $(1/2)\log r$ and
$\log r$ preserves square windows but not infinitely recurring head hits. The
window statement is stronger than necessary: the twin-prime-style conclusion
needs only infinitely many successful windows.

For an irregular skew schedule, the authoritative head criterion is

```math
\boxed{
\sum_{Q\text{ prime}}e^{-D_{\kappa}(Q)}=\infty,
}
```

together with persistent availability and adequate mixing. A pointwise skew
percentage cannot replace this cumulative test.

No Scala/Stainless theorem currently encodes biased exact-quota sampling, the
endpoint-pair collision premise, or these analytic phase boundaries.

## 21. Relation To The Real Sieve

For a real 2-gap $(a,a+2)$ and incoming prime $r$, the harmful copies are not
chosen freely. They are fixed by

```math
K_{a,r}^{\mathrm{real}}
=
\{-aM^{-1},-(a+2)M^{-1}\}\pmod r.
```

Different parents are coupled through this single arithmetic rule. The real
filter has neither independent policy coins nor freely allocated good and bad
labels. It nevertheless has directly measurable local destruction $f_r$, a
relative factor $w_r=rf_r/2$, and cumulative hazard $D(Q)$. Assigning it an
effective policy share $\alpha_r$ requires an additional declared companion
benchmark, while assessing its positional concentration requires the separate
hit count and targeting normalization from §18.

The score developed in [Realized Filter Adversariality](
../../properties/sieve-sequence/realized-filter-adversariality-score.md)
provides a finite-transition destruction normalization. The new allocation
axis asks an additional question: for the same global destruction budget, how
close is the realized local hit count to the uniform mean or targeted maximum?

The companion diagrams identify what a transfer theorem would need to control:

- the realized relative damage $w_r$ and cumulative hazard $D(Q)$;
- the exact-quota fractions $u_r$ and their cumulative deviation from
  $\sum_{r<Q}1/r$;
- raw endpoint preference $\beta_r$, quota-normalized effective skew
  $\kappa_r^{\mathrm{eff}}$, and cumulative skew hazard $D_{\kappa}(Q)$;
- any scheduled or effective policy budget $A(Q)$ used for a particular
  companion specialization;
- the availability and abundance premises for the chosen target; and
- sufficient cross-layer mixing for divergent head-event sums.

No current property proves that the real CRT-coupled filter follows the random,
good, delayed, noisy, or perfectly adversarial companion asymptotically.

## 22. Limitations

The balanced companions track descendants of existing 2-gaps rather than a
coherent randomized sequence of integers. They do not model non-2 gaps, gap
mergers, or shared endpoint effects. Their adversary is stronger than the real
filter because it may select harmful copies separately for each parent. The
good sister is also an oracle: it knows the current target and moves both
deletions elsewhere. Neither endpoint is a description of the real filter.

The bad/random window theorem assumes spatial uniformity. The bad/good window
theorem instead assumes a quadratic optimistic supply $B(Q)$. Its head theorem
assumes an eligible good-sister head lineage with availability bounded below.
None of these premises follows from the exact-two choice alone.

The exact-CRT-quota/random-location theorem preserves shot counts but discards
their deterministic arithmetic locations. Its recurrence conclusion requires
the cumulative quota conditions in Property XI, persistent head availability,
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

Accordingly, this article proves a phase diagram for stipulated companions. It
does not prove that the real sieve occupies any particular regime, and it does
not prove the twin-prime conjecture.

## 23. Conclusion

Balanced 2-gap companions make global persistence deliberately uninformative:
every parent always leaves $r-2$ children, so the complete-period population
grows under friendly, random, adversarial, and mixed selection alike. The
local distinction is carried by realized destruction relative to random, its
cumulative hazard, and allocation.

The central formulas are

```math
\begin{aligned}
N_{k+1}&=(r_k-2)N_k,\\
D(Q)&=\sum_{r<Q}-\log(1-f_r),\\
w_r&=\frac{rf_r}{2},\\
P(Q)&=e^{-D(Q)},\\
s_r
&=\frac{\binom{N_r-2}{J_r}}{\binom{N_r}{J_r}},\\
P_{\mathrm{quota}}(Q)
&=\prod_{r<Q}s_r
\asymp\frac{C}{(\log Q)^2},\\
\kappa_r^{\mathrm{eff}}
&=\frac{\beta_r}{1+(\beta_r-1)x_r},\\
D_{\kappa}(Q)
&=\sum_{r<Q}-\log\left(1-\frac{2\kappa_r}{r}\right),\\
A(Q)&=\sum_{r < Q}-\log(1-\alpha_r),\\
\lambda_Q^{\mathrm{bad/random}}
&\asymp C\frac{Q^2}{(\log Q)^2}e^{-A(Q)},\\
\lambda_Q^{\mathrm{bad/good}}
&\asymp C_0Q^2e^{-A(Q)},\\
\max(0,L-K)&\le S\le\min(L,N-K).
\end{aligned}
```

The main answer is that there is no maximum finite constant factor worse than
random. If $w_r=w<\infty$, local survival decays only as
$(\log Q)^{-2w}$; quadratic square-window supply still dominates, and the head
probability series still diverges. Under the article's stated spatial and
mixing premises, square windows are eventually nonempty and head 2-gaps recur
infinitely often for every fixed finite $w$.

The exact-quota sister sharpens what “random” means: it keeps the CRT number of
shots and randomizes only their positions. Uniform sampling without replacement
gives the exact factor $s_r$ above. When the quota fractions have cumulative
CRT rate, head-event probabilities remain of order $(\log Q)^{-2}$; their sum
over prime heads diverges, and adequate cross-layer mixing gives infinitely
many head hits almost surely. Eventual square-window occupancy is a stronger
companion conclusion; only infinitely many successful windows or head hits are
needed for infinitely many certificates.

The biased exact-quota sister confirms the same phase boundary from a second
direction. Every fixed finite effective skew toward 2-gap endpoints retains
infinite head recurrence with mixing. In the family
$\kappa_r=1+c\log r$, head recurrence holds for $c<1/2$ and fails almost surely
for $c\ge1/2$; square-window occupancy instead has coefficient $c=1$. Thus the
robust frontier functions are

```math
\begin{aligned}
\kappa_r
&\le1+\left(\frac12-\varepsilon\right)\log r
&&[\text{Head Recurrence}],\\
\kappa_r
&\le1+(1-\varepsilon)\log r
&&[\text{Eventual Square Windows}].
\end{aligned}
```

The equality $c=1/2$ is on the failure side for the explicitly normalized
effective-skew family. If a raw endpoint weight $\beta_r$ is specified instead,
quota normalization changes lower-order terms and the cumulative prime-head
series must be checked directly.

The first nontrivial boundary occurs when worsening grows with the filter. For
$w_r=1+c\log r$, square-window survival holds for $c<1$, while head recurrence
holds for $c<1/2$. Equivalently, robust sufficient total-destruction regimes
are $f_r<(2-\varepsilon)\log r/r$ for square windows and
$f_r<(1-\varepsilon)\log r/r$ for the head. These are cumulative asymptotic
regimes, not fresh percentages that may be spent independently at each filter.

A repeated fixed absolute bad share $\alpha>0$ is locally fatal only because it
makes $w_r\sim\alpha r/2$, an increasingly severe multiple of the shrinking
random rate. The absolute-share bad/random and bad/good diagrams remain useful
specializations: for $\alpha_r\sim c\log r/r$, their square-window threshold is
$c=2$; bad/random head recurrence requires $c<1$, whereas bad/good recurrence
includes $c=1$ under optimistic availability and mixing.

Every relative-hazard threshold must be measured in the tracked segment. A
target-aware bad sister can erase $L$ local candidates as soon as $K\ge L$ and
can kill one head candidate with one bad label, even when $K/N$ is globally
tiny. Uniform allocation instead leaves expected population $L(1-K/N)$, while
optimistic allocation leaves $\min(L,N-K)$. Total relative damage and targeting
intelligence are therefore independent axes, not alternative names for one
percentage.

The real sieve question is now expressible as a cumulative comparison rather
than a vague claim of random or adversarial behavior: measure the total local
destruction $f_r$ generated by the CRT-coupled harmful indices, normalize it by
the random rate to obtain $w_r$, measure where the controllable damage lands
relative to the head, and compare the resulting cumulative hazard with the
companion thresholds above.

## Related Work

- [Balanced Randomized 2-Gap Companion Process](
  ../../candidates/balanced-randomized-2-gap-companion-process.md)
- [Balanced Adversarial 2-Gap Companion Process](
  ../../candidates/balanced-adversarial-2-gap-companion-process.md)
- [Realized Filter Adversariality Score](
  ../../properties/sieve-sequence/realized-filter-adversariality-score.md)
- [Exact Global 2-Gap Count](
  ../../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Copy-Index Filter Frequency](
  ../../properties/sieve-sequence/copy-index-filter-frequency.md)
- [Short-Window Discrepancy](../../candidates/short-window-discrepancy.md)
- [Learnings: Capacity Argument](
  ../learnings/learnings-capacity-argument.md)
