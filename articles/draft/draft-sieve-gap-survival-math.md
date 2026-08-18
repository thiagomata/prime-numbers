# Sieve Gap Survival: A Math-Only Follow-Up to Sieve Sequences

**Status:** Superseded historical draft — mathematical exploration, not a
Stainless-verified article.

**Author:** Mata, T. H.
Independent Researcher
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)
**GitHub:** [@thiagomata](https://github.com/thiagomata)

This file preserves the early copy/merge, stable-absence, cluster, and local-
capacity development. It is no longer the current proof-boundary document.
The twin-prime analysis continues in [Structural Properties and Signed
Boundaries of 2-Gaps in Sieve Sequences](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics-v2.md); the
distinct prime-plus-almost-prime relaxation is developed in [Relaxed
Almost-Prime Production in Sieve Sequences](https://github.com/thiagomata/prime-numbers/blob/master/articles/draft/draft-relaxed-almost-prime-sieve-sequence.md).

## Abstract

This article studies what the Sieve Sequence transition says about future
gaps, especially 2-gaps. It follows the verified Sieve Sequence article, but
it does not attempt to package these claims as verified Stainless properties.
The goal is mathematical: describe how gaps are copied or merged under a
filter, identify stable absence conditions for gap values, and separate global
survival facts from the local safe-zone question that controls twin primes. The
central boundary is positional. Full-period gap counts can grow, and
full-period 2-gaps can survive globally, while twin-prime certification
requires a 2-gap in the finite safe window below the square of the current
head.

## 1. Setting

Let a sieve stage be

```math
\begin{aligned}
S_k &= (h,\ \overline{P},\ T,\ G), \\
M &= \prod_{p \in \overline{P}} p.
\end{aligned}
```

The stage emits the increasing sequence

```math
\begin{aligned}
L(S_k) = (\ell_i)_{i \ge 0},
\end{aligned}
```

where each emitted value is accepted by every prime in
$\overline{P}$. The gap cycle is

```math
\begin{aligned}
G = [g_0,\ g_1,\ \ldots,\ g_{T-1}],
\qquad
g_i = \ell_{i+1} - \ell_i.
\end{aligned}
```

A **d-gap** is a pair of consecutive emitted values whose difference is
$d$. A **2-gap** is therefore a twin-prime candidate: a consecutive pair
$(x, x+2)$ that survives all filters in the current tail.

The current stage filters only primes smaller than $h$. Therefore it is
prime-correct below $h^2$: if a value $v < h^2$ is accepted by the stage
and $v \ge h$, then $v$ is prime. A 2-gap

```math
\begin{aligned}
x,\ x+2 \in [h,\ h^2)
\end{aligned}
```

therefore certifies a twin-prime pair. This motivates the **safe window**

```math
\begin{aligned}
W_h = [h,\ h^2).
\end{aligned}
```

The global gap cycle may contain many 2-gaps, but only the 2-gaps inside
$W_h$ are immediately certified as twin primes at this stage.

## 2. The Transition: Copy Or Merge

The next stage adds the current head $h$ as a new filter. Before filtering,
the current gap cycle is viewed through a longer window. The expanded object
has the same emitted values as the current cycle; the finite window merely
exposes the lifted copies:

```math
\begin{aligned}
e_i &= c_i
  && \text{[same emitted value]} \\
e_{qT+r} &= c_r + qM,
  && 0 \le q < h,\ 0 \le r < T.
\end{aligned}
```

Filtering removes exactly those expanded values divisible by $h$. The gaps
of the next stage come from the remaining consecutive survivors.

There are only two local possibilities.

### 2.1 Copy

If two consecutive expanded values both survive, then the old gap is copied:

```math
\begin{aligned}
e_i,\ e_{i+1} \text{ survive}
  &\Longrightarrow
  f_{j+1} - f_j = e_{i+1} - e_i \\
  &= g_{i \,\text{mod}\, T}.
\end{aligned}
```

The new stage did not invent this gap. It inherited it.

### 2.2 Merge

If the endpoints survive but one or more expanded values between them are
removed, the new gap is the sum of the skipped old gaps:

```math
\begin{aligned}
e_i,\ e_m \text{ survive},\quad
e_{i+1},\ldots,e_{m-1} \text{ removed}
  &\Longrightarrow
  f_{j+1} - f_j = e_m - e_i \\
  &= \sum_{r=i}^{m-1} (e_{r+1}-e_r) \\
  &= \sum_{r=i}^{m-1} g_{r \,\text{mod}\, T}.
\end{aligned}
```

Thus filtering does not create gaps by an arbitrary operation. Each next
gap is either a copied old gap or a sum of a contiguous block of old gaps.

## 3. Non-Generation Of Small Gaps

The copy-or-merge rule gives a useful negative principle.

Let $d$ be a positive gap value. If a stage has no copied source gap equal
to $d$, and no contiguous block of old gaps sums to $d$, then $d$ cannot
appear in the next stage.

```math
\begin{aligned}
d \notin G
\quad\land\quad
\forall i < j,\ \sum_{r=i}^{j-1} g_{r \,\text{mod}\,T} \ne d
\quad\Longrightarrow\quad
d \notin G'.
\end{aligned}
```

This becomes especially simple for 2-gaps after the filter by 2 has been
installed. From then on, every emitted value is odd, so every gap between
consecutive emitted values is positive and even.

If no gap of value 2 exists at such a stage, then no later stage can
recreate one:

```math
\begin{aligned}
2 \notin G_k
&\Longrightarrow 2 \notin G_{k+1} \\
&\Longrightarrow 2 \notin G_{k+2} \\
&\Longrightarrow \cdots.
\end{aligned}
```

Indeed, let $g' \in G_{k+1}$ be any next-stage gap. By the copy-or-merge
rule, it has one of the following two forms:

```math
\begin{aligned}
\text{Copy case:}\quad
g' &= g_i
  && \text{for some } g_i \in G_k, \\
\text{Merge case:}\quad
g' &= \sum_{r=i}^{j-1} g_r
  && \text{for some } j > i+1.
\end{aligned}
```

In the copy case, $g' \ne 2$ because $2 \notin G_k$. In the merge case,
the post-2 parity condition gives $g_r \ge 2$ and even for every summand,
and the merge contains at least two summands. Hence the merged gap is at
least the sum of two positive even gaps:

```math
\begin{aligned}
g'
  &= \sum_{r=i}^{j-1} g_r \\
  &\ge 4.
\end{aligned}
```

Therefore every next-stage gap satisfies $g' \ne 2$, so $2 \notin G_{k+1}$.
Induction gives absence at every later stage.

This does not prove twin primes exist. It gives the opposite kind of tool:
if a computation ever found a post-2 stage with no 2-gaps, that absence
would persist at every later stage. Since later stages can only copy or merge
from that gap population, no later stage could certify a new twin-prime pair
from a 2-gap. Conversely, any proof of twin-prime persistence must explain why
the sieve never reaches that dead configuration.

## 4. Full-Period 2-Gap Survival

Over a complete expanded period, a single 2-gap has a simple survival law.
Let $(r,r+2)$ be a 2-gap in the current stage. Its lifted copies are

```math
\begin{aligned}
(r+iM,\ r+2+iM), \qquad 0 \le i < h.
\end{aligned}
```

A lifted copy is destroyed by the new filter $h$ exactly when one endpoint
is divisible by $h$:

```math
\begin{aligned}
r+iM &\equiv 0 \pmod h,
\\
\text{or}\qquad
r+2+iM &\equiv 0 \pmod h.
\end{aligned}
```

Since $M$ is coprime to $h$, the values $r+iM$ cover all residue classes
modulo $h$ exactly once as $i$ ranges from $0$ to $h-1$. Therefore each of
the two endpoint conditions has exactly one solution. For $h>2$, the two
solutions are distinct, because otherwise $h$ would divide 2.

So each current 2-gap has exactly

```math
\begin{aligned}
h-2
\end{aligned}
```

surviving lifted 2-gap descendants over the complete expanded period.

This is a global, full-period statement. It says 2-gaps are not globally
extinguished by the transition once $h>2$. It does not say where those
descendants land in the next stage.

## 5. The Safe Window Is The Hard Part

The safe-window question is local. A certifying 2-gap must have both
endpoints below the square boundary:

```math
\begin{aligned}
\text{Does } G_k \text{ contain a 2-gap } (x,x+2)
\text{ with } x,\ x+2 \in [h,\ h^2)?
\end{aligned}
```

The full-period question is global:

```math
\begin{aligned}
\text{Does } G_k \text{ contain a 2-gap with left endpoint in } [h,\ h+M)?
\end{aligned}
```

These are not equivalent. The period length $M$ grows primorially, while the
safe window has length roughly $h^2$. After the early stages, $M$ is much
larger than $h^2$, so the safe window sees only a small initial fragment of
the full period.

This is the main boundary:

```math
\begin{aligned}
\text{global 2-gap survival}
\quad\not\Longrightarrow\quad
\text{safe-window 2-gap survival}.
\end{aligned}
```

Full-period CRT uniformity is exact. It controls lifted copies over complete
periods. It does not control the distribution of 2-gap positions inside a
short initial window.

## 6. Local Capacity

Inside the safe window $W_h=[h,h^2)$, the new filter $h$ has only linearly
many strike points:

```math
\begin{aligned}
h,\ 2h,\ 3h,\ \ldots,\ (h-1)h.
\end{aligned}
```

Thus there are at most $h-1$ filter strikes inside the safe window.

A 2-gap $(x,x+2)$ is destroyed only if the filter hits one of its endpoints:

```math
\begin{aligned}
x \equiv 0 \pmod h
\quad\text{or}\quad
x \equiv -2 \pmod h.
\end{aligned}
```

If 2-gaps are isolated enough that a single strike cannot destroy more than
one local 2-gap, then a simple capacity inequality gives survival:

```math
\begin{aligned}
G_{\mathrm{local}}(h) > h-1
\quad\Longrightarrow\quad
\text{at least one local 2-gap survives the } h\text{-filter}.
\end{aligned}
```

Here $G_{\mathrm{local}}(h)$ is the number of 2-gaps $(x,x+2)$ before the
$h$-filter is applied with both endpoints in $[h,h^2)$.

This is not a proof of the Twin Prime Conjecture. It is a conditional
reduction: under the stated isolation hypothesis, local 2-gap survival follows
from a local counting inequality.

## 7. Cluster Survival

A more geometric version of the same idea is cluster survival.

Suppose two 2-gaps lie close together, for example at

```math
\begin{aligned}
(x,x+2)
\quad\text{and}\quad
(x+6,x+8).
\end{aligned}
```

The whole cluster lies in an interval of width 8. If $h>8$, then the
$h$-filter can strike at most one integer inside this width-8 interval.
Therefore it cannot destroy both 2-gaps in the same filter step.

```math
\begin{aligned}
h>8
\quad\land\quad
\{x,x+2,x+6,x+8\} \subset [a,a+8]
\quad\Longrightarrow\quad
\text{at least one 2-gap survives}.
\end{aligned}
```

This is a conditional survival principle. It does not prove such a cluster
always exists in the safe window. It says that if the safe window contains a
small redundant cluster of 2-gaps, then one filter cannot eliminate the
entire cluster.

The difficult part is reconstruction. After one filter, a two-gap cluster
may become a singleton 2-gap. A singleton can be destroyed by the next
filter. Therefore an infinite survival proof cannot merely preserve one
cluster once; it must show that enough local 2-gap structure is rebuilt in
each stage.

## 8. Once Local, Still Local Unless Destroyed

There is a useful stability observation. If a 2-gap lies inside the safe
window for the current head, then after moving to a larger head the square
boundary grows faster than the left edge.

Let $h'$ be the next head, with $h'>h$. If a 2-gap coordinate $x$ satisfies

```math
\begin{aligned}
x,\ x+2 \in [h,\ h^2),
\end{aligned}
```

and the 2-gap at $x$ survives the next filter, then both endpoints remain
below the next square boundary:

```math
\begin{aligned}
x+2 < h^2 < (h')^2.
\end{aligned}
```

The remaining issue is the lower edge. The next stage begins at $h'$, so a
surviving 2-gap relevant to the next stage must also satisfy

```math
\begin{aligned}
x \ge h'.
\end{aligned}
```

For candidates that survive as actual next-stage emitted gaps, this lower
edge is automatic: the next sequence begins at $h'$, and its emitted values
are at or above $h'$. Thus a surviving emitted 2-gap whose endpoints were
already below $h^2$ stays below the next square boundary. The safe-window
obstruction is not that local candidates drift too far right; it is that
they may be destroyed, or that no local candidate exists in the first place.

## 9. Dead Configurations And Later-Forbidden Gaps

The copy-or-merge rule gives a broader way to reason about future stages.

For a property $P$ of gap lists, suppose:

1. $P$ is absent from the current gap list.
2. Copying cannot create $P$.
3. Merging contiguous blocks of current gaps cannot create $P$.

Then $P$ is absent from the next gap list. By induction, once such a
property becomes absent under these closure conditions, it remains absent at
every later stage.

For a single gap value $d$, define:

```math
\begin{aligned}
\text{Reach}_G(d)
  &\Longleftrightarrow
  \exists i < j,\ \sum_{r=i}^{j-1} g_{r \,\text{mod}\,T} = d.
\end{aligned}
```

If $\text{Reach}_G(d)$ is false, then $d$ cannot appear at the next
stage. For small values this can be very strong. In post-2 stages:

```math
\begin{aligned}
\text{Reach}_G(2)
\Longleftrightarrow
2 \in G.
\end{aligned}
```

So absence of 2 is a dead configuration. Other small gap values require more
care. For example, a gap of 6 can be created by merging gaps 2 and 4, or by
copying an existing 6. Thus absence of 6 is not permanent unless the current
cycle also lacks every contiguous block summing to 6.

This suggests a family of finite questions:

```math
\begin{aligned}
\text{Which gap values are reachable from the current gap cycle by copy/merge?}
\end{aligned}
```

Answering this for a finite stage can rule out entire classes of future
behavior.

## 10. Historical Form Of The Main Open Question

The structural facts above reduce twin-prime persistence to a local
distribution question.

Let

```math
\begin{aligned}
A_h = \{x \in [h,h^2) \mid x \text{ and } x+2
       \text{ are consecutive accepted values of } S_h
       \text{ and } x+2 < h^2\}.
\end{aligned}
```

The safe-window twin-prime question is:

```math
\begin{aligned}
A_h \ne \varnothing
\quad\text{for infinitely many heads } h.
\end{aligned}
```

A stronger stage-by-stage survival condition is:

```math
\begin{aligned}
|A_h| > h-1.
\end{aligned}
```

If this stronger inequality holds from some point onward, and if each local
filter strike destroys at most one local 2-gap, then each new filter lacks
enough local strikes to destroy all local 2-gaps.

This is a sound historical sufficient condition, but it is not the sharpest
current formulation. Later work replaces the raw strike count by exact
accepted strikes and then by a weighted harmful-excess quadratic threshold.
It also proves that optimizing separate unsigned capacities cannot clear that
threshold on an unbounded family.

Historical observation only: the superseded $[p,p^2]$ experiment reported
this stronger inequality in its tested range after an initial crossover
([3], superseded). The canonical $[q,q^2)$ transition data do not directly
measure $A_h$, so no current evidence is claimed here. The missing theorem is
not a full-period CRT statement. It is a positional theorem about where the
2-gaps fall inside the short safe window.

## 11. What This Article Claims

This historical draft established the following mathematical structure:

1. Filtering changes gaps only by copying or merging neighboring gaps.
2. Some gap absences are stable under later copy/merge transitions; absence
   of 2 in a post-2 stage is the cleanest example.
3. Over a complete period, every 2-gap has surviving descendants after an
   odd prime filter.
4. Safe-window survival is local and positional; it does not follow from
   full-period survival alone.
5. Local capacity and cluster arguments give conditional survival rules.
6. The hard open problem is proving that the safe window contains enough
   2-gaps infinitely often, or under stronger hypotheses, from some point
   onward.

No formal verification is claimed for the new results in this article. The
verified Sieve Sequence article supplies the stage language and the
current-to-next construction; this article explores mathematical consequences
that should be considered candidates for future formalization.

## 12. Current Successor Boundary

The newer signed analysis preserves the central global-versus-local lesson but
replaces this article's raw strike counts with a sharper accounting. This
section is a qualitative summary only; every formula below is defined and
proved in the successor article, [Structural Properties and Signed Boundaries
of 2-Gaps in Sieve Sequences](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics-v2.md).

Where this article compares the local 2-gap count with an unsigned strike
budget, the successor follows a conditioned chain of filters with an exact
population ledger and a weighted, signed energy. Three changes matter:

1. **Exact accepted strikes replace raw strike counts.** The successor counts
   only strikes that remove values actually accepted by the earlier filters,
   and tracks the eligible population layer by layer instead of comparing a
   window count to a window budget.

2. **A weighted quadratic threshold replaces the counting inequality.** The
   surviving population is compared against a weighted Cauchy–Schwarz-type
   energy bound: proving that the realized signed energy stays below a
   computable threshold implies a positive survivor count. The open candidate
   is therefore an arithmetic upper bound on that realized energy, not another
   complete-period population count.

3. **Complete old-period blocks reduce to residue energy.** For a general
   incoming prime, the harmful excess in complete block runs is controlled by
   the residue-class histogram of old 2-gap starts, and the sharp interval
   bound at the first odd composite layer is a small explicit constant. An
   arbitrary square window still contains at most two partial old-period
   fragments, and late layers may contain no complete old-period block at all.

The successor's remaining program is, correspondingly: prove a relative
residue-energy estimate in the actual short window; control the two signed
partial boundaries; and compose those bounds through the weighted filter
chain.

The separate candidate #25 relaxes `p+2` to have at most two prime factors.
Its Type-I remainder is a prime-progression discrepancy and its final
scalar-centered weight retains nonprincipal character modes, so that program
requires an averaged prime-progression theorem and a locally adapted bilinear
estimate; it does not prove a 2-gap. That relaxation is developed in [Relaxed
Almost-Prime Production in Sieve Sequences](https://github.com/thiagomata/prime-numbers/blob/master/articles/draft/draft-relaxed-almost-prime-sieve-sequence.md).

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). *Formal Verification of the Sieve Sequence*. Available
at: [../chapter6/sieve-sequence.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Gap Dynamics and Twin Prime Candidates in Sieve
Sequences*. Available at:
[../chapter6/gap-dynamics.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Empirical Analysis of Local 2-Gap Density in Sieve
Sequences* (superseded draft). Available at:
[draft-empirical-g-local-analysis.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/draft/draft-empirical-g-local-analysis.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Structural Properties and Signed Boundaries of 2-Gaps in
Sieve Sequences*. Available at:
[../chapter6/gap-dynamics-v2.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics-v2.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2026). *Relaxed Almost-Prime Production in Sieve Sequences*.
Available at:
[draft-relaxed-almost-prime-sieve-sequence.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/draft/draft-relaxed-almost-prime-sieve-sequence.md)
