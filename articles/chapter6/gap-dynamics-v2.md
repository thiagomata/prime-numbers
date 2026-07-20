# Structural Properties and Open Boundaries of 2-Gaps in Sieve Sequences

**Review status:** Mathematical and editorial review candidate
**Author:** Mata, T. H.
Independent Researcher
**Email:** [thiago.mata@email.com](mailto:thiago.mata@email.com)
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

This article studies 2-gaps in the periodic survivor sequences produced by
successive prime filters. Fix a prime $p$ and keep exactly the integers not
divisible by any smaller prime. The kept integers repeat modulo the product of
those smaller primes, and the adjacent differences in one period form a finite
gap cycle that generates the whole infinite survivor sequence.

Within that complete period, CRT gives a lower bound for cyclic 2-gaps. After
the filter $2$, each odd prime $r<p$ forbids only two residue classes for the
start of a 2-gap, so one period contains at least $\prod(r-2)$ cyclic 2-gaps
over those odd primes. Adding another prime filter copies a gap when both
values around it survive and otherwise merges neighboring gaps. For each new
odd filter, at most two residue classes of repeated copies of a 2-gap are
removed, so the absolute full-period 2-gap population grows while its relative
density decreases.

These are global statements over complete periods. They do not imply that a
2-gap appears in a particular square-safe window $[q,q^2)$, where surviving
endpoints would be certified prime. The article therefore separates what the
complete-period sieve structure proves from the remaining local placement
problem.

---

## 1. Scope

For a prime $p$, define the $p$-stage survivor sequence as the increasing
sequence of integers not divisible by any prime smaller than $p$. This
sequence is periodic modulo the product of those smaller primes, so one finite
period determines the whole infinite sequence. The adjacent differences inside
that finite period form a cyclic gap list. Repeating the gap list walks through
the same infinite survivor sequence.

The Sieve Sequence article defines this mathematical object and records the
verified base properties used here: accepted-value completeness, strict
increase, period shift, finite gap-cycle reconstruction, exact survivor count,
and the copy-or-merge transition rule [[1]](#references). The present article
uses those facts as its foundation and then studies the special behavior of
2-gaps as mathematical objects.

This article studies the value $2$ in those cyclic gap lists. A 2-gap has
endpoints $(x,x+2)$. Once the filter $2$ has been installed, $x+1$ is even and
rejected, so accepted endpoints at distance $2$ are consecutive survivors. The
article treats the resulting global counts, filtering rules, finite-batch
survival facts, and local square-window boundaries as mathematical statements.

The article is organized around properties of the sequence itself:

1. every prime determines a complete survivor gap cycle avoiding all
   earlier prime multiples;
2. that complete cycle has an exact positive 2-gap count;
3. filtering copies or merges old gaps;
4. absence of 2-gaps is stable under later filtering;
5. repetition gives two exact forbidden copy-index classes per new prime;
6. finite batches have an exact complete-period survivor count;
7. rotation preserves global cyclic multiplicities but not local placement;
8. a square-safe survivor is a genuine twin-prime pair;
9. one transition has an exact accepted-strike threshold;
10. one perfect scenario has a finite certificate;
11. infinitude requires a new short-window distribution theorem.

---

## 2. Stage And Window Notation

Let $p\ge5$ be the prime defining the stage. Every prime smaller than $p$ is an
installed filter. Define the modulus

```math
\begin{aligned}
M_p &= \prod_{r<p} r,
&& [\text{By Definition}]
\end{aligned}
```

where $r$ ranges over primes. The accepted set is periodic modulo $M_p$.
Within one period, write the ordered accepted values as

```math
\begin{aligned}
e_0<e_1<\cdots<e_{T-1},
\end{aligned}
```

with cyclic gaps

```math
\begin{aligned}
g_i &= e_{i+1}-e_i,
&& [\text{By Definition}]
\end{aligned}
```

where the final index wraps to the next period.

Let $q$ be the next prime after $p$. Before installing filter $p$, the window
relevant to the next stage is

```math
\begin{aligned}
W(p,q)
&=\{x:q\le x\text{ and }x+2<q^2\}.
&& [\text{By Definition}]
\end{aligned}
```

The strict upper endpoint is essential: $q^2$ is composite but has no prime
factor smaller than $q$.

For a longer chain ending at a prime $Q$, write

```math
\begin{aligned}
P_Q &= \prod_{r<Q}r,\\
W_Q &= \{x:Q\le x\text{ and }x+2<Q^2\}.
\end{aligned}
```

---

## 3. Complete Survivor Gap Cycles

For every prime $p$, the installed filters are exactly the primes smaller
than $p$. One complete stage period is obtained by taking the integers in a
length-$M_p$ interval that avoid all residue class $0$ multiples of those
earlier primes:

```math
\begin{aligned}
E_p
&=\{x\in[0,M_p):\forall r<p,\ r\text{ prime}\Longrightarrow x\not\equiv0\pmod r\}.
&& [\text{Survivor Period}]
\end{aligned}
```

Sorting these survivors and taking adjacent cyclic differences produces the
finite gap list for the stage. This is the list of steps that walks through
exactly the values avoiding every multiple of every previous prime, and then
repeats modulo $M_p$.

This setup is the finite object whose 2-gaps are counted in §5.2. The count is
global over one complete period; it is separate from the later question of
where those 2-gaps land inside a particular square-safe window.

---

## 4. Filtering Copies Or Merges Old Gaps

Filtering removes accepted values without changing the order of the values
that remain. Consequently, two consecutive survivors were either already
consecutive or had a consecutive block of old accepted values between them.
The first case copies one old gap. The second merges the old gaps spanning the
removed block.

### 4.1 Copied Gap

Suppose $e_i$ and $e_{i+1}$ both survive. Their new difference is unchanged:

```math
\begin{aligned}
g'_i
&=e_{i+1}-e_i
&& [\text{By Definition}]\\
&=g_i.
&& [\text{Substitution}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

### 4.2 Merged Gap

Suppose $e_i$ and $e_j$ survive while $e_{i+1},\ldots,e_{j-1}$ are removed. The
new gap telescopes across the old adjacent gaps:

```math
\begin{aligned}
g'_{i,j}
&=e_j-e_i
&& [\text{By Definition}]\\
&=\sum_{k=i}^{j-1}(e_{k+1}-e_k)
&& [\text{Telescoping}]\\
&=\sum_{k=i}^{j-1}g_k.
&& [\text{Substitution}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

The copy-or-merge rule is structural. It constrains how gaps change but does
not, by itself, prove that any chosen gap value occurs locally.

---

## 5. Stable Absence And Exact Global Presence

Two complementary properties describe the complete cyclic population of
2-gaps. Copy-or-merge shows that global absence would be permanent. CRT shows
that the canonical complete period never reaches that absent state.

### 5.1 Absence Of 2-Gaps Is Stable

After filter $2$ is installed, every accepted value is odd, so every old gap is
positive and even. If no old gap equals $2$, then every old gap is at least
$4$. A copied gap is at least $4$, while a merged gap is a sum of at least two
positive even gaps. Neither branch can produce $2$.

```math
\begin{aligned}
2\notin G_k
&\Longrightarrow
\forall g\in G_k,\ g\ge4
&& [\text{Positive Even Gaps}]\\
&\Longrightarrow
\forall g'\in G_{k+1},\ g'\ge4
&& [\text{Copy Or Merge}]\\
&\Longrightarrow
2\notin G_{k+1}.
&& [\text{Q.E.D.}]
\end{aligned}
```

### 5.2 Exact Non-Recursive Global Count

For one complete period modulo $M_p$, a cyclic 2-gap start $x$ must make both
$x$ and $x+2$ coprime to every installed prime. Modulo $2$, exactly one class
is possible. For every odd prime $r<p$, exactly two classes are forbidden:
$0$ and $-2$. The remaining choices combine independently by CRT.

```math
\begin{aligned}
G_2(p)
&=1\cdot
\prod_{\substack{3\le r<p\\r\text{ prime}}}
\left(r-2\right)
&& [\text{One Local Count Per Prime}]\\
&=\prod_{\substack{3\le r<p\\r\text{ prime}}}
\left(r-2\right).
&& [\text{By CRT}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

Every factor is positive. Therefore every odd stage has at least one cyclic
2-gap in its complete period. This global positivity is exact and
non-recursive.

### 5.3 Boundary

Global presence does not imply safe-window presence. The complete period grows
primorially, while a square-safe window grows quadratically in its defining
prime. The global theorem rules out complete-cycle extinction; it does not locate any
2-gap in $[p,p^2)$.

---

## 6. Repeated Copies And Exact Batch Survival

Repetition does provide exact distribution information. It does not place
copies arbitrarily. For one old cyclic 2-gap $(a,a+2)$ modulo an old period
$M$, its absolute copies are

```math
\begin{aligned}
(x_j,x_j+2)=(a+jM,a+2+jM).
\end{aligned}
```

### 6.1 One New Prime Forbids Two Copy Classes

Let $r>2$ be a new prime with $\gcd(M,r)=1$. Filter $r$ destroys copy $j$
exactly when one endpoint is $0$ modulo $r$. Since $M$ is invertible modulo $r$,
the two conditions have unique copy-index solutions:

```math
\begin{aligned}
a+jM\equiv0\pmod r
&\Longleftrightarrow
j\equiv-aM^{-1}\pmod r,
&& [\text{Multiplicative Inverse}]\\
a+2+jM\equiv0\pmod r
&\Longleftrightarrow
j\equiv-(a+2)M^{-1}\pmod r.
&& [\text{Multiplicative Inverse}]
\end{aligned}
```

The classes are distinct because equality would imply $2=0$ modulo $r$.
Therefore every complete block of $r$ copy indices has exactly two destroyed
copies and $r-2$ survivors. In any $N$ consecutive indices, each forbidden
class occurs at most $\lceil N/r\rceil$ times, giving

```math
\begin{aligned}
D_r(N)
&\le2\left\lceil\frac Nr\right\rceil.
&& [\text{Two Residue Classes}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

### 6.2 An Arbitrary Finite Batch

Let $\mathcal R$ be a finite set of distinct new odd primes, none dividing $M$, and set

```math
\begin{aligned}
B=\prod_{r\in\mathcal R}r.
\end{aligned}
```

Each prime leaves $r-2$ allowed copy-index classes. CRT combines one allowed
choice for each prime into one class modulo $B$. Thus the number of surviving
classes in one complete batch period is

```math
\begin{aligned}
S(\mathcal R)
&=\prod_{r\in\mathcal R}(r-2).
&& [\text{By CRT}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

If the old complete period contains $G$ cyclic 2-gaps, the complete batched
period contains exactly

```math
\begin{aligned}
G_{\mathrm{after}}
&=G\prod_{r\in\mathcal R}(r-2).
&& [\text{Sum Over Old 2-Gaps}]
\end{aligned}
```

This one-shot count automatically handles overlaps and is independent of the
order assigned to the filters.

### 6.3 What The Batch Does Not Prove

The combined modulus $B$ can be much longer than the eligible local run of
copy indices. Exact proportional survival over a complete $B$-block does not
force an allowed index in every shorter interval. Distinct primes can cover
different positions of one finite run even though every prime leaves most
indices untouched.

The unresolved local question is therefore not whether the copies have a
distribution. They do. It is how long a consecutive run can be covered by the
union of all known forbidden classes.

---

## 7. Rotation Preserves Global Multiplicity, Not Placement

Rotation chooses a different origin for the same finite cyclic gap list. For

```math
\begin{aligned}
G=(g_0,g_1,\ldots,g_{T-1}),
\end{aligned}
```

rotation by $j$ is a permutation of the index set. Therefore, for every gap
value $d$, its cyclic multiplicity is unchanged:

```math
\begin{aligned}
\#\{i:g_i=d\}
&=\#\{i:\operatorname{rot}_j(G)_i=d\}
&& [\text{Rotation Is A Bijection}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

Rotation can change which gap follows the first displayed value and whether a
cyclic gap crosses the end of one linear rendering. It cannot destroy, merge, or
create a cyclic 2-gap.

An absolute window such as $[q,q^2)$ is tied to numerical coordinates, not
only cyclic indices. Rotation is therefore not a random reshuffle and does not
imply that every short absolute window receives its proportional share.

---

## 8. Square-Safe 2-Gaps Are Twin Primes

Let $q$ be prime and suppose $n$ satisfies

```math
\begin{aligned}
q\le n<q^2,
\qquad
\gcd(n,P_q)=1.
\end{aligned}
```

If $n$ were composite, it would have a prime divisor $r\le\sqrt n<q$. That
prime would divide $P_q$, contradicting the coprimality condition. Hence $n$
is prime.

```math
\begin{aligned}
n\text{ composite}
&\Longrightarrow
\exists r\text{ prime}:r\mid n\land r\le\sqrt n
&& [\text{Small Prime Divisor}]\\
&\Longrightarrow
r<q
&& [n<q^2]\\
&\Longrightarrow
r\mid P_q
&& [\text{By Definition}]\\
&\Longrightarrow
\gcd(n,P_q)>1,
&& [\text{Contradiction}]\\
\therefore\quad n&\text{ is prime}.
&& [\text{Q.E.D.}]
\end{aligned}
```

Applying the argument to both endpoints proves

```math
\begin{aligned}
q\le x,\quad x+2<q^2,\quad
\gcd(x(x+2),P_q)=1
\Longrightarrow
x\text{ and }x+2\text{ are prime}.
\end{aligned}
```

This theorem certifies a survivor. It does not prove that the safe window
contains one.

---

## 9. The Sharp One-Transition Survival Criterion

During the transition from prime $p$ to the next prime $q$, only accepted values
inside $[q,q^2)$ can destroy safe-window 2-gaps. A multiple of $p$ outside this
window is irrelevant to this local certification problem, and a multiple that
was already removed by a smaller prime is not an accepted value of the current
stage. The useful count is therefore the number of accepted multiples of $p$
inside $[q,q^2)$.

Let $p\ge5$ be the new filter and $q$ the next prime after $p$. Define

```math
\begin{aligned}
K&=\left\lfloor\frac{q^2-1}{p}\right\rfloor,\\
A(p,q)&=\pi(K)-\pi(p-1).
\end{aligned}
```

### 9.1 Exact Accepted Strikes

A multiple of $p$ in $[q,q^2)$ has the form $pk$. It was accepted by every old
filter exactly when $k$ has no prime divisor below $p$. Bertrand's postulate
gives $q<2p$, so

```math
\begin{aligned}
K
&<\frac{q^2}{p}
<4p
\le p^2.
\end{aligned}
```

If such a $k<p^2$ were composite, it would have a prime divisor below $p$.
Therefore the accepted multipliers are exactly the primes $k$ with $p\le k\le K$,
and their number is $A(p,q)$.

```math
\begin{aligned}
\#\{\text{accepted multiples of }p\text{ in }[q,q^2)\}
&=\#\{k:p\le k\le K,\ k\text{ prime}\}
&& [\text{Accepted Multiplier Characterization}]\\
&=\pi(K)-\pi(p-1)
&& [\text{By Definition Of }\pi]\\
&=A(p,q).
&& [\text{Q.E.D.}]
\end{aligned}
```

### 9.2 One Strike Destroys At Most One 2-Gap

After filters $2$ and $3$ are installed, every 2-gap start is $5$ modulo $6$.
Two 2-gaps cannot share an endpoint: among $x,x+2,x+4$, one value is divisible
by $3$. Thus one removed accepted value is an endpoint of at most one 2-gap.

```math
\begin{aligned}
(x,x+2)\text{ and }(x+2,x+4)\text{ both accepted}
&\Longrightarrow
x,x+2,x+4\not\equiv0\pmod3
&& [\text{Acceptance}]\\
&\Longrightarrow
\bot,
&& [\text{One Of Three Is }0\pmod3]\\
\therefore\quad
\text{one removed value destroys at most one 2-gap}.
&& [\text{Q.E.D.}]
\end{aligned}
```

### 9.3 Sufficient Survival Threshold

Let $G_{\mathrm{local}}(p,q)$ be the number of pre-filter 2-gaps with both
endpoints in $[q,q^2)$. Since filter $p$ removes exactly $A(p,q)$ accepted
values and each removal destroys at most one 2-gap,

```math
\begin{aligned}
G_{\mathrm{surviving}}(p,q)
&\ge G_{\mathrm{local}}(p,q)-A(p,q)
&& [\text{Destruction Capacity}]\\
G_{\mathrm{local}}(p,q)>A(p,q)
&\Longrightarrow
G_{\mathrm{surviving}}(p,q)>0.
&& [\text{Integer Positivity}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

This criterion is conditional: it proves survival from a local abundance
hypothesis, but it does not prove that the hypothesis holds.

---

## 10. Finite Perfect Scenarios

An infinite proof does not need every stage to satisfy the sharp threshold. It
is enough that rare finite scenarios occur at unbounded coordinates. One old
2-gap need only survive the finite set of filters required to reach one
square-safe certification stage.

Choose an initial prime $p$, its modulus $M_p$, and a cyclic seed $(a,a+2)$.
For a later prime $Q>p$ (in the sense of §2's longer chain, not necessarily
the immediate successor of $p$), the copy indices whose endpoints lie in the
safe window are

```math
\begin{aligned}
I(a,M_p,Q)=
\left[
\left\lceil\frac{Q-a}{M_p}\right\rceil,
\left\lfloor\frac{Q^2-3-a}{M_p}\right\rfloor
\right]\cap\mathbb Z.
\end{aligned}
```

Let the transition batch be

```math
\begin{aligned}
\mathcal R(p,Q)=\{r:r\text{ prime and }p\le r<Q\}.
\end{aligned}
```

For each $r$ in the batch, copy index $j$ must avoid

```math
\begin{aligned}
j&\equiv-aM_p^{-1}\pmod r,\\
j&\equiv-(a+2)M_p^{-1}\pmod r.
\end{aligned}
```

Define the batch-allowed set $\mathcal A(a,M_p,p,Q)$ by those avoidance
conditions.
The complete finite certificate is

```math
\begin{aligned}
I(a,M_p,Q)\cap\mathcal A(a,M_p,p,Q)
&\ne\varnothing.
&& [\text{Perfect-Scenario Certificate}]
\end{aligned}
```

If $j$ lies in this intersection, $x=a+jM_p$ and $x+2$ survive every prime
filter below $Q$ and lie strictly below $Q^2$. Section 8 certifies both as
prime. When the sieve sequence later reaches the stage beginning at $x$, the
next accepted value is $x+2$, since $x+1$ is even. Thus the first gap is $2$.

```math
\begin{aligned}
j\in I\cap\mathcal A
&\Longrightarrow
\gcd(x(x+2),P_Q)=1
&& [\text{Batch Compatibility}]\\
&\Longrightarrow
x,x+2\text{ are prime}
&& [\text{Safe-Window Certification}]\\
&\Longrightarrow
\text{the stage beginning at }x\text{ begins with gap }2.
&& [\text{Consecutive Prime Starts}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

One certificate proves one twin-prime pair. Infinitely many pairs require an
unbounded family of certificates. Success at every stage, positive density, and
survival of one immortal seed are all stronger than necessary.

The infinite target is an unbounded family of such successful finite
certificates.

---

## 11. The Fixed-Seed Scale Conflict

One proposed restriction keeps the whole consecutive prime chain (ending at
the general later prime $Q$ from §2, not a single next-prime step) below the
initial square horizon:

```math
\begin{aligned}
Q<p^2.
\end{aligned}
```

This limits the numerical length of the chain, but it conflicts with using
many repeated copies of one fixed seed inside the final safe window. By the
prime number theorem in Chebyshev-theta form,

```math
\begin{aligned}
\log M_p
&=\sum_{r<p}\log r
\sim p.
\end{aligned}
```

Hence $M_p=\exp((1+o(1))p)$. Meanwhile $Q<p^2$ implies $Q^2<p^4$. Therefore

```math
\begin{aligned}
\frac{M_p}{Q^2}
&>\frac{\exp((1+o(1))p)}{p^4}
\longrightarrow\infty,
&& [p\longrightarrow\infty]\\
\therefore\quad M_p&>Q^2
&& [\text{For All Sufficiently Large }p].
\end{aligned}
```

For all sufficiently large scenarios satisfying $Q<p^2$, one fixed residue
class modulo $M_p$ occurs at most once in $[Q,Q^2)$. Its exact global
repetition frequency therefore cannot force local placement.

This is not a disproof of finite perfect scenarios. It says that a proof cannot
simultaneously rely on a short chain under $p^2$ and on many local copies of
one fixed seed. A viable average must instead range over seed residues, use a
much earlier seed and a longer filter chain, average over final primes, or find
another bilinear variable.

---

## 12. The Exact Open Boundary

The proved complete-period density does not become a local lower bound without
an error estimate. Define the fully filtered starts in a finite window $W$ by

```math
\begin{aligned}
\mathcal S_Q(W)
=\{x\in W:\gcd(x(x+2),P_Q)=1\}.
\end{aligned}
```

CRT gives the complete-period density

```math
\begin{aligned}
\delta_Q
=\frac12
\prod_{\substack{3\le r<Q\\r\text{ prime}}}
\left(1-\frac2r\right).
\end{aligned}
```

For the safe window $W_Q$, write the exact identity

```math
\begin{aligned}
|\mathcal S_Q(W_Q)|
=|W_Q|\delta_Q+E_Q,
\end{aligned}
```

where $E_Q$ is the short-window discrepancy. Positivity would follow from

```math
\begin{aligned}
E_Q>-|W_Q|\delta_Q.
\end{aligned}
```

No such general bound is proved here. The main term is not itself a lower
bound.

### 12.1 Equivalent Covered-Run Form

For one seed $(a,a+2)$, every future prime supplies two known forbidden
copy-index classes. Let $C$ be the union of those classes over the batch. The
local question is equivalent to asking how long a consecutive interval can be
contained in $C$.

```math
\begin{aligned}
\operatorname{coverRun}(C)
=\max\{|J|:J\text{ is consecutive and }J\subseteq C\}.
\end{aligned}
```

If an eligible copy-index interval is longer than this maximum covered run, it
contains a survivor. The missing theorem is a bound strong enough for an
unbounded family of eligible scenarios.

### 12.2 What Does Not Follow

The following implications are invalid without additional hypotheses:

```math
\begin{aligned}
\text{positive complete-period density}
&\not\Longrightarrow
\text{positive safe-window count},\\
\text{rotation}
&\not\Longrightarrow
\text{random local placement},\\
\text{two forbidden classes per prime}
&\not\Longrightarrow
\text{no finite run is fully covered},\\
\text{many global 2-gaps}
&\not\Longrightarrow
\text{one fixed seed has many local copies}.
\end{aligned}
```

These are theorem boundaries, not a history of failed experiments.

### 12.3 The Extremal Global-Count Threshold

A global count can force a local survivor, but only when it is so large that
all 2-gaps cannot fit outside the safe window. After filters $2$ and $3$, every
2-gap start is $5$ modulo $6$. One complete old period therefore has $M_p/6$
possible start slots.

Let

```math
\begin{aligned}
C(q)
=\left\lfloor\frac{q^2-8}{6}\right\rfloor
-\left\lfloor\frac{q-6}{6}\right\rfloor,
\end{aligned}
```

the number of eligible $5$ modulo $6$ starts in the next safe window. Assuming
the window maps injectively modulo $M_p$, its complement has only
$M_p/6-C(q)$ possible 2-gap slots. Therefore

```math
\begin{aligned}
G_{\mathrm{local}}(p,q)
&\ge
G_{\mathrm{global}}(p)-\left(\frac{M_p}{6}-C(q)\right)
&& [\text{Outside-Slot Capacity}]\\
G_{\mathrm{global}}(p)
&>\frac{M_p}{6}-C(q)+A(p,q)
&& [\text{Sufficient Global Threshold}]\\
&\Longrightarrow
G_{\mathrm{local}}(p,q)>A(p,q)
&& [\text{Substitution}]\\
&\Longrightarrow
G_{\mathrm{surviving}}(p,q)>0.
&& [\text{Sharp Local Threshold}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

This is a rigorous count-only bridge, but it is generally impractical. The
known exact global count has order roughly $M_p/\log^2(p)$, while the outside
capacity is close to $M_p/6$ once the primorial dominates the window. The
theorem therefore explains quantitatively why global abundance needs
additional positional information.

---

## 13. Recent Prime-Producing Sieve Research

Ford and Maynard study nonnegative sequences whose difference from a comparison
model satisfies Type I and Type II estimates. Type I controls divisibility
averages over many factor scales. Type II controls bilinear sums against
arbitrary bounded coefficient sequences. Their framework proves that a
substantial Type II range is genuinely necessary to guarantee a nontrivial
prime lower bound; very strong Type I information alone can still be
consistent with a sequence containing no primes.

The Sieve Sequence's exact residue and CRT formulas are algebraic input for a
possible Type I analysis. They are not yet a Ford-Maynard Type I theorem over
the required short intervals, because the accumulated discrepancy norm has
not been bounded. No arbitrary-coefficient Type II estimate is currently
proved for the perfect-scenario weights.

A natural endpoint weight at scale $X=q^2$ is

```math
\begin{aligned}
A_q(n)
=\mathbf1_{\gcd(n(n+2),P_q)=1}.
\end{aligned}
```

On primes $n$ strictly below $q^2-2$, positivity of the weighted prime sum

```math
\begin{aligned}
\sum_{\substack{n\text{ prime}\\q^2/2<n\le q^2-3}}A_q(n)>0
\end{aligned}
```

would produce a twin-prime pair. Establishing the necessary Type I/II
hypotheses for this or a non-circular comparison weight is itself the hard
problem.

Green and Sawhney's accepted work on prime values of $p^2+nq^2$ demonstrates a
modern successful Type II strategy using extra algebraic variables, number-
field factorization, and Gowers-norm machinery. Those structural inputs do not
automatically exist for the affine pair $(x,x+2)$. Their result is therefore a
methodological guide, not a theorem that transfers to the present problem.

The actionable analytic target is:

```text
Define a non-circular averaged perfect-scenario weight, prove a genuine
short-window Type I estimate and a sufficiently long arbitrary-coefficient
Type II estimate, then test those proved ranges against the Ford-Maynard
lower-bound criteria.
```

---

## 14. Finite Certificate Search

The open infinitude theorem does not prevent finite generation. For a chosen
prime $Q$ (again the general later-prime endpoint of §2, not a single
next-prime step), initialize all starts

```math
\begin{aligned}
J_Q=\{Q,Q+1,\ldots,Q^2-3\}.
\end{aligned}
```

For every prime $r<Q$, remove starts in the two classes

```math
\begin{aligned}
n\equiv0\pmod r,
\qquad
n\equiv-2\pmod r.
\end{aligned}
```

Every returned $n$ satisfies the square-safe certificate and is therefore a
genuine twin-prime start. For any chosen earlier stage $p$, its ancestry can be
reconstructed using

```math
\begin{aligned}
a&=n\bmod M_p,\\
j&=\frac{n-a}{M_p}.
\end{aligned}
```

This is a finite certificate search, not an infinitude theorem. Exhaustive
filtering in one chosen window terminates and returns exactly the starts in
that window whose two endpoints avoid every prime filter below $Q$. A returned
start has a complete modular certificate; an empty run only says that this
particular window contains no such certificate.

The same data can also be read through sieve-sequence ancestry by recording the
residue $a$ and copy index $j$. Comparing the direct endpoint filter with this
ancestry view measures the local discrepancy between complete-period counts and
short-window placement.

---

## 15. Boundary

The complete-period theory gives exact structure: survivor gaps are copied or
merged, 2-gaps exist in every full period, each new odd prime forbids two
copy-index classes for a repeated 2-gap, and CRT counts the surviving classes
over any finite batch. A square-safe survivor is a genuine twin-prime
certificate, and one finite certificate can be checked by ordinary modular
conditions.

The missing step is not another complete-period count. The unsolved step is
local placement: showing that square-safe windows contain surviving 2-gaps
beyond every bound, or equivalently proving a short-window discrepancy estimate
strong enough to overcome the forbidden residue classes. The present properties
alone do not prove that such windows always succeed, that finite certificates
occur infinitely often, or that the candidate weights satisfy the Type I/II
estimates needed by prime-producing sieve methods.

---

## 16. Conclusion

For any prime $p$, the Sieve Sequence has a finite cyclic gap list whose
repetition generates exactly the integers not divisible by primes smaller than
$p$. This matters because an infinite survivor sequence can be studied through
one finite period. The proof is by periodicity modulo the primorial $M_p$: once
the accepted residues in one period are known, the same residues repeat in
every period.

That finite period contains many cyclic 2-gaps. CRT proves a lower bound of
$\prod(r-2)$ over odd primes $r<p$, because each odd prime removes at most
two endpoint residue classes from a possible 2-gap. This matters because
2-gaps are not a fragile local accident of the first few terms; they are forced
through the complete-period residue structure.

Filtering explains how those gaps evolve. A gap is copied when both values
around it survive; otherwise adjacent gaps are merged. For each new prime $r$,
at most two copies of an old 2-gap are removed in every block of $r$ copies,
so full-period survival can be counted by CRT across any finite batch of new
filters. This proves growth in the absolute number of full-period 2-gaps while
also showing why their relative density decreases.

The final boundary is local. Complete-period survival does not imply that a
2-gap appears in a particular square-safe window. Even though the infinite
generator contains infinitely many 2-gaps, the properties in this article do
not prove that infinitely many of them reach windows where both endpoints are
certified prime. That local placement problem is the remaining obstruction
between global gap survival and infinitely many twin-prime certificates.

---

## References

1. Mata, T. H. (2026). [Formal Verification of Sieve Sequence Stages and Their
   Transitions](sieve-sequence-v2.md).
2. Kevin Ford and James Maynard (2024). [On the theory of prime producing
   sieves](https://arxiv.org/abs/2407.14368).
3. Ben Green and Mehtaab Sawhney (2024, revised 2026). [Primes of the form
   p^2+nq^2](https://arxiv.org/abs/2410.04189). Accepted for publication in
   *Acta Mathematica*.
4. Hardy, G. H. and Wright, E. M. (1979). *An Introduction to the Theory of
   Numbers*, 5th edition. Oxford University Press.
