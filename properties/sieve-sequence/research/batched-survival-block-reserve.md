# A Positive Reserve Across a Growing Block of Sieve Heads

**Status:** Mathematical research proof. The cumulative loss estimate is
unconditional for actual square-rule transitions; positivity throughout the
block is conditional on a positive starting reserve. No infinite survival,
historical novelty, empirical check, or Stainless verification is claimed.

## Meaning

A small loss at each step does not automatically give a small total loss.
Here we bound the total across a specified block directly. The block occupies
a shrinking relative interval of head values, but contains an increasing
number of consecutive primes. A strong enough starting survival certificate
then stays positive throughout the block without repeatedly halving its
guaranteed reserve.

## 1. Setup and Existing Inputs

Let p tend to infinity through prime values. Put

```math
\begin{aligned}
x&=p\left(1+\frac1{(\log p)^3}\right),\\
P&=\max\{r\le x:r\text{ prime}\},\\
p_0=p<p_1<\cdots<p_m&=P,\\
q_i&=\min\{r>p_i^2:r\text{ prime}\},\\
L_i&=L(p_i,q_i),\qquad F_0=F(p,q_0).
\end{aligned}
```

The p_i are all consecutive prime heads in the interval. Transitions are
indexed by 0<=i<m; there is no included transition starting at P.
The [exact transport](batched-survival-propagation-check-2026-10-27.md) and
[combined loss bounds](batched-survival-new-region-bound.md) give actual terms

```math
\begin{aligned}
L_{i+1}&=L_i+A_i+N_i-R_i-J_i,\qquad A_i\ge0,\\
B_i&=|N_i|+R_{{\rm cap},i}+J_i\ge0,\\
L_{i+1}&\ge L_i-B_i,\\
|N_i|&\le\frac{35}{6}(q_{i+1}^2-q_i^2),\\
R_{{\rm cap},i}&\le(q_{i+1}-q_i)/6+1.
\end{aligned}
```

The [filtered shot bound](batched-survival-filtered-shot-bound.md) further gives

```math
\begin{aligned}
J_i&\le3b_i C_i,\\
b_i&=\pi(q_{i+1}-1)-\pi(q_i-1),\\
C_i&=\pi(q_i-1)-\pi(p_{i+1}-1)\le\pi(q_m).
\end{aligned}
```

Here pi counts primes at most its argument. Flat destination steps have
b_i=J_i=N_i=0. The positive benchmark satisfies F_0>=c_0 p^4/(log p)^2
eventually for some c_0>0, by the
[component scale calculation](batched-survival-component-bounds.md).
This is not a lower bound on L_0.

## 2. The Block Contains Increasingly Many Heads

We use de la Vallée Poussin's classical quantitative prime number theorem
(1899), as stated in
[Evertse's notes, equation (1.1), printed p.53](https://pub.math.leidenuniv.nl/~evertsejh/ant18-1.pdf#page=3):

```math
\pi(y)=\operatorname{Li}(y)
       +O\!\left(ye^{-c\sqrt{\log y}}\right),\qquad c>0.
```

The [new-region proof](batched-survival-new-region-bound.md) derives from it
a prime within y/(log y)^k to the right of y for every fixed k, eventually.
The same proof works to the left: the Li increment over
[y-y/(log y)^k,y] dominates both endpoint errors. Taking k=5 yields

```math
\begin{aligned}
P&=x+O\!\left(\frac p{(\log p)^5}\right),\qquad P\le x,\\
P-p&\sim\frac p{(\log p)^3},\\
m=\pi(P)-\pi(p)&=\pi(x)-\pi(p)
 \sim\frac p{(\log p)^4}\longrightarrow\infty.
\end{aligned}
```

The last asymptotic also follows by subtracting quantitative PNT at p and x:
the Li increment is asymptotic to p/(log p)^4 and its errors are smaller.
Thus this result covers an unbounded number of successive transitions as
the starting prime grows, despite P/p tending to1.

The right-interval bound at each p_i squared, uniformly for p_i in [p,P],
gives q_i=p_i squared+O(p squared/(log p)^5). Therefore

```math
q_i\asymp p^2,\qquad
0\le q_m-q_0=O\!\left(\frac{p^2}{(\log p)^3}\right).
```

All constants and thresholds here are independent of the index inside the
block. Uniformity follows because the single quantitative-PNT bound applies
to every sufficiently large argument, and all those arguments are comparable.

## 3. Summing the Actual Loss Budgets

The fresh-region bounds telescope rather than acquire a factor m:

```math
\begin{aligned}
\sum_{i<m}|N_i|
&\le\frac{35}{6}\sum_{i<m}(q_{i+1}^2-q_i^2)\\
&=\frac{35}{6}(q_m^2-q_0^2)
 =O\!\left(\frac{p^4}{(\log p)^3}\right).
\end{aligned}
```

The lost-region caps obey

```math
\sum_{i<m}R_{{\rm cap},i}
\le\frac{q_m-q_0}{6}+m
=O\!\left(\frac{p^2}{(\log p)^3}+p\right).
```

The new-filter intervals [q_i,q_{i+1}) are disjoint. Their prime counts
therefore telescope, too:

```math
\sum_{i<m}J_i
\le3\pi(q_m)\sum_{i<m}b_i
=3\pi(q_m)\bigl(\pi(q_m-1)-\pi(q_0-1)\bigr).
```

Quantitative PNT and q_i comparable to p squared give

```math
\begin{aligned}
\pi(q_m)&=O\!\left(\frac{p^2}{\log p}\right),\\
\pi(q_m-1)-\pi(q_0-1)
&=O\!\left(\frac{q_m-q_0}{\log p}
               +p^2e^{-c'\sqrt{\log p}}\right)\\
&=O\!\left(\frac{p^2}{(\log p)^4}\right),\\
\sum_{i<m}J_i&=O\!\left(\frac{p^4}{(\log p)^5}\right).
\end{aligned}
```

A positive constant c' absorbs the change from log(p squared) to log p.
The Li difference is bounded by interval length divided by the smallest
logarithm in the interval. No asymptotic proportional to interval length is
assumed when that length might vanish.

Combining these estimates with the lower bound on F_0 proves

```math
\boxed{\frac1{F_0}\sum_{i<m}B_i
       =O\!\left(\frac1{\log p}\right)\longrightarrow0.}
```

This controls the actual cumulative nonnegative budget, not merely the
individual ratios B_i/F_i. Since B_i>=0, it bounds every prefix uniformly.

## 4. Conditional Reserve Throughout the Whole Block

For each 0<=j<=m, summing the actual transition inequalities gives

```math
L_j\ge L_0-\sum_{i<j}B_i
    \ge L_0-\sum_{i<m}B_i.
```

Consequently, for each fixed eta>0, every sufficiently late starting prime
satisfies

```math
\boxed{L_0\ge\eta F_0
\quad\Longrightarrow\quad
L_j\ge\frac\eta2 F_0>0\quad\text{for every }0\le j\le m.}
```

The old benchmark F_0 is used throughout. We subtract the block's total
budget once; we do not halve the reserve at each of its m transitions.
Positive L_j certifies an actual twin pair in its destination window, but
these windows can count the same pair repeatedly. Even though m tends to
infinity with p, each individual block is finite and the positive starting
premise has not been proved at unboundedly many starting primes.

The generic [weighted chain lemma](../weighted-collision-energy-chain-survival.md)
already explains how transition inequalities compose in a fixed conditioned
window. This proof instead bounds concrete cumulative costs for moving square
destinations. It makes no historical priority claim for telescoping or PNT.

## 5. The Remaining Renewal Question

The block result does not reproduce the initial positive reserve for a next
block. Repeatedly applying a fixed fraction guarantee could exhaust it, and
our thresholds depend on the chosen fixed reserve. No indefinite concatenation
follows from the displayed estimate alone.

The next target is an actual signed compensation estimate: retain the gains
A_i and the signs of N_i and R_i, and compare their accumulated contribution
with the reserve needed at the next block. A sufficient comparison must then
be proved for real sieve stages. Defining it is not that proof.

Subsequent [higher-order analysis](batched-survival-propagation-check-2026-10-27.md#conditional-retention-through-a-fixed-factor-head-interval)
retains a positive seventh-order certificate across any fixed interval
[p,Cp], possibly from a cubic starting seed. It uses the persistence of
already-certified twins and a small seventh-order penalty. It does not
extend the cubic conclusion of this note to that range or create fresh
twins; renewal remains open. The cubic cumulative-budget proof above
retains its original scope.
