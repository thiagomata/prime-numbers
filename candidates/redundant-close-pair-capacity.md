# Redundant Close-Pair Capacity

**Candidate hypothesis:** Partially proved. Local density is proved to force an
explicit number of raw and disjoint close-pair certificates; uniform or
unbounded growth of that bound through conditioned chains remains unproved
and potentially false.

**Conditional implication:** Mathematically proved from disjoint close-pair
certificates and the exact `k=2` shot spacing.

**Algebraic status:** The density-to-matching conversion and sharp transition
attrition bounds are mathematically proved without a distribution assumption.

**Empirical status:** REINFORCED AT FINITE SCALE — across 53 future heads and
1,837 conditioned layers, the disjoint and canonical-block certificate counts
are always positive. The chain-minimum disjoint count grows from 8 to 4,043.

## Purpose

Candidate #14 requires one local interval containing two 2-gaps but at most one
destructive shot. One certificate is enough for one-layer survival, yet it may
leave only a single 2-gap for the next filter.

This candidate asks whether conditioned square windows contain many disjoint
`k=2` certificates at every layer. Redundancy would quantify how far the local
population is from the extinction boundary and may support a cumulative
hereditary argument.

## Setup

Fix a future prime head `Q` and an incoming prime layer `r>=5`. Write the
complete 2-gap starts currently present in

```math
W_Q=[Q,Q^2)
```

as

```math
x_1<x_2<\cdots<x_N.
```

A consecutive pair index `i` is **qualifying** when

```math
x_{i+1}+2-x_i<2r.
```

Let the raw qualifying-pair count be

```math
P(Q,r)
=
\#\left\{
1\le i<N:
x_{i+1}+2-x_i<2r
\right\}.
```

Two qualifying indices are certificate-disjoint when they share no 2-gap
index. Thus indices `i` and `j` are compatible when `|i-j|>=2`. Let

```math
D(Q,r)
```

be the maximum size of a pairwise compatible set of qualifying indices. Since
the qualifying indices form edges of a path, `D(Q,r)` is the maximum matching
size and is computed exactly by the usual left-to-right greedy selection.

## Compressed-Separator Equivalence

In the accepted gap sequence, keep each 2-gap and compress all intervening
non-2 gaps between two consecutive 2-gaps into their sum. Let `R_i` be that
sum between the 2-gaps starting at `x_i` and `x_{i+1}`.

The first 2-gap ends at `x_i+2`. Traversing the intervening non-2 gaps advances
by `R_i`, so

```math
\begin{aligned}
x_{i+1}
&=x_i+2+R_i
&&[\text{By the Compressed-Separator Definition}],\\
x_{i+1}-x_i
&=R_i+2
&&[\text{Simplification}],\\
x_{i+1}+2-x_i
&=R_i+4.
&&[\text{Add the Second 2-Gap}]
\end{aligned}
```

Therefore the qualifying-pair condition has the exact separator form

```math
\boxed{
x_{i+1}+2-x_i<2r
\quad\Longleftrightarrow\quad
R_i<2r-4.
}
```

Consequently,

```math
\boxed{
P(Q,r)
=
\#\{i:R_i<2r-4\}.
}
```

This is an algebraic identity, not an empirical distribution claim. It makes
the true 2-focused compressed sequence a direct observable for this candidate.

## Canonical Block Sub-Count

Define

```math
d_r=2r-2
```

and partition the allowed start range from the canonical origin `Q` into
half-open blocks

```math
B_j=[Q+jd_r,Q+(j+1)d_r).
```

Let

```math
B_2(Q,r)
=
\#\{j:B_j\text{ contains at least two complete 2-gap starts}\}.
```

Two integer starts in one block differ by at most `d_r-1`, so their enclosure
has length at most

```math
(d_r-1)+2=2r-1<2r.
```

Every multiply occupied block therefore supplies a qualifying pair. Different
blocks supply disjoint start sets, so selecting one pair per such block gives

```math
B_2(Q,r)\le D(Q,r)\le P(Q,r).
```

The block count depends on the declared origin `Q`; the raw and disjoint pair
counts do not.

## One-Layer Redundancy Theorem

At a post-filter-3 layer, every qualifying pair contains two endpoint-disjoint
2-gaps in an interval shorter than

```math
\sigma_r(2)=2r.
```

The interval contains at most one filter-`r` shot, and one shot destroys at
most one of its two 2-gaps. Hence every qualifying pair leaves at least one
survivor.

Choose `D(Q,r)` certificate-disjoint qualifying pairs. Their 2-gap sets are
disjoint, so the survivor supplied by one pair is distinct from the survivor
supplied by every other pair. Therefore

```math
\boxed{
G_{r^+}(W_Q)\ge D(Q,r)\ge B_2(Q,r).
}
```

This is a one-layer lower bound. At the next layer, all three quantities must
be recomputed on the conditioned survivor population.

## Proved Density-to-Matching Bound

Let

```math
L_Q=Q^2-Q-3,
\qquad
\Delta_r
=
6\left\lceil\frac{2r-2}{6}\right\rceil.
```

Because every post-filter-3 start is congruent to `5 modulo 6`, telescoping
the consecutive start differences proves

```math
\boxed{
P(Q,r)
\ge
\max\left(
0,
\left\lceil
\frac{\Delta_r(G_r(W_Q)-1)-L_Q}{\Delta_r-6}
\right\rceil
\right).
}
```

Splitting qualifying path edges by index parity then proves

```math
\boxed{
D(Q,r)\ge\left\lceil\frac{P(Q,r)}2\right\rceil.
}
```

The complete derivation is in
[Local Density Forces a Close-Pair Matching Bound](
../properties/sieve-sequence/local-density-forces-close-pair-matching.md
).

Thus the remaining candidate obligation is not the conversion from density
to redundancy. It is proving that the conditioned-chain lower envelope of

```math
\frac{\Delta_r(G_r(W_Q)-1)-L_Q}{\Delta_r-6}
```

stays positive, grows without bound, or remains a fixed fraction of the local
population along infinitely many selected future heads.

## Proved Transition Attrition Bounds

Let `s` be the next incoming prime after `r`, and let `H_r` be the number of
complete local 2-gap starts destroyed by filter `r`. Filtering introduces no
new 2-gap starts, and the next qualifying threshold is larger. Two sharp
path-deletion theorems therefore give

```math
\boxed{
P(Q,s)\ge P(Q,r)-2H_r
}
```

and

```math
\boxed{
D(Q,s)\ge D(Q,r)-H_r.
}
```

The coefficient `2` in the raw bound is necessary because one deleted start
can remove its two incident qualifying edges. The coefficient `1` in the
matching bound is sufficient because a matching uses each start at most once.
Complete proofs and sharpness examples are in
[Filtering Attrition Bound for Raw Close Pairs](
../properties/sieve-sequence/filtering-attrition-bound-raw-close-pairs.md
) and
[Filtering Attrition Bound for Close-Pair Matchings](
../properties/sieve-sequence/filtering-attrition-bound-close-pair-matching.md
).

These are attrition bounds, not reconstruction theorems. They can become
nonpositive when `H_r` is large and do not establish the candidate's
chain-wide lower envelope.

## Candidate Hypothesis

The minimally useful redundant form is that there is an unbounded function
`R(Q)` and infinitely many future prime heads `Q` such that every prime layer
`5<=r<Q` satisfies

```math
\boxed{
D(Q,r)\ge R(Q).
}
```

A stronger density form, intended as an empirical target, is that some
constant `c>0` satisfies

```math
D(Q,r)\ge c\,G_r(W_Q)
```

at every layer of infinitely many selected chains.

Either form implies candidate #14 because `D(Q,r)>=1` supplies a `k=2`
certificate at every layer. The unbounded form additionally says the chain
stays increasingly far from a one-certificate bottleneck.

## Empirical Measurements

For each `(Q,r)` layer, record:

```text
P(Q,r)                 raw qualifying consecutive pairs
D(Q,r)                 maximum disjoint qualifying pairs
B_2(Q,r)               canonical multiply occupied blocks
P(Q,r)/(G_r(W_Q)-1)    raw edge fraction
D(Q,r)/G_r(W_Q)        disjoint certificate density
B_2(Q,r)/D(Q,r)        block-capture fraction
```

For each future head, report the chain minima

```math
P_{\min}(Q),\qquad
D_{\min}(Q),\qquad
B_{2,\min}(Q),
```

their attaining layers, and their trends with `Q`.

## Empirical Falsifiers

- `D(Q,r)=0` means the actual `k=2` premise fails at that measured layer.
- A bounded or decreasing `D_min(Q)` weakens the unbounded-redundancy form.
- `D(Q,r)/G_r(W_Q)` trending toward zero weakens the fixed-fraction form even
  when one certificate persists.
- `B_2(Q,r)=0` refutes only the canonical-block sufficient sub-count; a
  qualifying pair may cross a block boundary.
- Large `P` with small `D` indicates heavy overlap: many raw pairs reuse the
  same small cluster and do not provide independent redundancy.

No finite positive sweep proves either asymptotic candidate.

## Empirical Results

The expanded in-memory lineage sweep found:

```text
0 layers with D(Q,r) = 0
0 layers with B_2(Q,r) = 0
0 layers where the algebraic raw or disjoint lower bound fails
1,837 / 1,837 layers with a positive proved disjoint lower bound
0 separator-threshold identity failures
0 raw or matching attrition-bound failures
```

over 53 future heads and 1,837 applicable layers. The headwise minimum
disjoint-certificate count grows from

```text
D_min(17) = 8
```

to

```text
D_min(997) = 4,043.
```

Across every individual layer, the smallest measured disjoint density is
approximately `0.296296`; over most of the range it stays near one third. A
finite-range log-log fit gives exponent approximately `1.572157` with
correlation `0.998923`.

The headwise minimum algebraic disjoint bound grows from `4` at Q17 to `3,799`
at Q997. At the layer level, `D_alg(Q,r)=D(Q,r)` on 39 layers, and the median
capture of the actual maximum matching is approximately `74.3869%`. The
sampled headwise minimum has one early decrease, so these data do not support
a universal stepwise-monotonicity claim.

The independent transition sweep covers 1,784 consecutive-layer transitions.
It refutes the natural stronger reconstruction statements:

```text
1,639 failures of P(Q,s) >= P(Q,r)
1,685 failures of D(Q,s) >= D(Q,r)
385 failures of P(Q,s) >= P(Q,r) - H_r
```

Reconstructed adjacencies across deleted starts occur frequently, but they do
not usually replace every lost qualifying edge. Consequently, no monotone
separator-reconstruction candidate is created from these data.

These observations reinforce both the unbounded-redundancy and fixed-fraction
forms, but prove neither. The complete measurement definitions, validation
gates, selected-head table, and falsifiers are recorded in
[Empirical Evidence for Capacity-Density Candidates](
../empirical/sieve-sequence/capacity-density-candidates.md
).

## Limitation

Redundancy at one layer does not itself propagate. Filtering may leave the
guaranteed survivors widely separated, so the next layer still needs a fresh
close-pair analysis. A full proof requires either reconstruction of redundant
local clusters or a cumulative invariant preventing `D(Q,r)` from collapsing
through the chain.

The candidate also does not follow from the increasing complete-period
`(2,4,2)` count. Those global clusters may lie outside the designated square
window.

## Related

- [Bounded pair separation gives the k=2 interval premise](
  ../properties/sieve-sequence/interval-premise-from-pair-existence.md
  ) — supplies the one-certificate survival implication.
- [A local count forces the k=2 shot-capacity premise](
  ../properties/sieve-sequence/local-count-forces-k2-shot-capacity.md
  ) — forces at least one qualifying pair from a total local count.
- [Local density forces a close-pair matching bound](
  ../properties/sieve-sequence/local-density-forces-close-pair-matching.md
  ) — proves the quantitative raw and disjoint certificate bounds.
- [Filtering attrition bound for raw close pairs](
  ../properties/sieve-sequence/filtering-attrition-bound-raw-close-pairs.md
  ) — proves `P_new>=P_old-2H`.
- [Filtering attrition bound for close-pair matchings](
  ../properties/sieve-sequence/filtering-attrition-bound-close-pair-matching.md
  ) — proves `D_new>=D_old-H`.
- [Hereditary shot-spacing capacity](
  hereditary-shot-spacing-capacity.md
  ) — candidate #14, which needs a fresh local capacity certificate at every
  conditioned layer.
