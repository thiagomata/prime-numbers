# Empirical Evidence for Capacity-Density Candidates

**Status:** Finite measurements over 53 future heads and 1,837 conditioned
filter layers. No universal density claim is mathematically proved here.

## Scope

This note tests two candidate conditions suggested by the proved local-count
threshold:

- [Seven-Layer Capacity Floor](
  ../../candidates/seven-layer-capacity-floor.md
  );
- [Redundant Close-Pair Capacity](
  ../../candidates/redundant-close-pair-capacity.md
  ).

The measured future heads are every prime

```text
17 <= Q <= 251
```

together with

```text
307, 401, 503, 701, 997.
```

This gives 53 heads and 1,837 applicable prime-filter layers `5<=r<Q`.

The sweep used the population definitions from
`candidates/analysis/lib_lineage.py`. It ran in memory and did not write a new
CSV. At each head, the `[Q,Q^2)` population was initialized after filters
`2,3`, then conditioned incrementally by each next prime filter. This is the
actual Reading-A population at every layer, not a frozen initial population.

## Metrics

Let

```math
L_Q=Q^2-Q-3
```

and let `G_r(W_Q)` count complete 2-gaps before filter `r`. The normalized
capacity ratio is

```math
\rho(Q,r)
=
\frac{(G_r(W_Q)-1)(2r-2)}{L_Q}.
```

The proved property
[A Local Count Forces the k=2 Shot-Capacity Premise](
../../properties/sieve-sequence/local-count-forces-k2-shot-capacity.md
) gives the exact implication

```math
\rho(Q,r)>1
\quad\Longrightarrow\quad
\text{candidate #14's }k=2\text{ premise holds at layer }r.
```

The early inequality is no longer only empirical. The
[Exact Seven-Layer Capacity Floor](
../../properties/sieve-sequence/exact-seven-layer-capacity-floor.md
) proves `rho(Q,7)>1` for every integer `Q>=17`. The present sweep still tests
the open later-layer comparison `rho(Q,r)>=rho(Q,7)`.

For redundancy, write the local starts as

```math
x_1<x_2<\cdots<x_N.
```

The sweep records:

```text
P(Q,r)   consecutive indices i with x_(i+1)+2-x_i < 2r
D(Q,r)   maximum number of those qualifying edges sharing no start
B_2(Q,r) canonical length-(2r-2) blocks containing at least two starts
```

Equivalently, let `R_i` be the sum of all intervening non-2 gaps between the
2-gaps starting at `x_i` and `x_(i+1)`. Then

```math
x_{i+1}=x_i+2+R_i
```

and therefore

```math
P(Q,r)
=
\#\{i:R_i<2r-4\}.
```

This is the true 2-focused compressed-separator observable, not the collection
of individual non-2 gap values.

The proved one-layer relations are

```math
B_2(Q,r)\le D(Q,r)\le P(Q,r)
```

and

```math
G_{r^+}(W_Q)\ge D(Q,r).
```

The last inequality uses maximum-matching disjointness: every selected pair
leaves one survivor, and different selected pairs leave distinct survivors.

The proved
[Local Density Forces a Close-Pair Matching Bound](
../../properties/sieve-sequence/local-density-forces-close-pair-matching.md
) supplies two further observables. Define

```math
d_r=2r-2,
\qquad
\Delta_r=6\left\lceil\frac{d_r}{6}\right\rceil
```

and

```math
\begin{aligned}
P_{\mathrm{alg}}(Q,r)
&=
\max\left(
0,
\left\lceil
\frac{\Delta_r(G_r(W_Q)-1)-L_Q}{\Delta_r-6}
\right\rceil
\right),\\
D_{\mathrm{alg}}(Q,r)
&=
\left\lceil\frac{P_{\mathrm{alg}}(Q,r)}2\right\rceil.
\end{aligned}
```

These are deterministic lower bounds:

```math
P(Q,r)\ge P_{\mathrm{alg}}(Q,r),
\qquad
D(Q,r)\ge D_{\mathrm{alg}}(Q,r).
```

For two consecutive incoming primes `r<s`, let `H_r` be the number of local
2-gap starts destroyed by filter `r`. The proved transition bounds are

```math
P(Q,s)\ge P(Q,r)-2H_r,
\qquad
D(Q,s)\ge D(Q,r)-H_r.
```

They are proved in
[Filtering Attrition Bound for Raw Close Pairs](
../../properties/sieve-sequence/filtering-attrition-bound-raw-close-pairs.md
) and
[Filtering Attrition Bound for Close-Pair Matchings](
../../properties/sieve-sequence/filtering-attrition-bound-close-pair-matching.md
).

The transition sweep also classifies every next-layer qualifying edge as:

```text
retained       an old qualifying adjacent edge whose endpoints survive
reconstructed  a short new adjacency spanning one or more destroyed starts
expanded       an adjacency admitted only because the threshold grows from r to s
```

These classes are disjoint and sum exactly to `P(Q,s)`.

## Validation Gates

Before the sweep, the unchanged lineage test suite passed under the
repository-local analysis environment. It checks exact small-period shot
spans, stable small-`k` inputs, Reading-A population transitions, a hand-derived
Q17 layer, and existing candidate margins.

The new sweep enforced at every layer:

```text
destroyed + surviving == G_r(W_Q)
B_2(Q,r) <= D(Q,r)
P_alg(Q,r) <= P(Q,r)
D_alg(Q,r) <= D(Q,r)
P(Q,r) == count_i(R_i < 2r-4)
post-filter starts are a subset of pre-filter starts
retained + reconstructed + expanded == P(Q,s)
P(Q,s) >= P(Q,r) - 2H_r
D(Q,s) >= D(Q,r) - H_r
```

Across all 1,837 layers there were:

```text
0 population-identity failures
0 block-to-matching bound failures
0 algebraic raw-edge bound failures
0 algebraic disjoint bound failures
0 separator-threshold identity failures
0 start-subset failures
0 transition-decomposition failures
0 raw attrition-bound failures
0 matching attrition-bound failures
```

Two independent cross-checks also passed:

1. fresh recomputation matched all 4 applicable stored Q17 rows and all 23
   applicable stored Q101 rows;
2. the direct period-30 formula matched `G_7(W_Q)` at all 53 heads.

Before filter `7`, the complete 2-gap starts are exactly the integers
congruent to

```text
11, 17, or 29 modulo 30
```

inside the eligible start interval. This gives an independent finite-period
calculation of the proposed bottleneck layer.

## 1. Seven-Layer Capacity Floor

For every measured head:

```math
\rho(Q,r)>1
\qquad
\text{at every layer }5\le r<Q.
```

There were:

```text
0 layers with rho <= 1
0 heads violating rho(Q,r) >= rho(Q,7)
```

Most decisively, the attaining layer was the same in every chain:

```text
argmin_r rho(Q,r) = 7
```

for all 53 measured heads.

The observed `r=7` range was

```math
1.132743
\le
\rho(Q,7)
\le
1.199989.
```

Selected exact finite values are:

| `Q` | `G_7(W_Q)` | `rho(Q,7)` | distance below `6/5` |
|---:|---:|---:|---:|
| 17 | 27 | 1.159851 | 0.040149 |
| 101 | 1,010 | 1.199168 | 0.000832 |
| 251 | 6,275 | 1.199866 | 0.000134 |
| 503 | 25,250 | 1.199938 | 0.000062 |
| 997 | 99,301 | 1.199989 | 0.000011 |

The convergence to

```math
\frac65=1.2
```

comes from the exact period-30 layer, not from a fitted asymptotic model.
The quotient/remainder argument in the established property proves strict
positivity for every integer `Q>=17`; the table above is only a finite
cross-check of that theorem.

### Interpretation

The finite data strongly reinforces the lower-envelope formulation. It also
confirms that strict stepwise monotonicity is the wrong statement: individual
later transitions sometimes decrease `rho`, but none of the 1,837 measured
layers falls below the early `r=7` floor.

The load-bearing unproved statement is therefore not the period-30 density. It
is propagation of that floor through every later conditioned filter.

## 2. Redundant Close-Pair Capacity

No measured layer was a one-certificate edge case:

```text
0 layers with D(Q,r) = 0
0 layers with B_2(Q,r) = 0
```

The chain minimum

```math
D_{\min}(Q)=\min_{5\le r<Q}D(Q,r)
```

grew from `8` at Q17 to `4,043` at Q997.

| `Q` | layers | `D_min(Q)` | `B_2,min(Q)` | minimum `D/G` |
|---:|---:|---:|---:|---:|
| 17 | 4 | 8 | 4 | 0.296296 |
| 101 | 23 | 100 | 50 | 0.333663 |
| 251 | 51 | 409 | 130 | 0.333386 |
| 503 | 93 | 1,292 | 253 | 0.333307 |
| 997 | 165 | 4,043 | 502 | 0.333330 |

Across every individual measured layer:

```text
minimum disjoint-certificate density D/G = 0.296296
minimum raw qualifying-edge fraction P/(G-1) = 0.307692
```

### Algebraic Lower-Bound Strength

The new density-to-matching theorem gives a positive disjoint-certificate
lower bound at every measured layer:

```text
1,837 / 1,837 layers with D_alg(Q,r) > 0
```

It is also sharp on actual sieve populations:

```text
35 layers with P_alg(Q,r) = P(Q,r)
39 layers with D_alg(Q,r) = D(Q,r)
```

Across all layers, the minimum and median capture ratios are:

| bound capture | minimum | median |
|---|---:|---:|
| `P_alg/P` | 0.448276 | 0.755162 |
| `D_alg/D` | 0.363636 | 0.743869 |

Thus the algebraic theorem explains a substantial fraction of the measured
redundancy without assuming local randomness.

Let

```math
\begin{aligned}
P_{\mathrm{alg,min}}(Q)
&=
\min_{5\le r<Q}P_{\mathrm{alg}}(Q,r),\\
D_{\mathrm{alg,min}}(Q)
&=
\min_{5\le r<Q}D_{\mathrm{alg}}(Q,r).
\end{aligned}
```

Selected headwise minima are:

| `Q` | `P_alg,min(Q)` | `D_alg,min(Q)` | actual `D_min(Q)` |
|---:|---:|---:|---:|
| 17 | 8 | 4 | 8 |
| 101 | 146 | 73 | 100 |
| 251 | 696 | 348 | 409 |
| 503 | 2,339 | 1,170 | 1,292 |
| 997 | 7,597 | 3,799 | 4,043 |

The measured headwise algebraic minimum has one early decrease, from `4` at
Q17 to `3` at Q19, so monotonicity is false even on this finite sample. Its
growth from `4` to `3,799` is strong finite evidence for an unbounded
lower-envelope target, not a proof of one.

### Compressed-Separator Distribution

Across every measured layer, the fraction of compressed separators below the
qualifying threshold satisfies

```math
\frac{\#\{i:R_i<2r-4\}}{G_r(W_Q)-1}
\ge
0.307692.
```

The minimum occurs at `Q=17`, `r=7`, where `8` of `26` separators qualify.
This is the same raw-edge fraction `P/(G-1)` under the proved separator
identity.

Normalize separators by their layer threshold:

```math
Z_i=\frac{R_i}{2r-4}.
```

Using linear-interpolation quantiles independently within each layer, the
largest observed layer quantiles are:

| layer statistic | largest observed value | attaining layer |
|---|---:|---:|
| median `Z` | 1.000000 | `Q=997, r=7` |
| 75th percentile `Z` | 1.204545 | `Q=19, r=13` |
| 90th percentile `Z` | 1.555556 | `Q=997, r=11` |
| 95th percentile `Z` | 1.744828 | `Q=41, r=31` |
| maximum `Z` | 3.523810 | `Q=997, r=23` |

The maximum case is `R_i=148` against threshold `42`. Thus abundant short
separators coexist with a nontrivial long tail; a maximum-separator hypothesis
would be much stronger than the fixed-fraction form of candidate #18.

These are local linear-window statistics. They do not measure candidate #7's
complete-period cyclic maximum or imbalance factor.

### Transition Reconstruction and Attrition

The sweep contains 1,784 consecutive-layer transitions. Reconstruction and
threshold growth are common:

```text
1,652 transitions with at least one reconstructed adjacency
906 transitions with at least one threshold-expanded adjacency
145 transitions where reconstruction plus expansion fully offsets all lost old edges
```

Across the overlapping finite sweep populations, the raw totals are:

```text
463,202 destroyed 2-gap starts
769,991 lost old qualifying edges
88,349 reconstructed qualifying adjacencies
218,307 threshold-expanded qualifying adjacencies
```

These totals are validation summaries over overlapping future-head
experiments, not independent-event probabilities.

The data decisively refutes simple monotone reconstruction:

```text
1,639 failures of P(Q,s) >= P(Q,r)
1,685 failures of D(Q,s) >= D(Q,r)
385 failures of P(Q,s) >= P(Q,r) - H_r
```

The first failure of all three stronger raw/matching ideas occurs at
`Q=17`, `r=5 -> s=7`: `P` falls from `44` to `8`, `D` falls from `22` to
`8`, and `H_r=18`.

The sharp proved fallbacks have zero failures:

```math
P(Q,s)\ge P(Q,r)-2H_r,
\qquad
D(Q,s)\ge D(Q,r)-H_r.
```

Consequently, the data does not justify a new monotone separator-
reconstruction candidate. The short-separator fixed-fraction statement is
already candidate #18, while the distinct monotone forms are empirically
false.

For the headwise minimum disjoint count, a log-log fit gives

```math
D_{\min}(Q)\approx Q^{1.572157}
```

over the measured range, with Pearson correlation approximately

```text
0.998923.
```

This exponent is an empirical finite-range description, not a proved
asymptotic law.

### Interpretation

The measured chains are not surviving through one isolated close pair. Even
at their weakest layers they contain many disjoint `k=2` certificates, and the
minimum redundancy grows strongly with `Q`.

The disjoint density stays near one third over most of the range. This suggests
a more structured target than mere existence:

```math
D(Q,r)\ge c\,G_r(W_Q)
```

for a fixed positive `c`, perhaps below the observed one-third scale.

The canonical block sub-count captures less redundancy than the maximum
matching, especially at large heads, but it remains positive at every measured
layer. Its fixed origin therefore supplies a simpler sufficient statistic,
not a complete account of the close-pair geometry.

## Falsifiers And Next Measurements

For the seven-layer floor:

- any layer with `rho(Q,r)<=1` defeats the count-based `k=2` certificate there;
- any layer with `rho(Q,r)<rho(Q,7)` refutes the proposed floor for that head;
- an eventual downward trend of the headwise minimum toward `1` weakens the
  eventual-uniform form.

For redundancy:

- `D(Q,r)=0` is an actual measured failure of the `k=2` premise;
- bounded `D_min(Q)` weakens the unbounded-redundancy candidate;
- `D/G` trending toward zero weakens a fixed-fraction theorem;
- `B_2=0` refutes only the canonical-block sub-count because a close pair may
  cross a block boundary.

The next high-value empirical extension is a sparse sweep above Q997,
prioritizing heads where the last prime gaps or harmful residue-class excesses
are unusually large. That is more informative than simply densifying the
already uniform small-Q range.

## Boundary

The measurements do not prove the open later-layer or unbounded-growth parts
of either candidate for every sufficiently large head or for infinitely many
heads.

In particular:

- the exact `r=7` density does not imply its preservation after later filters;
- increasing complete-period cluster counts do not place clusters in the
  square window;
- growing finite redundancy does not prove reconstruction of redundancy after
  every future filter;
- the fitted exponent must not be used as an assumption in a proof.

The finite result is narrower and useful: throughout 53 heads and 1,837
conditioned layers, the capacity boundary is never approached, the same
exactly tractable layer is always the weakest one, and local `k=2`
certificates remain highly redundant.
