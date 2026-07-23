# Uniform Local Observable Sampling

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Candidate Hypothesis

Fix an incoming prime `p` and a local window. Let `V` be the `N > 0` old
accepted values used as anchors for complete fixed-radius gap neighborhoods,
and let `D` be the subset hit by the actual deterministic filter. Write

```math
N=|V|,
\qquad
H=|D|.
```

For any bounded local observable `F`, let `F(v)` depend only on a fixed-radius
gap neighborhood around `v`. The candidate is that, for a gap-agnostic class of
such observables and every transition with `H > 0`,

```math
\left|
\frac1H\sum_{v\in D}F(v)
-\frac1N\sum_{v\in V}F(v)
\right|
\le\eta_p\|F\|_\infty.
```

This is a deterministic sampling statement. It says that the neighborhoods
selected for merging do not differ too much from the full local population.
The observable class may include indicators of finite gap words, adjacent-gap
sums, merge arity, cluster width, or large-spacer incidence.

## The Zero-Hit Case

Let `L > 0` count exactly the complete post-3 2-gaps whose two endpoint
anchors belong to `V`; exclude every boundary-crossing gap from both `L` and
the endpoint observable below. If `H = 0`, no old
accepted value in the window is removed, so every one of those gaps survives.
No division by `H` or discrepancy hypothesis is needed in this case.

## Endpoint-Bias Corollary

Now assume `H > 0` and `p > 2`. Define the bounded local observable

```math
c(v)=
\begin{cases}
1,&v\text{ is an endpoint of one of the }L\text{ counted 2-gaps},\\
0,&\text{otherwise}.
\end{cases}
```

After filter `3`, distinct 2-gaps do not share endpoints. Therefore

```math
\sum_{v\in V}c(v)=2L,
\qquad
\|c\|_\infty=1.
```

Because `p > 2`, the filter cannot hit both endpoints of the same 2-gap. If
`K` is the number of local 2-gaps destroyed, then

```math
K=\sum_{v\in D}c(v).
```

Applying the candidate to `c` gives

```math
\frac KH
\le
\frac{2L}{N}+\eta_p.
```

Hence

```math
K
\le
H\left(\frac{2L}{N}+\eta_p\right).
```

## Why The Candidate Is Sufficient

The explicit survival condition is

```math
H\left(\frac{2L}{N}+\eta_p\right)<L.
```

It implies `K < L` and therefore `L-K>0`. At least one square-safe 2-gap
survives.

A concise stronger specialization is bounded multiplicative target bias:

```math
\frac KH
\le
C\frac{2L}{N},
\qquad
2CH<N.
```

Indeed, these inequalities give `K < L`. This endpoint formulation is a
corollary of the general sampling idea, not a separate candidate property.

## Why A Numerical Mean Is Insufficient

Controlling only the average gap value or average merge size tests a single
observable. Equal means can conceal incompatible local structures:

```math
(2,10,2,10)
\qquad\text{and}\qquad
(6,6,6,6)
```

both have mean `6`, but only the first list contains 2-gaps. A filter may have
an ordinary average merge size while concentrating all of its hits on one
exceptional pattern. Survival needs distributional control strong enough to
include the relevant indicator observable.

## Relation To Other Candidates

- [Local pattern-residue balance](local-pattern-residue-balance.md) controls
  the phase of each finite word modulo `p`.
- [Random-like merge survival](random-like-merge-survival.md) compares actual
  marked neighborhoods with a selected probabilistic benchmark.

This candidate instead compares the neighborhoods selected by the actual hit
set directly with the whole deterministic local population.

## Established Inputs

- [2-gap endpoint isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
- [Exact accepted local strikes](../properties/sieve-sequence/exact-accepted-local-filter-strikes.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

Correct total hit density does not imply representative local sampling. The
modular filter may correlate with particular gap words, and a short window can
amplify that alignment. Proving one observable, such as mean gap size, does not
prove the universal statement. A viable theorem must identify a sufficiently
rich observable class and establish an explicit error `eta_p` small enough for
the survival inequality.

## Empirical status (window scale, p to ~19000)

Source: `candidates/analysis/measure_candidates.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantity: `endpoint_bias = |(1/H) sum_D c(v) -
(1/N) sum_V c(v)|`, the bias of the filter's hit set `D` versus the whole anchor
population `V`, on the observable `c(v) = 1` iff `v` is an endpoint of a 2-gap.
The candidate requires "there exists `eta_p` small enough" — existential, so no
finite run can confirm it, only falsify it by showing the bias growing.

| range | min | median | max |
|-------|-----|--------|-----|
| dense (p 5..991) | 0.0003 | 0.22 | 0.77 |
| sparse (p ~1000..19000) | 0.03 | 0.16 | 0.85 |

Trend (log-log, n=186): exponent k = -0.011, Pearson r = -0.052 against log p —
**no detectable trend**. The endpoint bias is flat, confined to roughly
`[0, 0.85]`, regardless of p.

### What this does and does not establish

- **Does:** show the endpoint bias is *flat* and bounded at window scale to
  p~19000. A flat trend is the favorable outcome for an existential tolerance
  claim: any proof invoking #13 may assume an `eta_p` in roughly `[0, 0.85]`
  (constant, not growing with p) without contradicting data. The candidate only
  needs `eta_p` to exist and be small *enough* for the survival inequality; the
  data shows a stable, finite value.
- **Does not:** confirm the existential claim (finite data cannot), nor test
  the *universal* statement over "a sufficiently rich observable class" — only
  the single endpoint observable `c(v)` was measured. The survival inequality
  itself (`H(2L/N + eta_p) < L`) was not checked end-to-end here. Window-scale
  only; does not touch infinitude.
