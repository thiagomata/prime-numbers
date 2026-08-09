# Uniform Local Observable Sampling

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Empirical status:** INCONCLUSIVE — absolute-bias diagnostic was window-flat;
the exact one-sided margin `H(2L/N+b₊) < L` is positive in all 1,890 measured
lineage layers across 53 heads, but the candidate still asks for a proof
rather than finite agreement. See "Empirical status (one-sided margin, lineage
experiment)".

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

## Signed Endpoint-Imbalance Corollary

The weighted collision program also needs to distinguish left-endpoint hits
from right-endpoint hits. Let `K_L` and `K_R` be those two destruction counts,
so

```math
K=K_L+K_R,
\qquad
\Delta=K_L-K_R.
```

Define the signed bounded observable

```math
c_-(v)=
\begin{cases}
+1,&v\text{ is the left endpoint of a counted 2-gap},\\
-1,&v\text{ is the right endpoint of a counted 2-gap},\\
0,&\text{otherwise}.
\end{cases}
```

Every counted 2-gap contributes one left and one right endpoint to `V`.
Post-3 endpoint isolation therefore gives

```math
\sum_{v\in V}c_-(v)=0,
\qquad
\|c_-\|_\infty=1.
```

The hit sum is exactly

```math
\sum_{v\in D}c_-(v)=\Delta.
```

Applying the candidate to `c_-` proves

```math
\boxed{
|\Delta|\le H\eta_p.
}
```

Thus the unsigned and signed endpoint observables control two different
errors: total destruction and left/right harmful-class imbalance.

## Exact Bridge To Strike Density

Define the signed unsigned-endpoint sampling bias

```math
\beta
=
\frac KH-\frac{2L}{N}
```

and the accepted-strike density discrepancy

```math
\varepsilon
=
\frac HN-\frac1p.
```

The harmful excess used by candidate #21 is

```math
b
=
K-\frac{2L}{p}.
```

Direct substitution gives

```math
\boxed{
b
=
H\beta+2L\varepsilon.
}
```

Candidate #13 bounds `beta` and `Delta`. In the separate fallback
decomposition, candidate #23 bounds the accepted-strike density error
`epsilon`. Candidate #10 does not supply that theorem: it concerns post-filter
safe-window count discrepancy, not the ratio `H/N` of accepted anchors hit.
Together, endpoint sampling and a future strike-density theorem would control
the two scalar square errors in the orthogonal residue-energy decomposition.
They do not control dispersion among the `p-2` harmless survivor classes;
that is candidate #22.

Property #58, discussed below, proves that restricted candidate #12 can
instead control the two harmful residue deviations directly. That direct
weighted norm is the preferred scalar interface because it retains
correlation lost by the separate #13+#23 composition. Property #66 proves
that this aggregate scalar interface is already terminal at candidate #21's
global allowance: a successful bound forces a positive final population
without a separate harmless-energy premise.

## Sharp Joint Capacity Envelope

Property #56 centers the two endpoint-class hit counts directly:

```math
e_L=K_L-\frac{LH}{N},
\qquad
e_R=K_R-\frac{LH}{N}.
```

Then

```math
H\beta=e_L+e_R,
\qquad
\Delta=e_L-e_R.
```

Let

```math
\ell=\max(0,H+2L-N),
\qquad
u=\min(H,2L),
```

and

```math
\mathcal S
=
\{\ell,u\}
\cup
\left(
\{L\}\text{ if }\ell\le L\le u
\right).
```

The exact worst-case joint scalar energy allowed by endpoint isolation and
class capacities alone is

```math
\boxed{
\max_{s\in\mathcal S}
\left[
\frac{p}{2(p-2)}
\left(
s-\frac{2LH}{N}
\right)^2
+
\frac12\min(s,2L-s)^2
\right].
}
```

Here `s=K_L+K_R` is the total number of endpoint hits. At every candidate
vertex, the worst imbalance concentrates as many hits as possible in one
endpoint orientation.

This is a sharp finite-population theorem, but it does not prove the sampling
hypothesis. It shows precisely why capacity is insufficient: capacity permits
the actual incoming residue class to select an extremal endpoint pattern. A
useful #13 theorem must exclude those vertices through arithmetic correlation
information.

Property #57 shows that this limitation is quantitatively decisive for the
collision program. In a capacity-admissible one-layer configuration, the
filter hits all `L` left endpoints and no right endpoints. Then

```math
|\Delta|=L,
```

so the imbalance cost is `L^2/2`, while candidate #21's entire one-layer
allowance is

```math
\frac{L^2}{2}
\left(1-\frac2p\right)^2
<
\frac{L^2}{2}.
```

Thus endpoint isolation and class capacities cannot certify #21 even before
the other nonnegative energy terms are inserted. This is not a refutation of
candidate #13; it proves that a residue-sampling or correlation theorem is
essential.

Property #58 shows that candidate #13 can also be bypassed as a separate
component if the two harmful start-residue deviations are controlled
directly. Define

```math
\delta_0=K_L-\frac Lp,
\qquad
\delta_{-2}=K_R-\frac Lp.
```

Then

```math
b=\delta_0+\delta_{-2},
\qquad
\Delta=\delta_0-\delta_{-2}.
```

Moreover, with `epsilon=H/N-1/p`,

```math
H\beta
=
\delta_0+\delta_{-2}-2L\varepsilon.
```

Thus the separated #13 plus #23 route decomposes the same two harmful
residue deviations that #21 ultimately consumes. A direct joint estimate for
`delta_0,delta_(-2)` can preserve correlation lost by generic Minkowski
composition. This is the minimal two-class specialization of candidate #12,
not a requirement for balance in every residue class.

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
- [Two endpoint observables separate harmful excess and imbalance](
  ../properties/sieve-sequence/two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Endpoint-observable joint capacity envelope](
  ../properties/sieve-sequence/endpoint-observable-joint-capacity-envelope.md
  )
- [Endpoint capacity cannot certify the collision budget](
  ../properties/sieve-sequence/endpoint-capacity-cannot-certify-collision-budget.md
  )
- [Endpoint sampling and strike density recombine into harmful residues](
  ../properties/sieve-sequence/endpoint-sampling-strike-density-harmful-residue-bridge.md
  )
- [Weighted harmful-excess energy is already terminal](
  ../properties/sieve-sequence/weighted-harmful-excess-energy-is-terminal.md
  )
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

Correct total hit density does not imply representative local sampling. The
modular filter may correlate with particular gap words, and a short window can
amplify that alignment. Proving one observable, such as mean gap size, does not
prove the universal statement. For the current collision-energy program, the
minimal known useful class contains both unsigned and signed endpoint
observables. Even proving those two leaves candidate #23 accepted-strike
density as the remaining part of the separated scalar representation.
Property #66 then makes a sufficiently small aggregate scalar bound terminal;
candidate #22's harmless-class dispersion remains an independent distribution
question, not an additional survival obligation after scalar feasibility.

## Empirical status (window scale, p to ~19000)

Source: `empirical/sieve-sequence/src/sieve_sequence_empirical/window_cli.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantity: `endpoint_bias = |(1/H) sum_D c(v) -
(1/N) sum_V c(v)|`, the bias of the filter's hit set `D` versus the whole anchor
population `V`, on the observable `c(v) = 1` iff `v` is an endpoint of a 2-gap.
This is only a partial diagnostic: the absolute value discards whether the
filter over-samples endpoints (harmful) or under-samples them (helpful), and
the run did not compare the error with the transition-specific survival
margin.

| range | min | median | max |
|-------|-----|--------|-----|
| dense (p 5..991) | 0.0003 | 0.22 | 0.77 |
| sparse (p ~1000..19000) | 0.03 | 0.16 | 0.85 |

Trend (log-log, n=186): exponent k = -0.011, Pearson r = -0.052 against log p —
**no detectable trend**. The endpoint bias is flat, confined to roughly
`[0, 0.85]`, regardless of p.

Those facts alone do not say whether `eta_p` is small enough. A constant error
can fail a shrinking margin, while a large negative signed bias is harmless.
The earlier favorable interpretation is therefore withdrawn.

### What must be measured

For every transition with `H>0`, retain `N`, `H`, `L`, and the signed harmful
bias

```math
b_+=\max\left(0,\frac KH-\frac{2L}{N}\right).
```

Then test the exact available margin

```math
b_+ < \frac LH-\frac{2L}{N},
```

which is equivalent to `H(2L/N+b_+)<L`. Report the normalized margin as well as
failures. The `H=0` case remains an automatic success handled separately.

## Strategic assessment after empirical review

The current `endpoint_bias` column does **not** test the sufficient condition
end-to-end, so the empirical status is partial and inconclusive. The candidate
is still a strong gap-agnostic framework if a conditioned sampling theorem can
be proved for a bounded observable class. Priority should go to the endpoint
indicator and a few merge/cluster observables under successive future filters,
not to a universal class before the necessary one-sided margin is understood.

## Empirical status (one-sided margin, lineage experiment)

The candidate's OWN sufficient condition `H(2L/N + b_+) < L` (where `b_+` is
the harmful one-sided bias, retaining the sign that actually hurts) was
measured per layer by the fixed-future-window lineage experiment
(`empirical/sieve-sequence/src/sieve_sequence_empirical/lineage_cli.py`), replacing the earlier absolute-bias
diagnostic that discarded the sign.

**Q=101, 24 layers:** the margin `L - H(2L/N + b_+)` is **positive at 24/24
layers**, ranging from `+201` (final layer, r=97) to `+1683.7` (layer 0). Like
#12 it shrinks across the chain but stays well clear of zero. No layer failed.

**Expanded exact sweep (53 heads, 1,890 layers):** using the same exact
lineage library in-memory on every prime head `17<=Q<=251`, together with
`307,401,503,701,997`, the one-sided margin stayed positive at
**1,890/1,890** measured layers. The smallest observed margin was about
`+15.9851`, at `Q=19`, `r=17`, with `G_r(W_Q)=17`. No exact layer failure was
found.

This tests the candidate's stated condition (not the absolute-bias proxy) and
does so after conditioning on every preceding filter. Honest scope: 53 finite
heads still do not prove the margin holds for all `Q`. What remains open is a
proof or a narrower observable class with a demonstrable deterministic sampling
bound.
