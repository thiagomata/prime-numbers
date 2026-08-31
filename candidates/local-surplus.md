# Local Surplus

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Empirical status:** REINFORCED — `surplus > 0` in 186/186 window-pass transitions (p to ~19000), growing like `p^1.6`; the terminal sufficient target. See "Empirical status" section.

## Candidate Hypothesis

Let `L(p,q)` be the number of pre-filter 2-gaps wholly contained in `W_q`.
Suppose, for infinitely many consecutive primes `p<q`,

```math
L(p,q)>A(p,q),
```

where the exact number of accepted values removed by filter `p` is

```math
A(p,q)=
\pi\!\left(\left\lfloor\frac{q^2-1}{p}\right\rfloor\right)
-\pi(p-1).
```

## Why It Is Sufficient

After filter `3`, distinct 2-gaps do not share an endpoint. One removed
accepted value therefore destroys at most one local 2-gap. At most `A(p,q)`
of the `L(p,q)` gaps are destroyed, so

```math
G_{surviving}(p,q)\ge L(p,q)-A(p,q)>0.
```

Every surviving member of `W_q` is a twin-prime certificate.

## Incremental Annular Form

The [incremental danger-annulus decomposition](../properties/sieve-sequence/incremental-danger-annulus-decomposition.md)
defines `L_D(p,q)` as the number of actual pre-filter 2-gaps whose starts lie
in the refined newly exposed coordinate set, and `K_D(p,q)` as the number of
those gaps destroyed by filter `p`.

The sharper incremental candidate is that, for infinitely many consecutive
primes `p<q`,

```math
L_D(p,q)>A(p,q)-1.
```

The established effective destruction bound gives

```math
\begin{aligned}
G_{D,surviving}(p,q)
&\ge L_D(p,q)-K_D(p,q),\\
&\ge L_D(p,q)-(A(p,q)-1),\\
&>0.
\end{aligned}
```

Every such survivor starts above `p^2` and has upper endpoint below `q^2`, so
it is a newly exposed square-safe twin-prime certificate. Success at infinitely
many transitions gives distinct pairs because consecutive square annuli do not
overlap.

For a condition expressed only through the consecutive-prime gap `d=q-p`, the
simpler but weaker raw sufficient form is

```math
L_D(p,q)
>
R_V(p,q)-1
=
2d+\left\lceil\frac{d^2}{p}\right\rceil-1.
```

Since `A(p,q)<=R_V(p,q)`, this implies the exact accepted-strike condition.
The original full-window hypothesis `L(p,q)>A(p,q)` remains valid as a
square-safe survival condition; the annular form asks specifically for newly
exposed survival.

The existing 186-transition measurements below count the full window `W_q`.
They do not measure `L_D(p,q)` and therefore are not empirical evidence that
either annular inequality holds. The missing ingredient is still a recurring
lower bound for the actual annular population.

## Established Inputs

- [Exact accepted local strikes](../properties/sieve-sequence/exact-accepted-local-filter-strikes.md)
- [2-gap isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
- [Sharp local threshold](../properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md)

## Proved Capacity, Defined Benchmark, and Open Local Transfer

The proof-status boundary is:

| Statement | Status |
|---|---|
| Exact `A(p,q)` and the upper bound `A(p,q)<=3p` | **[Mathematically proved]** |
| `L(p,q)>A(p,q)` implies at least one surviving local 2-gap | **[Proved conditional implication]** |
| `L_hat(p,q)=(q^2-q)delta_p` | **[Definition; complete-period-density benchmark]** |
| `L_hat~kappa*p^2/log^2(p)` and `L_hat/(3p)->infinity` | **[Mathematically proved for the defined benchmark only]** |
| Actual `L>A` in all 186 measured transitions and the measured `L/L_hat` range | **[Empirically checked on a finite sample]** |
| Actual `L>A` infinitely often, or a sufficient bound on the local discrepancy | **[Open]** |

The two sides of the surplus inequality have very different known scales.
Write the next prime as `q=p+d`. The exact accepted-strike endpoint is

```math
K
=
\left\lfloor\frac{q^2-1}{p}\right\rfloor
=
p+2d+\left\lfloor\frac{d^2-1}{p}\right\rfloor,
```

and therefore

```math
A(p,q)=\pi(K)-\pi(p-1).
```

The raw annular multiple count gives the unconditional upper bound

```math
A(p,q)
\le
2d+\left\lceil\frac{d^2}{p}\right\rceil.
```

Bertrand's postulate gives `d<p`, so the deliberately loose consequence
`A(p,q)<=3p` is available without predicting the size of the next prime gap.
The exact accepted count is normally far below this raw bound.

Immediately before installing `p`, the exact complete-period density of
2-gap starts is

```math
\delta_p
=
\frac12
\prod_{\substack{3\le r<p\\r\text{ prime}}}
\left(1-\frac2r\right).
```

The recorded measurements use the **ambient-coordinate benchmark** obtained by
multiplying this density by the length of the value interval `[q,q^2)`:

```math
\widehat L(p,q)
=
(q^2-q)\delta_p.
```

This is a defined benchmark, not a transfer theorem for actual `L`, and its
length is not the cardinality of the eligible 2-gap-start window. Under the
canonical endpoint convention

```math
W_q=\{x:q\le x\text{ and }x+2<q^2\},
\qquad
|W_q|=q^2-q-2.
```

Actual `L` counts only complete pairs with starts in `W_q`. A strict-start
benchmark would instead be `(q^2-q-2)delta_p`; it differs from the recorded
ambient benchmark by exactly `2delta_p` and has the same asymptotic scale. The
finite `L/L_hat` ratios below refer to the recorded ambient benchmark.

If `C_2` denotes the twin-prime Euler-product constant, the classical Mertens
product gives

```math
\delta_p
\sim
\frac{\kappa}{\log^2p},
\qquad
\kappa=2C_2e^{-2\gamma}\approx0.416,
```

and hence

```math
\widehat L(p,q)
\sim
\kappa\frac{p^2}{\log^2p}.
```

At the level of this benchmark, even comparison with the loose raw capacity
is overwhelmingly favorable:

```math
\frac{\widehat L(p,q)}{3p}
\sim
\frac{\kappa}{3}\frac{p}{\log^2p}
\longrightarrow\infty.
```

For the incremental annulus, the corresponding conditional benchmark is

```math
\widehat L_D(p,q)
=
(q^2-p^2)\delta_p
=
(2pd+d^2)\delta_p.
```

On the ordinary average-prime-gap scale `d` comparable to `log(p)`, this is
of order `p/log(p)` and diverges, while the heuristic accepted-strike scale is
constant order. This average-scale statement is not a bound for every
individual consecutive-prime gap.

The exact logical boundary is the local discrepancy

```math
L(p,q)=\widehat L(p,q)+E^{\mathrm{pre}}_{p,q}.
```

Neither the complete-period product nor its asymptotic controls
`E^{pre}_{p,q}` in this distinguished window. Thus the scale separation is a
benchmark asymptotic, not a proof of `L>A`: an unconditional lower bound
preventing `E^{pre}_{p,q}` from cancelling essentially the entire main term
is still the candidate's missing theorem.

The 186 distinct measured transitions with `5<=p<=19429` agree strongly with
the projected separation:

- the exact accepted count was always between `2` and `5`, with histogram
  `A=2:90`, `A=3:68`, `A=4:20`, and `A=5:8`;
- actual `L` divided by the pre-filter benchmark `L_hat` stayed between
  approximately `0.808` and `1.132`; and
- the measured surplus grew from `4` to `1,431,886`.

Representative rows are:

| `p` | actual `L` | exact `A` | `L-A` |
|---:|---:|---:|---:|
| 37 | 49 | 3 | 46 |
| 71 | 124 | 2 | 122 |
| 233 | 765 | 3 | 762 |
| 467 | 2,391 | 4 | 2,387 |
| 19,429 | 1,431,888 | 2 | 1,431,886 |

## Limitation

The conditional inequality is established; the candidate is the recurring
local lower bound `L(p,q)>A(p,q)`. Complete-period counts do not prove it.

## Empirical status (window scale, p to ~19000)

Source: `python/src/sieve_sequence/window_cli.py` (dense p<=991, 165 clean
transitions) + `--sparse` (every 100th prime to p~19000, 21 more). Full data in
`data/candidates/window-measurements{,-sparse}.csv`. See
`empirical/sieve-sequence/FINDINGS.md` for the cross-candidate synthesis.

The candidate's concrete sufficient condition `surplus = G_local - A(p,q) > 0`
holds in **186/186** measured transitions. It is the strongest signal in the
entire run, and it strengthens with p:

| range | min surplus | median | max |
|-------|-------------|--------|-----|
| dense (p 5..991) | 4 | 2,100 | 8,085 |
| sparse (p ~1000..19000) | 11,768 | 420,697 | 1,431,886 |

Trend (log-log fit over all 186 transitions): `surplus ~ p^(+1.61)`,
Pearson r = +0.998 against log p. The worst-case survival margin does not just
stay positive — it grows superlinearly.

### No counterexample

Zero failures: `surplus > 0` in every transition. The local-surplus lower bound
never comes close to failing at window scale; the minimum observed margin is 4
(at the smallest clean transition (7,11)) and it grows from there.

### What this does and does not establish

- **Does:** show that, at window scale to p~19000, the worst-case bound alone
  guarantees a surviving 2-gap in every transition, with a margin that grows
  along a fitted `p^1.6` trend over the sample. This is a conjectural target
  scale, not an assumption available to a proof. The observations contradict a
  claim that local surplus is already empirically failing in this range.
- **Does not:** prove `surplus > 0` for all p or at infinitely many stages
  (measured to p~19000 only, still small analytically). Its favorable trend is
  robustness evidence, not an asymptotic theorem.

## Strategic assessment after empirical review

This is the clearest **terminal sufficient target** in the catalog. Contrary to
the earlier synthesis, it is not irrelevant to infinitude merely because it is
window-local: a proof of `L(p,q)>A(p,q)` at infinitely many consecutive-prime
transitions would, by the conditional implication above, produce infinitely
many square-safe 2-gaps. What it lacks is an explanatory mechanism for the
lower bound on `L`.

The finite 186/186 record makes #2 a high-value theorem target, but attempting
it only through global density is likely to encounter the same local-placement
barrier. The most promising use of the other candidates is to upper-bound
actual harmful hits more sharply than `A(p,q)`, or to prove a hereditary local
lower bound that closes this surplus inequality.
