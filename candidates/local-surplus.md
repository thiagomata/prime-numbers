# Local Surplus

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

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

## Established Inputs

- [Exact accepted local strikes](../properties/sieve-sequence/exact-accepted-local-filter-strikes.md)
- [2-gap isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
- [Sharp local threshold](../properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md)

## Limitation

The conditional inequality is established; the candidate is the recurring
local lower bound `L(p,q)>A(p,q)`. Complete-period counts do not prove it.

## Empirical status (window scale, p to ~19000)

Source: `candidates/analysis/measure_candidates.py` (dense p<=991, 165 clean
transitions) + `--sparse` (every 100th prime to p~19000, 21 more). Full data in
`data/candidates/window-measurements{,-sparse}.csv`. See
`candidates/analysis/FINDINGS.md` for the cross-candidate synthesis.

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
