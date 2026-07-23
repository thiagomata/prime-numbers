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
  like `p^1.6`. Any proof invoking #2 may assume `surplus` grows at least this
  fast at this scale without contradicting the data. This directly overturns the
  "Fatal (unproven)" local-density verdict of the learnings doc at window scale.
- **Does not:** prove `surplus > 0` for all p (measured to p~19000 only, still
  small analytically), nor prove the infinitude theorem — #2 is a window-scale
  conditional; its favorable trend is robustness evidence, not a theorem. The
  candidates bearing on infinitude (#5, #6, #7, #9, full #14 chain) are separate
  and unmeasured here.
