# Bounded Post-Merge Spacer

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Candidate Hypothesis

Let `S_q` be the nonempty post-filter 2-gap starts in their bi-infinite
periodic ordering with modulus `M_q`. Let

```math
D_{max}(q)=\max_i(s_{i+1}-s_i)
```

be the largest cyclic distance between consecutive starts. Suppose, for
infinitely many `q`,

```math
D_{max}(q)<q^2-q-2.
```

## Why It Is Sufficient

An interval longer than every empty spacer cannot avoid all points of the
periodic set. The admissible start interval

```math
[q,q^2-2)
```

has length `q^2-q-2`. Under the strict spacer bound it contains a point of
`S_q`; that point satisfies `x+2<q^2` and certifies a twin-prime pair.

## Established Inputs

- [Exact global non-emptiness](../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

The global count controls the average spacer, not the maximum. Merging deleted
starts adds adjacent spacers and can create a rare empty arc much larger than
the average.

## Empirical status: not measured this pass

This candidate is **whole-period** — it bounds the maximum cyclic spacer
`D_max(q)` over the full period modulus `M_q`, which requires primorial-scale
data. The window-scale stress-test (`candidates/analysis/measure_candidates.py`)
sieves only `[q,q^2)` and so cannot measure `D_max`. Deferred to a deeper
(whole-period) pass. See `candidates/analysis/FINDINGS.md` for the distinction
between window-measurable and whole-period candidates.

## Strategic assessment after empirical review

This criterion is sufficient but substantially stronger than the local
conclusion: it controls the single worst empty arc anywhere in a primorial
period, even though survival needs only the arc containing the distinguished
head to be short. Its extreme-value character is similar to a
Jacobsthal-function problem and may be much harder than the original local
placement question.

Proof priority is therefore low as a direct route. Complete periods at the
small stages should still be measured to learn the scale of `D_max(q)` and to
test proposed bounds, but the head-specific spacer (#8) or a hereditary
fixed-window argument is likely a better target than a universal maximum.
