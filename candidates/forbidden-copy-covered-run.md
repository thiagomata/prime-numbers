# Forbidden-Copy Covered Run

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Candidate Hypothesis

Fix an old 2-gap `(a,a+2)` with period `M`. Take the complete finite batch
containing every not-yet-installed prime below the target head `q`. Each batch
prime forbids two copy-index classes. Let `C` be the union of all those
forbidden classes, and let

```math
\operatorname{coverRun}(C)
=\max\{|J|:J\text{ is consecutive and }J\subseteq C\}.
```

Let `I(a,M,q)` be the consecutive copy-index interval placing both endpoints
inside `W_q`. Suppose, for infinitely many finite scenarios,

```math
|I(a,M,q)|>\operatorname{coverRun}(C).
```

## Why It Is Sufficient

If every eligible index were forbidden, the whole interval `I(a,M,q)` would
be a covered run longer than `coverRun(C)`, a contradiction. Hence some

```math
j\in I(a,M,q)\setminus C
```

avoids every filter in the batch. Its pair `(a+jM,a+2+jM)` lies in the safe
window and survives all primes below `q`, so it is a twin-prime certificate.

## Established Inputs

- [Exact copy-index filter frequency](../properties/sieve-sequence/copy-index-filter-frequency.md)
- [Exact batched survival](../properties/sieve-sequence/exact-batched-two-gap-survival.md)
- [Short-window boundary](../properties/sieve-sequence/batched-short-window-discrepancy-boundary.md)

## Limitation

CRT counts allowed classes over a complete batch modulus but does not bound the
longest partially covered run strongly enough for the eligible interval. A
fixed seed may also have at most one eligible copy once its primorial exceeds
the square window.

## Empirical status: not measured this pass

This candidate's true form operates over the *copy-index* view (a fixed seed's
copies modulo the old period `M`, with the batch of future primes forbidding
copy-index classes) — a whole-period / primorial-scale object. The window-scale
stress-test sieves `[q,q^2)` directly and does not construct the copy-index
lattice, so the covered-run quantity `coverRun(C)` was not measured. Deferred
to a deeper pass. (A window-proxy exists in principle but would not test the
candidate's actual copy-index claim.)

## Strategic assessment after empirical review

The fixed-seed formulation has an intrinsic scale problem: once the seed
period `M` is comparable with or larger than the length of the future square
window, that seed may contribute at most one eligible copy. A covered-run
bound can then have no room to force an uncovered index, regardless of the
large complete-batch survivor count.

Proof priority is low as stated. A more viable descendant would let the seed
stage move with the target head, or aggregate many seed 2-gaps into a
mesoscopic copy-index population. The next experiment should follow those
copies through all intervening filters in one fixed future window and measure
the longest genuinely covered run after conditioning.
