# Safe-Zone Exhaustion Curve

**Status:** Problem boundary. The boundary value is proved (elementary). A
universal, data-independent lower bound on how many survivors populate the
safe zone before that value is reached is proved via external citation
(Schroeder 2017), but is far looser than the best-fitting practical estimate,
which itself remains unproven. Stainless verification is not claimed here.

## Meaning

[Safe-Window 2-Gaps Certify Twin Primes](safe-window-two-gaps-certify-twin-primes.md)
establishes that every stage-`p` survivor in `[p, p^2)` is genuinely prime.
This note asks the companion question: how many survivors actually populate
that window before it runs out? That count determines how far a finite-length
sample of a sieve-sequence stage can go before it is even possible to see a
value where acceptance and certified primality diverge -- directly relevant
wherever such a sample is drawn, e.g. the gap-cycle heatmaps in
`presentations/sieve-sequence-visualization/figures/gap_heatmap.py`
(`estimated_boundary_indices`, `proven_safe_boundary_indices`,
`draw_boundary_curves`), which plot both curves from this note directly on
the diagrams.

## Setup

Let `p` be a sieve-sequence head, `M = \prod_{r<p} r` the primorial of primes
below it, and

```math
A(p) = \#\{n \in [p, p^2) : \gcd(n, M) = 1\},
```

the count of stage-`p` survivors strictly inside the safe window.

## Property 1 (elementary, proved here): The Boundary Value Is Exact

The first composite stage-`p` survivor is exactly `p^2`. Already established
in
[Safe-Window 2-Gaps Certify Twin Primes](safe-window-two-gaps-certify-twin-primes.md);
restated because `A(p)` is defined directly from it.

## Property 2 (external citation, proved, universal): A Loose But Unconditional Lower Bound

For every prime `p >= 11`,

```math
A(p) \ge \left\lfloor \frac{2(p^2-1)}{p} \right\rfloor.
```

### Proof

J.Z. Schroeder, "A lower bound on the number of rough numbers,"
arXiv:1705.04831 (2017), proves

```math
\Phi(n,p) \ge \left\lfloor \frac{2n}{p} \right\rfloor + 1
\qquad\text{for every prime } p\ge11 \text{ and every } n\ge2p,
```

where `\Phi(n,p)` counts positive integers up to `n` with no prime factor
below `p`. Apply this with `n = p^2 - 1` (which satisfies `n \ge 2p` for
every `p` in this range). `A(p)` differs from `\Phi(p^2-1, p)` only by
excluding the single integer `1` (the lone value below `p` that is trivially
coprime to every prime below `p`), giving

```math
A(p) = \Phi(p^2-1, p) - 1 \ge \left\lfloor\frac{2(p^2-1)}{p}\right\rfloor.
```

### This Bound Is Genuinely Universal, Not Fit To Any Dataset

Nothing in its derivation references any specific generated sieve-sequence
data. It holds for every prime `p >= 11`, including primes far beyond any
stage this project has generated. It was checked -- not derived from -- this
project's own generated data
(`data/sieve-sequence/first_gaps_per_seq.csv`, 200
stages) for every row where ground truth exists (`p` from 11 to 131): zero
violations.

## Property 3 (unproven, empirical): A Much Tighter Practical Estimate

```math
\hat A(p) = (p^2-p)\prod_{r<p}\left(1-\frac1r\right)
```

fits the true `A(p)` far more closely in practice: checked against every
available ground-truth point (`p` from 13 to 131), it never overshoots, with
`A(p)/\hat A(p)` between 0.99 and 1.03 and tightening as `p` grows. But this
is not proved. `\hat A(p)` assumes stage-`p` survivors are locally
equidistributed across `[p,p^2)` at their global density, and no argument
here establishes that a short interval (length `p^2-p`, a vanishing fraction
of the full period `M` once `p` exceeds roughly 15-20) must track that global
average. Read this as a well-supported conjecture about this specific
quantity, not a theorem. Mertens' third theorem (F. Mertens, "Ein Beitrag zur
analytischen Zahlentheorie," J. Reine Angew. Math. 78 (1874), 46-62) is the
classical result behind why the product itself is well understood asymptotically;
it says nothing about a short sub-interval.

## Why Property 2 Alone Isn't Enough In Practice

`\hat A(p)` grows like `p^2/\ln p`; the proved bound in Property 2 grows only
like `2p`. They diverge fast: by `p=131`, the proved bound (261) is only
about 13% of the actual value (1944). Property 2 is what can be relied on
without qualification; Property 3 is what actually predicts the data.

## Rejected Approach: Rosser & Schoenfeld's Density Bound

An earlier attempt used Rosser & Schoenfeld's explicit two-sided bound on the
Mertens product (J.B. Rosser and L. Schoenfeld, "Approximate formulas for
some functions of prime numbers," Illinois J. Math. 6 (1962), 64-94,
Theorem 7):

```math
\frac{e^{-\gamma}}{\ln x}\left(1-\frac{1}{2\ln^2x}\right)
< \prod_{r\le x}\left(1-\frac1r\right) <
\frac{e^{-\gamma}}{\ln x}\left(1+\frac{1}{2\ln^2x}\right),
```

lower bound proved for `x >= 285`, upper bound for `x > 1`. This bounds the
density product itself -- essentially an average over a full period `M` (or,
in the limiting sense, counting from `1` up to `N` as `N \to \infty`) -- not
the count within one short, specific sub-interval `[p,p^2)`. Using a global
average density as a lower bound on a short interval's count requires an
additional equidistribution argument. A real one likely exists in deeper
sieve theory (Brun's sieve, Selberg's sieve, or a more careful application of
explicit prime-counting results), well beyond the direct substitution
attempted here. That gap was never closed, so this approach was withdrawn.
Recorded so it is not attempted again the same way without addressing the gap.

## Also Rejected: Naive Legendre/Möbius Inclusion-Exclusion

The classical exact identity

```math
\Phi(n,p) = \sum_{d\mid M} \mu(d)\left\lfloor\frac{n}{d}\right\rfloor
```

gives `|\Phi(n,p) - n\prod_{r<p}(1-1/r)| < 2^{k}`, where `k` is the number of
primes below `p` (the number of squarefree divisors of `M`). Applied here,
`2^k` overwhelms the main term almost immediately: the resulting bound is
already negative at `p=3` and stays negative (vacuous) for every stage in the
generated dataset. Recorded as a negative result explaining why a cruder
inclusion-exclusion argument was abandoned in favor of Property 2.

## Consequence For The Visualization

Any fixed-length sample of a sieve-sequence stage will show only "safe"
behavior (acceptance = primality, no merges yet possible) for every column
left of `A(p)`. Property 2 gives a certificate for this holding for literally
any prime, at the cost of being far more conservative than necessary.
Property 3 predicts where the transition actually happens, but remains a
conjecture.

## References

- Elementary boundary value: [Safe-Window 2-Gaps Certify Twin Primes](safe-window-two-gaps-certify-twin-primes.md)
- J.Z. Schroeder, "A lower bound on the number of rough numbers," arXiv:1705.04831 (2017). https://arxiv.org/abs/1705.04831
- J.B. Rosser and L. Schoenfeld, "Approximate formulas for some functions of prime numbers," Illinois J. Math. 6 (1962), 64-94.
- F. Mertens, "Ein Beitrag zur analytischen Zahlentheorie," J. Reine Angew. Math. 78 (1874), 46-62.

## Limitation

Property 3 -- the estimate that actually matters for predicting where the
chart transitions from chaos to order -- is not proved here or anywhere
cited. Closing that gap, proving stage-`p` survivors are sufficiently
equidistributed across `[p,p^2)` specifically and not just on average over a
full period, is the open problem this note leaves behind.
