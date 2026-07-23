# Protected Endpoints

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Proved below.

## Candidate Hypothesis

For infinitely many transitions installing `p` with next head `q`, some
pre-filter 2-gap start `x` lies in `W_q` and neither endpoint is divisible by
`p`:

```math
x\in S_{old}\cap W_q,
\qquad x\not\equiv0\pmod p,
\qquad x+2\not\equiv0\pmod p.
```

A stronger merge formulation says that at least one local 2-gap has no merge
touching either endpoint. The still stronger rule “merge only at values not
adjacent to a 2-gap” protects every old 2-gap, but is not the real sieve rule.

## Why It Is Sufficient

Filtering preserves the order and value of surviving endpoints. If neither
endpoint is removed, `(x,x+2)` remains a gap of size `2`. Since it lies in
`W_q`, both endpoints are prime. Infinitely many stages satisfying the
hypothesis therefore give infinitely many twin-prime certificates.

## Established Inputs

- [Stable absence and copy-or-merge](../properties/sieve-sequence/absence-of-two-gaps-is-stable.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

The implication is immediate, but the hypothesis already asks for a protected
local candidate. Global survival does not show that one lies in `W_q` or that
the real modular filter avoids its endpoints.

## Empirical status (window scale, p to ~19000)

Source: `candidates/analysis/measure_candidates.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantity: `surviving` = the count of 2-gaps among
*post-filter* survivors in the window `[q,q^2)`. Each such 2-gap is, by the
square-safe certification, a genuine twin-prime pair whose endpoints survived
the filter untouched — i.e. an instance of this candidate's hypothesis.

The candidate's condition holds in **186/186** transitions: `surviving > 0`
always.

| range | min surviving | median | max |
|-------|---------------|--------|-----|
| dense (p 5..991) | 4 | 2,600 | 8,087 |
| sparse (p ~1000..19000) | 11,769 | 440,825 | 1,431,888 |

Trend (log-log, n=186): `surviving ~ p^(+1.60)`, r = +0.998 against log p. The
number of surviving (protected) 2-gaps grows superlinearly with p.

### No counterexample

Zero failures.

### What this does and does not establish

- **Does:** show that at window scale to p~19000 a protected 2-gap (both
  endpoints untouched by the filter) always exists, in abundance. The count of
  twin-prime certificates per window grows like `p^1.6`.
- **Does not:** distinguish this candidate from the others empirically —
  `surviving > 0` is the *conclusion* shared by all the survival candidates, so
  this measurement does not isolate #1's specific mechanism (endpoint
  protection as opposed to, say, surplus). Nor does the finite run prove that
  the conclusion recurs at infinitely many stages.

## Strategic assessment after empirical review

This is best treated as an **outcome formulation**, not a proof mechanism.
The measured column asks directly whether a protected 2-gap survived, so its
perfect finite record is useful ground truth but cannot explain why the filter
must leave one. Proof work should use #1 as the terminal statement that a more
structural candidate—such as local surplus, bounded destruction runs, residue
balance, or shot-spacing capacity—has to deliver. Its standalone proof priority
is therefore low.
