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
