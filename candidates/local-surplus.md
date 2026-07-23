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
