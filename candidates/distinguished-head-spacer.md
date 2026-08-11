# Distinguished Head Spacer

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Candidate Hypothesis

Let `S_q` be the bi-infinite periodic set of post-filter 2-gap starts. Define
the forward distance from the head to the next start by

```math
d_{head}(q)=\min\{s-q:s\in S_q,\ s\ge q\}.
```

Suppose, for infinitely many heads `q`,

```math
d_{head}(q)\le q^2-q-3.
```

## Why It Is Sufficient

Let `s=q+d_head(q)`. The candidate bound gives

```math
q\le s\le q^2-3,
```

so `s+2<q^2`. Since `s` is a post-filter 2-gap start, both endpoints avoid
all primes below `q`; the square bound makes both endpoints prime.

This condition is weaker than bounding every cyclic spacer. It controls only
the empty region immediately in front of the distinguished head.

## Established Inputs

- [Rotation and the local boundary](../properties/sieve-sequence/rotation-preserves-cyclic-gap-counts.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

The inequality is close to the desired local-placement theorem. Its value as a
candidate is that it isolates the single relevant spacer, but global counts and
rotation invariance currently provide no bound on its phase relative to `q`.
