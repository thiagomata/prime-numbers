# Exact Global 2-Gap Count

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

This property counts every 2-gap in one complete sieve period directly from
the installed prime filters. It is an exact finite product, not a recurrence
and not an asymptotic estimate.

## Setup

Let `p` be the head prime of a sieve stage. All primes smaller than `p` have
already been installed as filters. Define the stage modulus

```math
M_p=\prod_{r<p}r,
```

where every `r` in the product is prime.

A cyclic 2-gap is represented by a residue `x modulo M_p` for which both `x`
and `x+2` are coprime to `M_p`. These endpoints are consecutive accepted
values because `x+1` is even.

## Property

The exact number of cyclic 2-gaps in one complete period is

```math
G_2(p)=\prod_{\substack{3\le r<p\\r\text{ prime}}}(r-2).
```

The empty product is `1`, so the formula also covers the first odd stage.

## Proof

For the filter `2`, exactly one residue class is available: `x` must be odd.

For each odd prime `r<p`, the pair fails precisely when

```math
x\equiv0\pmod r
\qquad\text{or}\qquad
x\equiv-2\pmod r.
```

These are two distinct residue classes because an odd prime does not divide
`2`. Therefore exactly `r-2` residue classes modulo `r` remain available.

The installed primes are pairwise coprime. The Chinese remainder theorem says
that independent choices of an allowed residue for every installed prime
correspond bijectively to residues modulo `M_p`. Multiplying the number of
choices gives the stated product.

## Consequences

- Every odd stage has at least one global cyclic 2-gap.
- The value can be calculated for an arbitrarily large stage without building
  its gap sequence.
- Adding a new odd prime filter `p` multiplies the global count by `p-2`.

## Limitation

This is a complete-period count. It does not locate the 2-gaps and does not
imply that one occurs in a particular short interval such as `[p,p^2)`.
