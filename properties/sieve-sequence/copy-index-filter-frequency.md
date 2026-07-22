# Exact Filter Frequency Across Repeated Copies

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

Repetition gives deterministic distribution information. A new prime filter
cannot choose arbitrary copies of an old 2-gap: it can strike only two known
residue classes of the copy index.

## Setup

Let `M` be the old period modulus and let `(a,a+2)` be one old cyclic 2-gap.
Its lifted copies have endpoints

```math
(a+jM,\ a+2+jM),
```

where `j` ranges through consecutive integers. Let `r>2` be a new prime not
dividing `M`.

## Property For One Filter

There are exactly two forbidden copy-index classes modulo `r`:

```math
j\equiv-aM^{-1}\pmod r
```

and

```math
j\equiv-(a+2)M^{-1}\pmod r.
```

They are distinct. Every other copy survives filter `r`.

Consequently, among any `N` consecutive copy indices, filter `r` destroys at
most

```math
2\left\lceil\frac Nr\right\rceil
```

copies of this old 2-gap. In a complete block of `r` consecutive copies, it
destroys exactly `2` and preserves exactly `r-2`.

## Proof

Because `gcd(M,r)=1`, multiplication by `M` is invertible modulo `r`. The left
endpoint is divisible by `r` for exactly the first displayed class, and the
right endpoint is divisible by `r` for exactly the second. If the classes were
equal, subtracting their congruences would give `2=0 modulo r`, impossible for
`r>2`.

Each residue class modulo `r` occurs at most `ceil(N/r)` times in `N`
consecutive integers. Summing the capacities of the two forbidden classes
proves the finite-slice bound.

## Exact Batch Distribution

For a batch `R` of distinct new odd primes, define

```math
B=\prod_{r\in\mathcal R}r.
```

The surviving copy indices form a completely determined periodic set modulo
`B`. By CRT, that set contains exactly

```math
\prod_{r\in\mathcal R}(r-2)
```

classes in each complete block of `B` copy indices.

For any finite run `J` of copy indices, the exact survival question is

```math
J\cap
\left\{j:
j\text{ avoids both forbidden classes modulo every }r\in\mathcal R
\right\}
\ne\varnothing.
```

## What This Corrects

The filter cannot remove repeated 2-gaps as though their positions were
arbitrary. Their strike frequency and phases are fixed by modular arithmetic.
A proof should use this copy-index structure before applying a worst-case
capacity estimate.

## Limitation

Different primes have different forbidden index classes. Over a partial block
shorter than `B`, their union can cover a finite run collectively even though
each individual prime leaves most copies untouched and no new prime divides
`M`.

Thus the remaining batch question is precise: bound the longest consecutive
run of copy indices covered by the union of all batch-forbidden classes. Full
coverage of a short run does not require one new prime to be a multiple of an
old prime; distinct coprime primes may cover different indices.
