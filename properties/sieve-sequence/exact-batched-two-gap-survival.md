# Exact Batched 2-Gap Survival

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

Several future prime filters can be applied as one mathematical batch. This
avoids recursive rounding and counts overlaps exactly over a complete expanded
period.

## Setup

Let `M` be the current modulus and let `(x,x+2)` be one current cyclic 2-gap.
Choose a finite set of distinct odd primes

```math
\mathcal R=\{r_1,r_2,\ldots,r_k\}
```

such that no `r_i` divides `M`. Define

```math
B=\prod_{r\in\mathcal R}r.
```

In the combined period modulo `MB`, the old 2-gap has `B` lifted copies.

## Property

Exactly

```math
\prod_{r\in\mathcal R}(r-2)
```

of those `B` copies survive every filter in the batch. Consequently, if the
old complete period contains `G` cyclic 2-gaps, the batched period contains

```math
G_{\mathrm{after}}
=G\prod_{r\in\mathcal R}(r-2).
```

## Proof

Fix one new prime `r`. A lifted pair is destroyed by its filter exactly when
its left endpoint is `0 modulo r` or its right endpoint is `0 modulo r`:

```math
x\equiv0\pmod r
\qquad\text{or}\qquad
x\equiv-2\pmod r.
```

The two forbidden classes are distinct, leaving exactly `r-2` allowed classes
modulo `r`.

The primes in the batch are pairwise coprime and are also coprime to `M`.
The Chinese remainder theorem makes the allowed choices independent across
the whole batch. Their product is therefore the exact number of surviving
lifts. Summing the same count over all old 2-gaps proves the aggregate formula.

## Why Batching Is Stronger Bookkeeping

- No floor is applied after an intermediate prime.
- A value hit by several new filters is still removed only once.
- The result is independent of the order in which the batch filters are
  conceptually applied.
- Prime-by-prime multiplication and one-shot CRT counting give the same exact
  complete-period answer.

## Limitation

The theorem needs the complete combined period of length `MB`. In a shorter
window, the allowed CRT classes need not occur in their full proportions.
Batching therefore proves global survival but does not, by itself, prove a
surviving 2-gap inside a safe window shorter than `MB`.
