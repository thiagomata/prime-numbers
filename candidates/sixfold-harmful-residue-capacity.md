# Sixfold Harmful-Residue Capacity

**Candidate hypothesis:** Unproved and potentially false.

**One-layer capacity theorem:** Mathematically proved.

**Conditional implication:** Mathematically proved.

**Empirical status:** NOT EVALUATED AS A SEPARATE CANDIDATE — this candidate
was derived during an algebra-first proof pass. No new data collection is
proposed.

## Purpose

Candidates #12 and #13 seek distributional control over the locations selected
by an incoming filter. Candidate #14 instead seeks a short interval containing
more 2-gaps than the filter has shots.

This candidate uses a smaller deterministic fact. After filter `3`, every
2-gap start is `5 modulo 6`. Within one residue class modulo an incoming prime
`r`, those starts are therefore spaced by at least `6r`. Since only two
residue classes are harmful, their combined capacity can be bounded directly.

## Candidate Hypothesis

Fix a future prime head `Q`. In the conditioned chain that installs every
not-yet-installed prime `r<Q`, let `G_r(W_Q)` count the complete 2-gaps present
immediately before filter `r` in

```math
W_Q=[Q,Q^2).
```

Define

```math
L_Q=Q^2-Q-3.
```

The hereditary candidate is that, at every conditioned layer `5<=r<Q`,

```math
\boxed{
G_r(W_Q)
\ge
2\left\lfloor\frac{L_Q}{6r}\right\rfloor+3.
}
```

The hypothesis may first be sought for an infinite family of future heads
`Q`; eventual validity for every `Q` would be stronger than necessary.

## Proved One-Layer Capacity

The post-3 phase theorem gives

```math
x\equiv5\pmod6
```

for every 2-gap start `x`. If two such starts also agree modulo the odd prime
`r`, their difference is divisible by `6r`. Therefore one residue class
modulo `r` contains at most

```math
\left\lfloor\frac{L_Q}{6r}\right\rfloor+1
```

complete starts in the window.

Filter `r` destroys exactly the starts in the two distinct classes

```math
0\pmod r
\qquad\text{and}\qquad
-2\pmod r.
```

Hence the destruction count satisfies

```math
K_r(W_Q)
\le
2\left(
\left\lfloor\frac{L_Q}{6r}\right\rfloor+1
\right).
```

This theorem is proved in
[Harmful residue capacity after filter three](
../properties/sieve-sequence/harmful-residue-capacity-after-filter-three.md
).

## Why The Candidate Is Sufficient

At any conditioned layer, the candidate hypothesis and the capacity theorem
give

```math
\begin{aligned}
G_{r^+}(W_Q)
&\ge G_r(W_Q)-K_r(W_Q)
&&[\text{Delete At Most the Harmful Starts}]\\
&\ge
2\left\lfloor\frac{L_Q}{6r}\right\rfloor+3
-
2\left(
\left\lfloor\frac{L_Q}{6r}\right\rfloor+1
\right)
&&[\text{Candidate and Capacity}]\\
&=1.
&&[\text{Simplification}]
\end{aligned}
```

Thus at least one complete 2-gap survives each filter. The next layer's
hypothesis is evaluated on the actual population left by all preceding
filters, so the argument composes through the finite conditioned chain.

After the last prime below `Q` is installed, any remaining complete 2-gap in
`[Q,Q^2)` is square-safe and certifies a twin-prime pair. If the hereditary
population floor holds for infinitely many `Q`, it yields infinitely many
such certificates.

## Relation To Existing Candidates

- **#12, local pattern-residue balance:** controls every residue class by a
  discrepancy estimate. The present candidate needs no equidistribution; it
  uses only the exact capacity of the two harmful classes. Its price is an
  explicit population floor of order `Q^2/r`.
- **#13, uniform local observable sampling:** bounds how strongly filter hits
  favor 2-gap endpoints. The present theorem bounds harmful endpoints through
  their forced arithmetic spacing instead of representativeness.
- **#14, hereditary shot-spacing capacity:** forces a locally crowded pair of
  2-gaps. The present candidate directly forces one-layer survival and does
  not imply that a close pair exists.
- **#22, harmless-class collision energy:** asks how the post-filter survivors
  distribute among the `r-2` harmless classes. The present candidate supplies
  an absolute capacity for every class, but applying that same capacity
  symmetrically to harmful and harmless classes recovers only the direct
  whole-histogram bound. It remains an unconditional fallback, not a proof of
  #22's relative collision scale.
- **#2, local surplus:** compares local 2-gaps with the exact number of
  accepted filter strikes. The present capacity can be smaller than counting
  all accepted strikes because only two start phases can be harmful.

The asymptotic count threshold is

```math
\frac{L_Q}{3r}+O(1),
```

whereas the order-only `k=2` threshold used by #14 is

```math
\frac{L_Q}{2r}+O(1).
```

The factor `2/3` improvement is a genuine consequence of the common
`5 modulo 6` phase of 2-gap starts.

## Algebraic Proof Target

The remaining theorem is now an integer lower bound, not a distributional
analogy:

```math
G_r(W_Q)
\ge
2\left\lfloor\frac{Q^2-Q-3}{6r}\right\rfloor+3
```

through every layer of infinitely many conditioned chains.

A useful intermediate theorem would be a hereditary lower envelope

```math
\inf_{5\le r<Q}
\frac{
G_r(W_Q)
}{
2\left(\left\lfloor L_Q/(6r)\right\rfloor+1\right)
}
>1.
```

Unlike candidate #12, this formulation does not demand small error in all
residue classes. It asks only whether the total conditioned population stays
above a deterministic arithmetic capacity.

## Limitation

The capacity theorem is proved, but the candidate population floor is not.
At a final layer with `r` comparable to `Q`, it still asks for order `Q`
pre-filter 2-gaps in the square window. A proof of that lower bound would be a
major local-abundance result and may retain the same parity obstruction that
blocks direct twin-prime sieving.

The naive cumulative recurrence

```math
G_{r^+}(W_Q)
\ge
G_r(W_Q)
-
2\left(
\left\lfloor\frac{L_Q}{6r}\right\rfloor+1
\right)
```

is valid but too lossy when summed over all `r<Q`: it ignores overlaps between
the harmful sets for different primes, while the sum of reciprocal primes
grows without bound. A viable proof must use the actual conditioned population,
batch overlaps, or another invariant; simply summing the one-layer maxima
cannot establish the hereditary floor for all large `Q`.

## Established Inputs

- [Harmful residue capacity after filter three](
  ../properties/sieve-sequence/harmful-residue-capacity-after-filter-three.md
  )
- [Isolation of 2-gaps after filtering by 3](
  ../properties/sieve-sequence/two-gap-isolation-after-filter-three.md
  )
- [Square-safe certification](
  ../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md
  )
