# Position-Blind Index Spectrum

**Status:** Mathematically proved finite-probability fact. Holds for **any**
uniformly random size-`K` subset of a population of size `N`, and therefore
for any position-blind allocator read in the population's own index
coordinates: the exact-quota companion's uniform draw without replacement,
and (by independence, separately) per-parent Bernoulli coins. Like the
[Local Survivor Allocation Range](local-survivor-allocation-range.md), this
property requires no companion-process premise beyond position-blind
placement; it is the null model for spectral placement comparisons against
the real sieve's CRT-determined strikes.

## Meaning

When a filter's strikes are placed without any information about position,
the expected power spectrum of the strike indicator along the population's
own index axis is exactly flat beyond the zero frequency. Deterministic
structured placement is the opposite extreme: an arithmetic placement
concentrates all of its power into a small family of frequencies. This
separation is the reference point for asking, frequency by frequency,
whether the real sieve's strike placement resembles a position-blind
allocator or a structured one.

Flatness here is a statement about the **expectation over placements**, not
about a single realization. A finite experiment must therefore use the full
permutation distribution (sampled or enumerated size-`K` subsets) as its
null band, not the mean alone.

## Setup

Let `S` be a uniformly random subset of `Z/NZ` with `|S|=K` fixed,
`1<=K<=N`. For a frequency `k` with `k mod N != 0`, let

```math
X_k=\sum_{i\in S}\chi_k(i),
\qquad
\chi_k(i)=e^{-2\pi iki/N}.
```

For distinct indices `i!=j`,

```math
\Pr(i\in S,\ j\in S)=\frac{K(K-1)}{N(N-1)},
```

and for `i=j` the probability is `K/N`.

## Flat-Spectrum Identity

Expanding the second moment by inclusion of pairs,

```math
\begin{aligned}
\mathbb E|X_k|^2
&=\sum_{i,j\bmod N}
\chi_k(i)\overline{\chi_k(j)}
\Pr(i\in S,\ j\in S)\\
&=\frac KN\sum_i1
+\frac{K(K-1)}{N(N-1)}
\sum_{i\ne j}\chi_k(i)\overline{\chi_k(j)}
&&[\text{Split Diagonal And Off-Diagonal}]\\
&=K+\frac{K(K-1)}{N(N-1)}(-N)
&&[\text{Full Sum Is }0\text{; Diagonal Is }N]\\
&=K-\frac{K(K-1)}{N-1}\\
&=\frac{K(N-K)}{N-1}.
&&[\text{Simplification}]
\end{aligned}
```

The value is independent of `k`: for every nonzero frequency,

```math
\boxed{
\mathbb E|X_k|^2=\frac{K(N-K)}{N-1}.
}
\qquad[\text{Q.E.D.}]
```

With `delta=K/N`, the normalized power is
`delta(1-delta)N/(N-1)`, so the expected spectrum is flat at the
Bernoulli-variance level up to the finite-population factor `N/(N-1)`.

## Deterministic Contrast

Flatness is a property of position-blind placement, not of indicator
supports in general. If `K` divides `N` and `S` is the subgroup (or a
coset) of index `N/K`, then

```math
X_k=
\begin{cases}
K\chi_k(i_0),&\chi_k\text{ trivial on }S,\\
0,&\text{otherwise},
\end{cases}
```

so all power sits in the dual subgroup: a Dirac concentration at the
opposite extreme of the flat law. A rotation-coded placement of strike
indices places its power on the associated rotation frequency and its
harmonics. Measured spectra can therefore distinguish placement families
even when every family has the same strike count.

## Coordinate Contract

The flatness claim is made in the **index coordinates** of the population
axis (`0..N-1` along the sequence's own enumeration). Two established
results warn against reading it in other coordinates:

- In raw integer coordinates, both position-blind and CRT placements inherit
  the wheel-comb lines of the index-to-value map, so spectra there are never
  flat regardless of placement policy.
- By the [short-interval localization property](
  ../../properties/sieve-sequence/short-interval-localization-destroys-prime-conductor-decay.md),
  any indicator supported on a short interval concentrates the exact
  fraction `1-1/p` of its Fourier energy in characters nontrivial at `p`,
  destroying the complete-set decay `2/p`. Localized spectral comparisons in
  quotient coordinates must therefore be normalized by the localized null,
  not by complete-period weights.

A spectral comparison is meaningful only after the coordinate contract is
fixed: index coordinates for placement-shape questions, with the permutation
null above; quotient coordinates for conductor questions, with the localized
normalization.

## Role

This property supplies the null model for the measurement obligations of
[candidate #26: sub-CRT strike decoherence](
../../candidates/sub-crt-strike-decoherence.md), which compares the real
sieve's realized strike placement spectrum against the position-blind band,
frequency by frequency, at window scales below the CRT period.

## Related

- [Local Survivor Allocation Range](local-survivor-allocation-range.md) —
  the same position-blind framework in physical space; this file is its
  frequency-space counterpart.
- The exact-quota random-location companion (named in the
  [companion registry](../README.md)) — its placement law is exactly the
  uniform size-`K` subset used here; its model folder is not yet populated.
- [Short-interval localization destroys prime conductor decay](
  ../../properties/sieve-sequence/short-interval-localization-destroys-prime-conductor-decay.md)
- [Accepted-strike cross-layer CRT orthogonality](
  ../../properties/sieve-sequence/accepted-strike-cross-layer-crt-orthogonality.md)
