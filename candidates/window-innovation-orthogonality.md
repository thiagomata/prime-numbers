# Window Innovation Orthogonality

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved (the cross-term
reduction and local Pythagoras below are elementary finite algebra).

**Empirical status:** ALGEBRA-FIRST — the global layer identity is proved
([Layer Strikes Are Innovations Of The Layer Filtration](
../properties/sieve-sequence/layer-strike-innovation-orthogonality.md));
the local window form is open, and the next action is exact computation
(N3) and bounded falsifier checks (N1) rather than broader measurement.

## Candidate Hypothesis

All quantities are deterministic; no probability space is assumed for the
real sieve. Fix a prime head `Q`, install the filters `r<Q`, and restrict
attention to the square window `W=[Q,Q^2)` of length `L`.

For each layer `i`, let `g_i` be the centered strike observable of the
[innovation property](
../properties/sieve-sequence/layer-strike-innovation-orthogonality.md).
On the complete period, `sum_a g_i(a)h(a)=0` for **every** past-measurable
`h`. The candidate asserts the window-restricted analogue: for every layer
`i` and every `h` from the explicit past-measurable class

```text
H_past = { g_j : j<i }
         union { g_j g_k : j<k<i }
         union { survival indicators 1_{gcd(a,P_j)=1} : j<=i }
```

the window correlation satisfies the position-blind fluctuation scale

```math
\left|\sum_{n\in W}g_i(n)\,h(n)\right|
\;\le\;
\kappa\cdot
\left(\sum_{n\in W}h(n)^2\cdot\frac{\varphi(P_i)}{P_i}\frac{r_i-1}{r_i^2}
\right)^{1/2},
```

with a constant `kappa` uniformly bounded over layers and heads (the
right side is the standard deviation of the centered sum under uniform
random sampling of `L` period residues — the exact fluctuation scale of
the position-blind null). Equivalently: the window-restricted innovation
Gram matrix `G^{(W)}_{ij}=sum_{n in W} g_i(n)g_j(n)` is near its typical
profile — diagonals near their complete-period densities scaled by `L`,
off-diagonals at the fluctuation scale.

This is deliberately the **strongest natural local form** of the
requirement that a new sequence carry low correlation with all previous
ones: the test class is the full past span (products included), not a
single predecessor, and the reference scale is exact rather than
heuristic.

## Why It Is Sufficient

The window cross terms are themselves instances of the hypothesis: for
`i<j`, the factor `g_i` is past-measurable for layer `j`, so

```math
\sum_{n\in W}g_i(n)g_j(n)
```

is exactly a window correlation of the hypothesized form. Therefore the
hypothesis controls every off-diagonal entry of `G^{(W)}`. Writing
`S(n)=sum_{i<m}g_i(n)` for the total centered layered discrepancy,

```math
\begin{aligned}
\sum_{n\in W}S(n)^2
&=\sum_i G^{(W)}_{ii}
+2\sum_{i<j}G^{(W)}_{ij}
&&[\text{Expansion}]\\
&\le
\sum_i\left(\text{typical}_i+O(\text{fluctuation})\right)
+2\sum_{i<j}\kappa\cdot\text{fluctuation}_{ij}
&&[\text{Hypothesis}]
\end{aligned}
```

which is the **local approximate Pythagoras**: the window mean-square of
the layered discrepancy is additive across layers, at the position-blind
scale, with no primorial factor. By Cauchy–Schwarz,

```math
\left|\sum_{n\in W}S(n)\right|
\le
\sqrt{L\sum_{n\in W}S(n)^2},
```

so the hypothesis yields a two-sided mean-square window discrepancy bound
of the exact shape the terminal chain lacks. This is the "new signed
mean-square or cross-layer cancellation" named by the
[Investigation Closure Matrix](INVESTIGATION_STATUS.md) as the primary
remaining frontier, formulated in the innovation basis where the
complete-period answer is exactly clean. Feeding it into the
`#23 -> #24` chain, or into candidate #10's two-sided discrepancy,
requires the chain's own composition steps and is not claimed here.

## Established Inputs

- [Layer Strikes Are Innovations Of The Layer Filtration](
  ../properties/sieve-sequence/layer-strike-innovation-orthogonality.md)
  — the global identity this candidate localizes: conditional mean zero,
  span orthogonality, product annihilation, adaptive Pythagoras, with the
  measurability constraint validated as load-bearing.
- [Accepted-strike cross-layer CRT orthogonality](
  ../properties/sieve-sequence/accepted-strike-cross-layer-crt-orthogonality.md)
  — the pairwise special case, exact norms, and the `LR` obstruction this
  candidate must overcome by typicality rather than by Bessel.
- [Fourier bound for two-gap correlation prefixes](
  ../properties/sieve-sequence/fourier-two-gap-correlation-prefix-bound.md)
  — conductor weights `prod 2/(p-2)`; the off-diagonal Gram entries
  CRT-factor into products of these local factors.
- [Short-interval localization destroys prime conductor decay](
  ../properties/sieve-sequence/short-interval-localization-destroys-prime-conductor-decay.md)
  — the warning that interval restriction concentrates spectral mass;
  typicality must be measured against the localized null.
- [Position-blind index spectrum](
  ../companions/properties/position-blind-index-spectrum.md) — the
  expectation-flat null and permutation-band protocol used by the N1
  falsifier.
- [Short-window discrepancy](short-window-discrepancy.md) (candidate #10)
  — the one-body marginal this candidate's mean-square bound would
  control.
- [Sub-CRT strike decoherence](sub-crt-strike-decoherence.md) (candidate
  #26) — the frequency-resolved companion; its premise (A) is the
  head-event version of the same typicality.

## Measurement Obligations

Ordered algebra-first:

1. **N3 — exact restricted Gram computation.** For the measured heads and
   windows (existing datasets), compute `G^{(W)}` exactly: diagonals,
   off-diagonals, and their ratios to the typical profile and the
   conductor-factor prediction. This is exact finite arithmetic on real
   data, not sampling, and directly reads how near the hypothesis stands.
2. **N1 — window span-regression falsifier.** Regress each layer's
   centered window strikes on the past class `H_past`; coefficients and
   residual norms against the permutation band. Subsumes pairwise and
   single-frequency tests; bounded falsifier: any layer/head whose
   normalized correlation exceeds the band by a fixed margin refutes the
   uniform-`kappa` form.
3. **Spectra (E1 of candidate #26) — context only.** Demoted from primary
   experiment: any spectrum test is one basis of the span regression.

## Limitation

- **Necessity, not just difficulty.** The [Past-Span Saturation property](
  ../properties/sieve-sequence/past-span-saturation-does-not-determine-placement.md)
  proves that accumulating complete-period constraints can never determine
  placement: the full past span is equivalent to the per-fiber quota, and
  every fiber-admissible placement satisfies every innovation identity.
  A local/window input is structurally irreplaceable — no global identity
  can substitute for this candidate.

- **No proof route for the local form is known.** The global innovation
  identity gives no window leverage by itself (the `LR` Bessel
  obstruction); typicality of a rigid interval for the class `g_i h` is
  the same wall as the conductor-decay concentration, now in the
  strongest basis. The candidate names the wall's door, not an opening.
- **The composition into the terminal chain is not proved here.** The
  mean-square window bound is the right *shape*; converting it into the
  `#23 -> #24` energy budget or #10's two-sided bound requires those
  chains' own steps.
- **Finite evidence transfers nothing.** N3/N1 can refute or calibrate
  `kappa`; they cannot establish the uniform bound over all layers and
  heads.
- **The adaptive-weight form is stronger than what N1 tests.** The
  hypothesis is stated for the explicit class `H_past`; the terminal
  chain ultimately needs past-measurable adaptive weights, a strictly
  larger class.

## Related

- [Sub-CRT strike decoherence](sub-crt-strike-decoherence.md) — #26, the
  frequency-resolved form of the same local typicality.
- [Short-window discrepancy](short-window-discrepancy.md) — #10, the
  one-body marginal.
- [Cumulative weighted collision budget](cumulative-weighted-collision-budget.md)
  — #21, the terminal chain this candidate's mean-square bound would
  feed.
- Ticket `tickets/active/spectral-positional-filter-analysis-2026-08-18.md`
  — working memory for N3/N1.
