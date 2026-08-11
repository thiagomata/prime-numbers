# Random-Like Merge Survival

**Probabilistic benchmark:** Proved within the independent random-filter model.

**Candidate hypothesis:** Deterministic transference to the real filter is
unproved and potentially false.

**Conditional implication:** Mathematically proved from the stated error bound.

## Purpose

The random calculation and the deterministic candidate belong together. The
random model supplies a survival rate and a quantitative error budget; the
candidate asks whether the real modular merge process is close enough to that
benchmark in a square-safe window.

## Proved Random Benchmark

Suppose a model filter independently removes each accepted value with
probability `1/p`. A 2-gap survives exactly when neither endpoint is removed,
so

```math
P_{survive}=\left(1-\frac1p\right)^2,
\qquad
P_{destroy}=\frac2p-\frac1{p^2}.
```

After filter `3`, local 2-gaps are endpoint-disjoint. Their endpoint deletion
events are therefore independent in this model. If a safe window contains `L`
such gaps, then

```math
P(\text{all }L\text{ destroyed})
=\left(\frac2p-\frac1{p^2}\right)^L,
```

and hence

```math
P(\text{at least one survives})
=1-\left(\frac2p-\frac1{p^2}\right)^L.
```

This is a theorem about the random model only. The real sieve filter is
deterministic and does not inherit this probability statement automatically.

## Uniform Random-Residue Benchmark

A structurally closer model chooses one forbidden residue class uniformly
modulo `p`. For `p > 2`, the two endpoints of a 2-gap occupy distinct residue
classes. The destruction and survival probabilities for one gap are therefore

```math
d_{mathrm{res}}=\frac{2}{p},
\qquad
s_{mathrm{res}}=1-\frac{2}{p}.
```

Unlike independent deletion, one random residue choice acts on every gap at
once. Destruction events for different gaps can be correlated, so this model
does not justify raising `d_res` to the power `L` to calculate the probability
that all `L` gaps are destroyed.

## Deterministic Random-Like Candidate

Fix `p > 2` and a square-safe window containing `L > 0` complete post-3
2-gaps. Let `K` be the number destroyed by the real filter, so

```math
0\le K\le L.
```

Choose either the independent-deletion destruction rate or the
uniform-random-residue destruction rate:

```math
d_p=d_{\mathrm{ind}}=\frac2p-\frac1{p^2}
\qquad\text{or}\qquad
d_p=d_{\mathrm{res}}=\frac2p.
```

In both cases, `p > 2` gives

```math
0\le d_p<1.
```

The candidate hypothesis is that, for infinitely many transitions, the real
destruction proportion is close to one selected benchmark:

```math
\left|\frac KL-d_p\right|\le\varepsilon_p
\qquad\text{and}\qquad
\varepsilon_p<1-d_p.
```

## Why The Candidate Is Sufficient

The error bound gives

```math
\begin{aligned}
\frac KL
&\le d_p+\varepsilon_p\\
&<1.
\end{aligned}
```

Hence `K < L`, so `L - K > 0`. At least one square-safe 2-gap survives whenever
the deterministic error remains inside the selected model's positive margin.

## Gap-Agnostic Transference Form

A more reusable hypothesis can range over every finite local gap word `A`, not
only `(2)`. Let `I_A` be the nonempty set of complete occurrences of `A` in the
chosen window, and let `psi` be any bounded function of the deletion marks in
a fixed-radius neighborhood of an occurrence. A gap-agnostic transference
condition has the form

```math
\left|
\frac1{|I_A|}\sum_{i\in I_A}\psi(\text{actual marks near }i)
-\mathbb E_{\mathrm{model}}[\psi]
\right|
\le\eta_p\|\psi\|_\infty.
```

The schema itself does not privilege 2-gaps. To obtain the candidate above,
take `I_(2)` to be the `L > 0` complete 2-gap occurrences and let `psi` be the
indicator that at least one of the two endpoint marks is deleted. Its actual
average is `K/L`, its selected-model expectation is exactly `d_p`, and its
supremum norm is `1`. The schema then gives

```math
\left|\frac KL-d_p\right|\le\eta_p.
```

Thus `eta_p < 1 - d_p` is sufficient. Other choices of `A` and `psi` test
arbitrary gap values, finite gap words, merge arity, clusters, or large-spacer
incidence using the same proposed property.

## Established Inputs

- [2-gap endpoint isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)
- [Short-window discrepancy candidate](short-window-discrepancy.md)

## Limitation

Calling a deterministic filter “random-like” is not evidence. A useful proof
must derive a non-circular discrepancy bound from its modular arithmetic,
preferably for a gap-agnostic class of local observables. Defining similarity
directly as “approximately the right number of 2-gaps survive” would merely
rename the desired conclusion. Moreover, the independent model permits both
endpoints of one gap to be deleted, whereas a prime residue filter with
`p > 2` does not; their destruction rates differ by `1/p^2`. The random-residue
model fixes that one-gap mismatch but retains correlations between different
gaps. Neither benchmark alone proves deterministic survival.
