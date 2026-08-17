# Random-Like Merge Survival

**Probabilistic benchmark:** Proved within the independent random-filter model.

**Candidate hypothesis:** Deterministic transference to the real filter is
unproved and potentially false.

**Conditional implication:** Mathematically proved from the stated error bound.

**Empirical status:** REINFORCED — `destruction_rate < 2/p` in 186/186 window-pass transitions, shrinking like `p^-1.6` (real filter ever further below the benchmark); deterministic transference still unproved. See "Empirical status" section.

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

## Realized 0-to-1 Destruction Diagnostic

The [realized filter adversariality score](../properties/sieve-sequence/realized-filter-adversariality-score.md)
uses this candidate's structurally closer uniform-random-residue benchmark

```math
d_p=\frac2p
```

to calibrate a realized destruction fraction `f=K/L` through the anchors

```math
C_p(0)=0,
\qquad
C_p(d_p)=\frac12,
\qquad
C_p(1)=1.
```

Score `0` means no gap in the typed population was destroyed, `1/2` is the
random-residue/complete-copy benchmark anchor, and `1` is local extinction.
The midpoint is a normalization point, not evidence that a deterministic
filter behaved randomly.

For observed full-window counts,

```math
C_{obs}=C_p(K/L)
```

is the realized score. For consecutive primes `p<q` with `p>=5`, let `A(p,q)`
be the exact accepted-strike count, not the raw multiple count. Then

```math
C_{cap}
=
C_p\!\left(
\min\!\left(1,\frac{A(p,q)}{L(p,q)}\right)
\right)
```

is a proved full-window capacity ceiling. Neither quantity is a probability or
a proof of deterministic transference.

The independent-deletion benchmark `2/p-1/p^2` remains valid for its own model,
but it would define a different midpoint calibration. The Filter Adversariality Score property intentionally
uses the uniform-residue rate because one modular filter selects one residue
class globally.

Across the 186 audited unique clean full-window transitions:

- `C_obs` has median `0`, unweighted finite-transition mean
  `0.044177363545902307`, and maximum `21/44`; all 186 observations are below
  `1/2`;
- `C_cap` has median `0.1285745802948713`, unweighted finite-transition mean
  `0.16908125524560394`, and maximum `61/110`; all 186 capacity ceilings are
  below `1`.

At `(p,q)=(7,11)`, the closest observed benchmark ratio is

```math
\frac{K/L}{2/p}=\frac{21}{22},
\qquad
C_{obs}=\frac{21}{44}.
```

These are finite full-window outcomes and finite-instance capacity bounds. The
current data contains neither `L_D` nor `K_D`, so it supplies no observed
annular score or numeric annular capacity ceiling. Candidate #11's hypothesis
remains the same deterministic discrepancy/transference statement and is not
discharged by the calibration or the measurements.

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

## Empirical status (window scale, p to ~19000)

Source: `python/src/sieve_sequence/window_cli.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantities: `destruction_rate = destroyed/G_local`
(actual fraction of 2-gaps the real filter destroys) vs the uniform-residue
benchmark `2/p`. Full data in
`data/candidates/window-measurements{,-sparse}.csv`.

The concrete sufficient condition `destruction_rate < 2/p` holds in **186/186**
transitions — the real modular filter destroys a strictly smaller fraction of
2-gaps than the uniform-residue benchmark predicts, in every measured window.

The gap widens sharply with p:

| range | destruction_rate (max) | benchmark 2/p (median) |
|-------|------------------------|------------------------|
| dense (p 5..991) | 0.333 (at (5,7)) | 0.004 |
| sparse (p ~1000..19000) | 0.00008 | 0.0001 |

Trend (log-log, over transitions with `destruction_rate > 0`, n=91):
`destruction_rate ~ p^(-1.62)`, Pearson r = -0.991 against log p. The actual
destruction rate decays superlinearly; the benchmark `2/p` decays exactly like
`p^(-1)` (r = -1.000). So the real filter falls below the benchmark by an
ever-growing margin — the opposite of what an adversarial "worst-case" reading
would assume.

### No counterexample

Zero failures of `destruction_rate < 2/p`. (Note: the *independent*-deletion
benchmark `2/p - 1/p^2` is even smaller; the data was checked against the
uniform-residue benchmark `2/p`, the structurally closer of the two models.)

### What this does and does not establish

- **Does:** show that, at window scale to p~19000, the real filter is reliably
  *less* destructive than the uniform-residue random model, and the margin
  grows like `p^0.6` (difference of the two fitted exponents). This supplies a
  favorable benchmark and target margin; it does not show that the modular
  filter samples local patterns randomly. A proof using #11 may target
  `destruction_rate <= 2/p` without contradicting the measured range.
- **Does not:** discharge the candidate's actual obligation, which is a
  *non-circular deterministic* transference bound (`epsilon_p` existing and
  being small enough). Measurement cannot confirm an existential tolerance; it
  can only show a wide finite-sample margin. The run does not prove recurrence
  at infinitely many stages; a deterministic bound that did recur would imply
  infinitely many certificates through the conditional argument above.

## Strategic assessment after empirical review

This is a useful benchmark and should be kept in one file: the independent and
uniform-residue models calibrate the scale a deterministic theorem would need
to match. The observed decline in `destroyed/G_local`, however, partly reflects
the rapid growth of the denominator and does not by itself establish
random-like sampling or transference.

Proof priority is medium as a framework and lower as a direct probabilistic
argument. Its strongest role is to supply explicit target margins for the
arithmetic candidates #12 and #13. Any proof must derive the error after
conditioning on earlier filters; simply fitting the observed destruction rate
would be circular.
