# Local Pattern-Residue Balance

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

## Candidate Hypothesis

Fix an incoming prime `p`, a local window `J`, and a finite gap word

```math
w=(g_1,\ldots,g_m).
```

An occurrence beginning at `x` visits the vertex offsets

```math
T(w)=\{0,g_1,g_1+g_2,\ldots,g_1+\cdots+g_m\}.
```

Let `N_w(J) > 0` be the number of complete occurrences of `w` in `J`, and let
`N_{w,a}(J)` count those whose starting value is congruent to `a` modulo `p`.
The candidate is that, for every residue class `a`,

```math
\left|
N_{w,a}(J)-\frac{N_w(J)}p
\right|
\le E_p(J,w),
\qquad
E_p(J,w)\ge0.
```

The statement can be required for every finite word, for all words of bounded
length, or for another gap-agnostic family large enough for the intended
application.

## Forbidden Start Residues

Installing `p` removes an occurrence if at least one of its vertices is
congruent to zero modulo `p`. Define

```math
R_p(w)=\{-t\bmod p:t\in T(w)\},
\qquad
\nu_p(w)=|R_p(w)|.
```

The use of distinct residues is essential: different vertices can produce the
same forbidden start class. Assume

```math
\nu_p(w)<p.
```

If `K_w(J)` is the number of occurrences destroyed by the filter, the union
bound and the candidate inequality give

```math
\begin{aligned}
K_w(J)
&\le\sum_{a\in R_p(w)}N_{w,a}(J)\\
&\le\nu_p(w)
\left(\frac{N_w(J)}p+E_p(J,w)\right).
\end{aligned}
```

## Why The Candidate Is Sufficient

The number of surviving occurrences is at least

```math
\begin{aligned}
N'_w(J)
&\ge N_w(J)-K_w(J)\\
&\ge
N_w(J)\left(1-\frac{\nu_p(w)}p\right)
-\nu_p(w)E_p(J,w).
\end{aligned}
```

Therefore the gap-agnostic sufficient condition is

```math
\nu_p(w)E_p(J,w)
<
N_w(J)\left(1-\frac{\nu_p(w)}p\right).
```

It implies `N'_w(J) > 0`.

For the single-gap word `w = (d)`, the offsets are `{0,d}`. Hence

```math
\nu_p((d))=
\begin{cases}
2,&p\nmid d,\\
1,&p\mid d.
\end{cases}
```

In particular, for `d = 2` and `p > 2`, the condition becomes

```math
2E_p(J,(2))
<
N_{(2)}(J)\left(1-\frac2p\right).
```

If `J` is square-safe, the surviving occurrence certifies a twin-prime pair.
The candidate itself, however, applies uniformly to arbitrary finite gap
words.

## Relation To Other Candidates

This is a deterministic, phase-sensitive equidistribution condition. It asks
how each old local pattern is distributed across the actual residue classes
used by the filter. That differs from comparing the deterministic filter with
a probabilistic model.

- [Uniform local observable sampling](uniform-local-observable-sampling.md)
  compares the hit set with the whole local population.
- [Random-like merge survival](random-like-merge-survival.md) compares marked
  local behavior with selected random benchmarks.

## Established Inputs

- [Copy-index filter frequency](../properties/sieve-sequence/copy-index-filter-frequency.md)
- [Stable absence and copy-or-merge](../properties/sieve-sequence/absence-of-two-gaps-is-stable.md)
- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)

## Limitation

Complete-period residue counts do not prove this bound in a short window.
Pointwise balance for every residue class and every finite word is a strong
local equidistribution demand; a useful proof may need a bounded word family,
averaging over stages, or a weaker norm. Matching only the average numerical
gap or average merge size is insufficient because it does not prevent the
filter from concentrating on one local pattern.

## Empirical status (window scale, p to ~19000)

Source: `candidates/analysis/measure_candidates.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantity: for the word `w=(2)`, `residue_max_dev =
max_a |N_{w,a} - N_w/p|`, the worst deviation of any residue class's 2-gap-start
count from uniform. **Low-power measurement**: one window is a small sample of
the whole residue distribution, so this is a weak test of the candidate.

**Important — a corrected reading.** A first pass flagged `residue_max_dev` as
*growing* with p (6 -> 43 -> 74), which looked unfavorable. That was an artifact
of measuring an absolute count deviation without normalizing for sample size:
counts grow with the window, so their absolute deviation grows too. Normalizing
by the expected fluctuation scale `sqrt(G_local)` (standard for a uniform
distribution) reverses the conclusion:

| quantity | dense (p 5..991) | sparse (p ~1000..19000) | trend |
|----------|------------------|--------------------------|-------|
| `residue_max_dev` (absolute) | med 6.2, max 10.3 | med 43.2, max 73.7 | grows p^(+0.54), r=+0.97 |
| `residue_max_dev / sqrt(G_local)` (normalized) | med 0.14, max 0.43 | med 0.067, max 0.096 | **shrinks** p^(-0.09), r=-0.87 |

The *relative* deviation shrinks with p: the residue distribution gets **closer
to uniform at scale**, not further from it. The earlier "unfavorable flag" on
this candidate is withdrawn.

### What this does and does not establish

- **Does:** show that at window scale the residue-class distribution of 2-gap
  starts approaches uniform as p grows (normalized deviation shrinks, r=-0.87).
  This is consistent with — mildly supportive of — the candidate's balance
  demand, at least for the word `(2)` and in the relative sense that matters.
- **Does not:** test arbitrary finite words (only `w=(2)` was measured), nor
  prove the pointwise bound for all p. The measurement is low-power by nature
  (one window = one sample). Window-scale only; does not touch infinititude.
