# Empirical Analysis of $G_{\text{local}}$: The Local 2-Gap Density in Sieve Sequences

**[Draft]** — This article reports empirical results, not formal proofs. The computational functions used are `@extern` (not Stainless-verified). See Section 5.3 for limitations.

**Author:** Mata, T. H.  
Independent Researcher  
**Email:** thiago.mata@email.com  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

We present an empirical investigation of $G_{\text{local}}(p)$ — the number of 2-gaps (adjacent survivors differing by 2) in the interval $[p, p^2]$ after sifting by all primes less than $p$. This quantity is the critical input to the capacity argument for twin prime persistence: if $G_{\text{local}}(p) > p$ for all sufficiently large $p$, the sieve filter lacks the "bullets" to destroy all local 2-gaps. Using a segmented sieve implemented with `BigInt` arithmetic, we compute $G_{\text{local}}$ for all primes $3 \le p \le 997$ (166 layers). The data confirms: permanent crossover at $p=37$, $G_{\text{local}}/p$ ratio growing from 1.13 to 8.09 across the range, and strict monotonicity of $\delta = G_{\text{local}} - p$ after the crossover layer with exactly one minor fluctuation. The results support the claim that the geometric expansion of the safe zone $[p, p^2]$ outpaces the linear bullet count $p$ by an increasingly wide margin. **These are empirical results, not formal proofs.**

---

## Property Index

| # | Property | Statement | Status |
|---|----------|-----------|--------|
| 1 | Crossover | $\exists p_c$ s.t. $\forall p \ge p_c$, $G_{\text{local}} > p$ | [Empirical — $p_c = 37$ up to $p=997$] |
| 2 | Monotonicity | $\delta$ never permanently dips back after crossover | [Empirical — single fluctuation at $p=73$; no extinction] |
| 3 | Domination | $\delta$ grows faster-than-linear with $p$ | [Empirical — $\delta/p$ increases from 0.14 to 7.09] |
| 4 | Extinction absence | No $p$ after $p=37$ has $G_{\text{local}} \le p-1$ | [Empirical — all 154 subsequent primes satisfy $G_{\text{local}} > p$] |

Status key: `[Empirical]` = observed in computed data; does not constitute a formal proof.

---

## 1. Motivation

The Twin Prime Conjecture for this sieve framework reduces to a single positional claim:

> In $A_k$ (the $k$-th gap cycle), some 2-gap exists in the safe zone $[p_{k+1}, p_{k+1}^2]$.

Let $G_{\text{local}}(p_{k+1})$ be the number of 2-gaps inherited from $A_k$ that fall in this window. The filter at layer $k+1$ carries at most $p_{k+1} - 1$ bullets (its stride strikes at $p, 2p, \dots, (p-1)p$ within the safe zone). The **extinction condition** — where the filter could destroy every local 2-gap — is:

$$G_{\text{local}}(p) \le p - 1$$

If this inequality fails permanently from some layer onward, the filter is structurally incapable of extinguishing the local 2-gap population, and twin prime candidates persist indefinitely.

This article tests that inequality empirically across all primes up to 1000. See [Gap Dynamics in Sieve Sequences](../articles/gap-dynamics.md) for the formal context and [Learnings: Capacity Argument](../articles/learnings/learnings-capacity-argument.md) Sections 10 and 16 for the theoretical boundary.

---

## 2. Method

### 2.1 Segmented Sieve

For each prime $p \ge 3$, we compute the survivors in $[p, p^2]$ after removing all multiples of primes smaller than $p$. The survivors are integers $n$ such that:

$$n \not\equiv 0 \pmod{p_i} \quad \forall p_i < p$$

This is equivalent to being coprime to the primorial $M_{<p} = \prod_{p_i < p} p_i$.

The segmented sieve isolates the window $[p, p^2]$ where twin primes could exist after filtering by all smaller primes. By computing survivors directly instead of simulating the full cycle, we avoid the exponential blowup of the full MemCycle.

This is the empirical approach to the local density question: can we verify that $G_{\text{local}} > p$ for all sufficiently large $p$? If so, the sieve lacks the capacity to destroy all 2-gaps.

Implementation uses a boolean array of size $(p^2 - p + 1)$ with `BigInt` arithmetic for the coordinates:

```scala
def survivorsInRange(lo: BigInt, hi: BigInt, primes: Array[BigInt]): List[BigInt]
```

This function is implemented in the [
  SegmentedSieve::survivorsInRange
](
  ../../src/main/scala/v1/chapter6/seq/sieve/empirical/SegmentedSieve.scala
) as an `@extern` function (not Stainless-verified).

### 2.2 2-Gap Counting

A 2-gap is a pair of consecutive survivors $(r, r+2)$. This is the exact structure that corresponds to twin prime candidates after filtering.

The capacity argument hinges on comparing the number of 2-gaps ($G_{\text{local}}$) against the number of filter bullets ($p-1$). If $G_{\text{local}} > p-1$, at least one 2-gap survives each filter application — the sieve cannot extinguish all twin prime candidates.

```scala
def countTwoGaps(survivors: List[BigInt]): BigInt
```

This function is implemented in the [
  GapAnalyzer::countTwoGaps
](
  ../../src/main/scala/v1/chapter6/seq/sieve/empirical/GapAnalyzer.scala
) as an `@extern` function (not Stainless-verified).

### 2.3 Output Metrics

For each prime $p$ we record:

| Metric | Definition |
|--------|------------|
| $k$ | Prime index (1-based) |
| $p$ | The prime $p_k$ |
| $p_{\text{next}}$ | The next prime $p_{k+1}$ |
| $G_{\text{local}}$ | 2-gap count in $[p, p^2]$ |
| $\delta$ | $G_{\text{local}} - p$ |
| Extinction | $\delta \le 0$ |

### 2.4 Range

All 166 primes from $p=3$ to $p=997$ (the largest prime $\le 1000$). Total runtime: 676 seconds on JVM 21.

### 2.5 Reproducibility

To reproduce the results:

```bash
# Run the empirical analysis (requires sbt and JVM 21+)
sbt 'runMain v1.seq.sieve.empirical.EmpiricalRunner'
```

Expected output: `data/empirical/results.csv` with 167 rows (header + 166 data rows). Expected runtime: approximately 11 minutes on a modern machine.

---

## 3. Results

### 3.1 Crossover Analysis

**First transient crossover:** $p=29$ (k=10): $G_{\text{local}}=30$, $\delta=+1$.

This reverts at $p=31$ (k=11): $G_{\text{local}}=30$, $\delta=-1$, extinction=true.

**Permanent crossover:** $p=37$ (k=12): $G_{\text{local}}=42$, $\delta=+5$.

From $p=37$ onward, $\delta > 0$ for all 154 subsequent primes. No reversion.

| Stage | $p$ | $k$ | $G_{\text{local}}$ | $\delta$ | Extinct? |
|-------|-----|-----|-------------------|----------|----------|
| Pre-crossover | 3 | 2 | 3 | 0 | true |
| Pre-crossover | 5 | 3 | 4 | -1 | true |
| Pre-crossover | 7 | 4 | 5 | -2 | true |
| Pre-crossover | 11 | 5 | 8 | -3 | true |
| Pre-crossover | 13 | 6 | 10 | -3 | true |
| Pre-crossover | 17 | 7 | 16 | -1 | true |
| Pre-crossover | 19 | 8 | 18 | -1 | true |
| Pre-crossover | 23 | 9 | 21 | -2 | true |
| Transient | **29** | **10** | **30** | **+1** | **false** |
| Reversion | 31 | 11 | 30 | -1 | true |
| **Permanent** | **37** | **12** | **42** | **+5** | **false** |

### 3.2 Growth Trajectory

The ratio $G_{\text{local}}/p$ grows steadily across the range:

| $p$ | $k$ | $G_{\text{local}}$ | $\delta$ | $G/p$ | $\delta/p$ |
|-----|-----|-------------------|----------|-------|------------|
| 37 | 12 | 42 | +5 | 1.14 | 0.14 |
| 71 | 20 | 122 | +51 | 1.72 | 0.72 |
| 113 | 30 | 234 | +121 | 2.07 | 1.07 |
| 173 | 40 | 456 | +283 | 2.64 | 1.64 |
| 233 | 51 | 733 | +500 | 3.15 | 2.15 |
| 353 | 71 | 1484 | +1125 | 4.20 | 3.19 |
| 467 | 91 | 2290 | +1823 | 4.90 | 3.90 |
| 607 | 112 | 3590 | +2977 | 5.91 | 4.90 |
| 739 | 132 | 4935 | +4192 | 6.68 | 5.67 |
| 881 | 153 | 6581 | +5698 | 7.47 | 6.47 |
| **997** | **168** | **8016** | **+7025** | **8.09** | **7.09** |

The $G/p$ ratio increases monotonically (with one small fluctuation, see Section 3.3) from 1.14 at the permanent crossover to 8.09 at the maximum tested $p$. The growth shows no signs of saturation.

### 3.3 Monotonicity

After permanent crossover ($p \ge 37$), $\delta$ strictly increases at all but one step:

**Single fluctuation:** $p=73$ where $\delta$ drops from 51 (at $p=71$) to 50 (at $p=73$).

This is a minor dip of 1 unit — well above the extinction boundary ($\delta=0$). No dip brings $\delta$ anywhere near the danger threshold.

After $p=73$, $\delta$ resumes strict monotonic increase for all remaining 153 primes.

### 3.4 Extinction Events

| Event | $p$ | $\delta$ | Detail |
|-------|-----|----------|--------|
| Last extinction | 31 | -1 | $G_{\text{local}}=30$ vs $p=31$ |
| Boundary cases | 3, 17, 19, 31 | $\delta=0$ or -1 | Tenuous but pre-crossover |
| Post-crossover | $\ge 37$ | $\delta \ge 5$ | Never returns to extinction |

### 3.5 Complete Data

Full dataset available at `data/empirical/results.csv` (167 rows including header). All 166 primes from $p=3$ through $p=997$ are covered.

---

## 4. Analysis

### 4.1 The $G/p$ Ratio Growth

The ratio $G_{\text{local}}/p$ grows approximately linearly with $p$ across the observed range. A linear regression of $G/p$ against $p$ yields:

$$\frac{G}{p} \approx 0.0071 \cdot p + 0.97 \quad (R^2 > 0.99)$$

At this rate, $G/p$ would reach 10 at approximately $p \approx 1270$ and 100 at $p \approx 13900$.

This empirical trend suggests the local 2-gap density in $[p, p^2]$ does not approach extinction but instead **strengthens** relative to $p$ as the sieve progresses to higher layers.

### 4.2 Growth Rate of $\delta$

The surplus $\delta = G_{\text{local}} - p$ grows faster than linearly. The ratio $\delta/p$ increases from 0.14 at $p=37$ to 7.09 at $p=997$, tracking closely with $p/140$.

This indicates that $G_{\text{local}}$ itself grows superlinearly in $p$, which is consistent with the quadratic expansion of the safe zone window $[p, p^2]$ — the window captures more of the global cycle as $p$ grows, and thus $G_{\text{local}}$ scales roughly with $p^2$ times the global 2-gap density.

### 4.3 Comparison with Global Density

Mertens' theorem gives the global density of 2-gaps in the full primorial cycle:

$$\rho_k = \prod_{i=3}^{k} \frac{p_i - 2}{p_i - 1} \approx \frac{C}{(\ln p_k)^2}$$

If 2-gaps were uniformly distributed within each cycle copy, we would expect:

$$G_{\text{local}} \approx (p^2 - p) \cdot \rho_{\text{prev}}$$

The empirical data exceeds this uniform estimate by a factor of approximately 2-3 across the range, suggesting 2-gaps are **more densely clustered in the early positions** of the cycle than the global average would predict. This is consistent with the 2-gap isolation property (no adjacent 2-gaps) not being the dominant constraint on their positions.

### 4.4 The Single Dip at $p=73$

The dip at $p=73$ ($\delta: 51 \to 50$) is structurally interesting but insignificant for the capacity argument. It occurs at a transition between closely-spaced primes ($p=71$, $p=73$). The safe zone for $p=73$ is $[73, 5329]$, which is almost identical to $p=71$'s safe zone $[71, 5041]$, so the comparable $G_{\text{local}}$ values are expected — the slight decrease is likely due to the larger prime having a higher bullet count ($p=73$ vs $p=71$) without a corresponding expansion of the window.

This pattern does not recur for any other adjacent pair in the dataset.

### 4.5 Performance Characteristics

The segmented sieve ran in 676 seconds for 166 primes on JVM 21. The runtime is dominated by the inner loops of the sieve (marking multiples of smaller primes). The computational complexity is approximately:

$$O\left(\sum_{p \le 1000} \frac{p^2}{\ln p}\right)$$

For extending to $p=10^5$, a block-segmented sieve would be necessary to avoid allocating arrays of size $O(p^2)$.

---

## 5. Conclusions

### 5.1 Empirical Findings

| Hypothesis | Status | Detail |
|------------|--------|--------|
| **Crossing**: $\exists p_c$ s.t. $\forall p \ge p_c$, $G_{\text{local}} > p$ | [Empirical] | $p_c = 37$; holds for all 154 subsequent primes tested |
| **Monotonicity**: $\delta$ never permanently dips back after crossover | [Empirical] | Single minor fluctuation at $p=73$ (51→50); no extinction reversion |
| **Domination**: $\delta$ grows faster-than-linear with $p$ | [Empirical] | $\delta/p$ increases from 0.14 to 7.09 across range |

### 5.2 No Counterexample Found

Across all 166 primes tested ($3 \le p \le 997$), no prime after $p=37$ exhibits the extinction condition. The filter's maximum local bullet count ($p-1$) is permanently exceeded by the local 2-gap count from layer 12 onward.

### 5.3 Relationship to Formal Verification

The empirical data supports the capacity argument for twin prime persistence:

- The inequality $G_{\text{local}} > p$ holds for all $p \ge 37$ up to $p=997$
- The ratio $G/p$ grows monotonically, suggesting the inequality is structural

**Crucially, this is empirical evidence, not a formal proof.** The local density question ($G_{\text{local}} > p$) remains open in the formal verification sense. See [Gap Dynamics in Sieve Sequences](../articles/gap-dynamics.md) Section 6 and [Learnings: Capacity Argument](../articles/learnings/learnings-capacity-argument.md) Sections 10 and 16 for the formal boundary.

The computational functions used (`SegmentedSieve.survivorsInRange` and `GapAnalyzer.countTwoGaps`) are marked `@extern` and are **not** Stainless-verified. They are standard Scala implementations used for empirical computation, not formal verification.

### 5.4 Methodology Limitations

| Limitation | Impact | Mitigation |
|------------|--------|------------|
| Range limited to $p \le 1000$ | Cannot rule out asymptotic reversal | Trend shows no saturation; extension to $p=10^5$ planned |
| Empirical result $\neq$ proof | Does not replace a formal invariant | Use to guide invariant discovery; reduces search space |
| Array-based sieve | Memory-bound for $p > 10^5$ | Block segmentation needed for larger ranges |
| `@extern` implementation | Functions not Stainless-verified | Manual code review performed; correctness assumed for empirical purposes |

---

## 6. Data Access

The complete dataset is at `data/empirical/results.csv` with columns: `k, p, p_next, G_local, delta, extinction`.

The empirical runner is at `src/main/scala/v1/chapter6/seq/sieve/empirical/`:

- `EmpiricalRunner.scala` — main entry point
- `SegmentedSieve.scala` — survivor computation (`@extern`)
- `GapAnalyzer.scala` — 2-gap counting (`@extern`)
- `Types.scala` — data types
- `CsvWriter.scala` — CSV output

All files use `BigInt` arithmetic for arbitrary-precision coordinate handling.

---

## References

1. Mata, T. H. (2026). Gap Dynamics and Twin Prime Candidates in Sieve Sequences. `articles/gap-dynamics.md`
2. Mata, T. H. (2026). Learnings: Capacity Argument for Twin Prime Persistence. `articles/learnings/learnings-capacity-argument.md`
3. Mata, T. H. (2026). Empirical Runner and Results. `src/main/scala/v1/chapter6/seq/sieve/empirical/EmpiricalRunner.scala`
