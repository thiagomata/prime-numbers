# Empirical Verification of $G_{\text{local}} > p$ Crossover

**Created:** 2026-06-15
**Status:** In Progress

---

## Goal

Build an empirical runner to compute $G_{\text{local}}$ (number of 2-gaps in $[p_{k+1}, p_{k+1}^2]$) across sieve sequence layers up to $p \approx 1000$, and measure the crossover point where $G_{\text{local}}$ permanently exceeds $p_{k+1}$.

This tests the core claim from the capacity argument: that the number of inherited 2-gaps in the safe zone eventually outpaces the filter's local bullets ($p$).

---

## Current State

- Verified MemCycle code exists but uses `stainless.collection.List` — recursive, not optimized for large computation
- Draft article `draft-generalized-gap-dynamic.md` presents the capacity argument
- Learnings saved in `articles/learnings-capacity-argument.md`
- **Verification:** 5303 valid, 0 invalid ✅

## Expected State

- A standalone Scala runner in `v1.seq.sieve.empirical` that outputs CSV to `data/empirical/results.csv`
- CSV contains columns: `k, p, p_next, G_local, delta, extinction`
- Data up to $p \approx 1000$ showing the trajectory of $G_{\text{local}}$ vs $p$

---

## Approach

Segmented sieve — compute numbers coprime to $M_k$ in $[p_{k+1}, p_{k+1}^2]$ using a boolean array, scan for adjacent pairs differing by 2. No full MemCycle needed, no Stainless, no Spark.

**Package structure:**
```
src/main/scala/v1/seq/sieve/empirical/
  Types.scala          — OutputRow case class
  SegmentedSieve.scala — Sieve logic
  GapAnalyzer.scala    — 2-gap counting
  CsvWriter.scala      — CSV output
  EmpiricalRunner.scala — Main loop
```

---

## Risks

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| $G_{\text{local}}$ never exceeds $p$ | Low | Runner always runs to bound; data is honest regardless |
| Crossover happens but reverses later | Medium | Scan to $p=1000$ to observe full trend |
| Window size exceeds memory for single array | Low | $p=1000$ safe zone = 1M — trivial. Will add block segmentation if needed for larger bounds. |
| Overlaps with verified code | Low | New package, no dependency on Stainless code |

## Assumptions

- $G_{\text{local}}$ can be computed via segmented sieve over $[p_{k+1}, p_{k+1}^2]$ without constructing the full MemCycle
- A number $n$ is coprime to $M_k = \prod_{i=1}^k p_i$ iff $n \not\equiv 0 \pmod{p_i}$ for all $p_i \le p_k$
- Two consecutive survivors differing by 2 in the safe zone correspond to a 2-gap in the sequence
- The sequence head rotation doesn't affect which 2-gaps fall in the safe zone (the safe zone is a fixed interval on the integer line)

## Hypotheses

1. **Crossing Hypothesis:** There exists a prime $p_c$ such that for all $p_k \ge p_c$, $G_{\text{local}} > p_{k+1}$.
2. **Monotonicity Hypothesis:** After the crossing point, $\delta = G_{\text{local}} - p_{k+1}$ grows monotonically (or at least never permanently dips back).
3. **Domination Hypothesis:** The delta grows faster-than-linear with $p$, confirming the geometric expansion outpaces the linear bullet cap.

## Validation

1. Compare discovered 2-gaps with known twin primes up to 1000. Every twin pair $(q, q+2)$ with $q \ge 3$ should be a 2-gap in the safe zone at the layer where $p_{k+1} = q$.
2. Manually inspect the CSV for consistency.
3. Cross-check against the known twin prime count in intervals.

## Related Tickets

None.

## Rules Followed

- **AGENTS.md §ticket-first:** This ticket created before implementation (>2 tool calls expected).
- **AGENTS.md §green-to-green:** Verify run before creation (5303 valid ✅).
- **AGENTS.md §never-destroy:** No modification of existing files or verified code.
- **AGENTS.md §small-changes:** Each file will be written independently.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-15 | Conversation identified $G_{\text{local}} > p$ as key testable metric. Burden of proof can be inverted with empirical data. | Create ticket, implement runner. |

## Completed

All 6 files written and tested. Full run to $p=1000$ completed in 676s (168 primes).

## Findings

### Crossing Hypothesis: CONFIRMED ✅
- Permanent crossover at $p=37$ (k=12): $G_{\text{local}}=42$, $\delta=+5$
- From $p=37$ onward, extinction is **permanently false** — $G_{\text{local}} > p$ for all higher primes tested
- First transient crossover at $p=29$ (k=10), reverted at $p=31$ (extinction=true again)

### Monotonicity Hypothesis: QUALIFIED ✅
- After permanent crossover ($p \ge 37$), only **1 dip** observed: $p=73$ where $\delta$ went $51 \to 50$
- No dips below the crossover threshold — delta never goes negative after $p=37$
- The single dip is minor and does not threaten the crossing claim

### Domination Hypothesis: CONFIRMED ✅ (super-linear growth)
| $p$ | $G_{\text{local}}/p$ | $\delta/p$ |
|-----|---------------------|------------|
| 37  | 1.135              | 0.135      |
| 233 | 3.146              | 2.146      |
| 463 | 4.879              | 3.879      |
| 727 | 6.546              | 5.546      |
| 991 | 8.089              | 7.089      |

The $G/p$ ratio grows steadily — no signs of saturation up to $p=1000$.

### Key Datapoints
- Last extinction: $p=31$, $G_{\text{local}}=30$, $\delta=-1$
- Final entry ($p=991$): $G_{\text{local}}=8016$, $\delta=7025$
- Total 2-gap count at $p=991$ is $8\times$ the filter bullet count

## Learnings

1. **The capacity argument holds empirically** up to $p=1000$: $G_{\text{local}}$ permanently exceeds $p$ from $p=37$ onward, and the gap grows monotonically in all but one minor fluctuation.

2. **BigInt conversion done**: All empirical files now use `BigInt` throughout (`OutputRow`, `SegmentedSieve`, `GapAnalyzer`, `EmpiricalRunner`). The segmented sieve range `[p, p^2]` stays within memory limits for $p$ up to the order of $10^5$ ($10^{10}$ range → 10B booleans is too large for a flat array; block segmentation would be needed beyond ~$2 \times 10^5$).

3. **Performance bottleneck**: The runner spends most of its time in the inner sieve loop (marking multiples of all smaller primes). Total runtime 676s for $p \le 1000$.

4. **Choice A (Jacobsthal Horizon)**: The empirical data supports bounding the maximum gap between survivors. $G_{\text{local}}/p$ grows roughly linearly with $p$ (from 1.13 at $p=37$ to 8.09 at $p=991$), suggesting the density of 2-gaps in $[p, p^2]$ increases as $p$ grows. This is stronger than what the structural proof alone provides.

5. **No counterexample found**: Not a single $p \ge 37$ shows extinction. The engine's core claim — that 2-gaps permanently outnumber bullets — is empirically validated across the full range tested.

## Next Steps

1. ~~Write `Types.scala`~~ ✅
2. ~~Write `SegmentedSieve.scala`~~ ✅
3. ~~Write `GapAnalyzer.scala`~~ ✅
4. ~~Write `CsvWriter.scala`~~ ✅
5. ~~Write `EmpiricalRunner.scala`~~ ✅
6. ~~Run up to $p=1000$, inspect results~~ ✅
7. ~~Update ticket with findings~~ ✅
8. Consider extending to $p=10^5$ with block segmentation for stronger empirical confidence
