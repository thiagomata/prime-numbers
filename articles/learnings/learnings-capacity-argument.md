# Learnings: Capacity Argument for Twin Prime Persistence

**Current assessment (2026-08-03):** Sections 1--21 preserve the historical
development of the capacity argument. Their empirical observations remain
useful, but their older claims that there is one undifferentiated remaining
density question are superseded by Sections 22--23. The properties from Terminal Harmful-Excess Energy through Copy-Block Excess Control now
separate the exhausted capacity/native-period envelopes from the live signed
residue-energy and partial-boundary problem. The properties from Divisor Local Factor through Cofactor Progression Discrepancy define a
distinct relaxed almost-prime program.

## 1. The Core Invariant (Sound)

**Worst-Case Growth Inequality:**

$$T_{k+1} \ge (p-2) \cdot T_k$$

- Proven via CRT uniformity: at most 2 copies of a 2-gap are destroyed out of $p$ concatenations
- $p \ge 5$ ensures the two destruction conditions are mutually exclusive within a single copy
- Verified in `verifyGeneralizedGrowth` (see Section 3.2 of draft)

## 2. The Isolation of 2-Gaps (Sound)

**Theorem:** For all layers $k \ge 2$ (post-3), no two 2-gaps can be adjacent in the gap cycle.
- Proof: three consecutive odd integers contain a multiple of 3, which is never coprime to $M_k$
- **Corollary:** Each filter deletion can destroy at most one 2-gap
- This caps the giant's kill efficiency at 1 per bullet

## 3. What $T_k$ Tracks

$T_k$ is the count of 2-gaps in the full periodic MemCycle (the gap sequence between consecutive coprime residues modulo $M_k$). It is **not** the count of twin primes on the integer line — a 2-gap in the cycle at position $r$ means $(r + m \cdot M_k, r + 2 + m \cdot M_k)$ are coprime to $M_k$ for all $m \ge 0$, but they may be filtered by larger primes at higher layers.

## 4. The Head-of-Stream Event

A 2-gap at position 0 in the rotated cycle at layer $k$ means the $k$-th prime $p_k$ satisfies $p_{k+1} - p_k = 2$, which IS a twin prime pair. This is because:
- $p_k$ is prime (proven: `assertHeadIsPrime`)
- $p_k + 2$ is coprime to $M_k$ (by construction — it's a 2-gap at head)
- $p_{k+1} \le p_k + 2 < p_k^2$ for all $p_k \ge 3$
- Any composite $\le p_k^2$ has a prime factor $\le p_k$, which would divide $M_k$ — impossible since $p_k + 2$ is coprime to $M_k$

So the Twin Prime Conjecture reduces to: **does a 2-gap land at position 0 for infinitely many $k$?**

## 5. The Refined Local Capacity Bound (Promising Framing)

At layer $k+1$ (processing prime $p = p_{k+1}$), the safe zone is:

$$\text{SafeZone}_k = [p_{k+1}, p_{k+1}^2]$$

**Max Local Bullets:** The filter strikes every $p_{k+1}$ steps starting from $p_{k+1}$, landing at $p, 2p, \dots, (p-1)p$. The $p$-th stride lands at $p^2$, which is the boundary. So:

$$\text{Max Local Bullets} = p - 1$$

**Incoming 2-gaps in the window:** Let $G_{\text{local}}$ be the number of 2-gaps inherited from $A_k$ (the previous layer's cycle) in the first $p^2$ positions. This is a fixed historical constant at the moment the frame begins.

**Survivors:**

$$\text{Surviving Local 2-Gaps} \ge G_{\text{local}} - (p - 1)$$

### What this achieves

It shifts the burden. The critic must now claim:

> $G_{\text{local}} \le p - 1$ for all sufficiently large $k$, despite $T_k \to \infty$ globally.

This is a strong claim requiring systematic avoidance of 2-gaps in early positions — structurally unlikely given the deterministic CRT-based construction.

## 6. Historical Empirical Results (superseded)

The table below records the old Scala `[p,p^2)` counter. That experiment is
incompatible with the canonical `[q,q^2)` transition workflow and is not
current evidence for it; physical retirement of the old runner and dataset is
still pending under the repository's file-deletion rule. Current measurements
are in `data/candidates/window-measurements.csv`, with analysis in
`empirical/sieve-sequence/FINDINGS.md` and
`empirical/sieve-sequence/FINDINGS_lineage.md`.

### 6.1 Crossover

| Event | $p$ | $k$ | $G_{\text{local}}$ | $\delta$ |
|-------|-----|-----|-------------------|----------|
| First transient | 29 | 10 | 30 | +1 |
| Reversion | 31 | 11 | 30 | -1 (extinct) |
| **Permanent** | **37** | **12** | **42** | **+5** |

From $p=37$ onward, $\delta > 0$ for all 154 subsequent primes — no reversion.

### 6.2 Growth Trajectory

The ratio $G_{\text{local}}/p$ grows steadily across the range:

| $p$ | $k$ | $G_{\text{local}}$ | $\delta$ | $G/p$ |
|-----|-----|-------------------|----------|-------|
| 37 | 12 | 42 | +5 | 1.14 |
| 71 | 20 | 122 | +51 | 1.72 |
| 113 | 30 | 234 | +121 | 2.07 |
| 173 | 40 | 456 | +283 | 2.64 |
| 233 | 51 | 733 | +500 | 3.15 |
| 353 | 71 | 1484 | +1125 | 4.20 |
| 467 | 91 | 2290 | +1823 | 4.90 |
| 607 | 112 | 3590 | +2977 | 5.91 |
| 739 | 132 | 4935 | +4192 | 6.68 |
| 881 | 153 | 6581 | +5698 | 7.47 |
| **997** | **168** | **8016** | **+7025** | **8.09** |

### 6.3 Monotonicity

After permanent crossover, $\delta$ strictly increases at all but one step: $p=73$ where $\delta$ drops from 51 (at $p=71$) to 50. This minor dip of 1 unit stays well above extinction; thereafter $\delta$ resumes strict monotonic increase.

### 6.4 Verdict

All three empirical hypotheses are confirmed across the full range $3 \le p \le 997$:

| Hypothesis | Status |
|------------|--------|
| **Crossing**: $\exists p_c$ s.t. $\forall p \ge p_c$, $G_{\text{local}} > p$ | [Confirmed] $p_c = 37$ |
| **Monotonicity**: $\delta$ never permanently dips back | [Confirmed] One minor fluctuation ($p=73$: 51→50) |
| **Domination**: $\delta$ grows faster-than-linear | [Confirmed] $\delta/p$ grows from 0.14 → 7.09 |

## 7. The Layer 4 Crossover (Window vs Period)

For the first three layers, the danger zone $[p, p^2]$ is larger than the entire previous primorial period $M_{k-1}$, so 100% of 2-gaps are forced into the window:

| Layer | $p$ | $p^2$ | $M_{k-1}$ | Window vs Period |
|---|---|---|---|---|
| 1 (p=3) | 3 | 9 | 2 | Entire period fits in window |
| 2 (p=5) | 5 | 25 | 6 | Entire period fits in window |
| 3 (p=7) | 7 | 49 | 30 | Entire period fits in window |
| **4 (p=11)** | **11** | **121** | **210** | **Window < Period** |

For $p \le 7$, $G_{\text{local}} = T_{k-1}$ trivially — every 2-gap in the cycle falls inside the window.
For $p \ge 11$, the primorial $M_k$ permanently outgrows $p^2$, and the window only sees a fraction of the cycle. This is when the distribution question becomes relevant.

## 8. Remaining Gaps (Not Yet Closed)

| Gap | Severity | Description |
|---|---|---|
| **Local density** | Fatal (unproven) | No proof that $G_{\text{local}}$ grows above $p$. $T_k \to \infty$ is global; $G_{\text{local}}$ depends on intra-copy distribution of 2-gap positions. Empirically holds up to $p=97$ (see Section 6). |
| **Across-copy vs. intra-copy** | Fatal (unproven) | The 1-value rotation proves deletions are uniform across copies at fixed index $i$. It does not prove 2-gap positions are uniformly distributed within a single copy. |
| **1-value rotation scope** | Clarified | Rotates the gap sequence so smallest survivor is at position 0. Offset is arithmetic (first survivor after filtration). Does NOT rotate the underlying positions of 2-gaps in any controlled way. |
| **Individual persistence** | Fatal (unproven) | $T_k$ grows, but individual 2-gaps are destroyed and replaced each layer. No invariant tracks a specific 2-gap across layers. The growth inequality is about count, not individual survival. |
| **Global density $\to$ local guarantee** | Fatal (unproven) | Mertens gives $\frac{T_k}{\|R_k\|} \sim \frac{C}{(\ln p)^2}$. Even if this holds, it's an average over $M_k$, not a guarantee for short interval $[p, p^2]$. Known hard problem (Jacobsthal's function). |
| **Empirical scan to $p=1000$** | Complete | Full scan completed (676s, 166 primes). Permanent crossover at $p=37$; $G/p$ reaches 8.09 at $p=997$. All three hypotheses confirmed. See article `draft-empirical-g-local-analysis.md`. |

## 9. Failed Approaches (Discarded)

These versions were evaluated and found insufficient:

1. **Static head box [1, 210]**: Finite box, impossible to have infinite 2-gaps in it. Fatal contradiction.

2. **Proportional density $p^2 / M_k$**: Assumes uniform distribution of 2-gap positions within a copy. Unproven and equivalent to the conjecture.

3. **"Gear scanning" across layers**: Claims safe zone scans across a fixed tape as $k$ increases. Fails because the tape (gap array) is deterministically transformed each layer — not a fixed background.

4. **Global surplus $\to$ local overflow**: $p \cdot T_k - |R_k| \to \infty$ does not force any 2-gap into $[p, p^2]$ without a positional guarantee.

## 10. The Fundamental Obstacle

The invariants provable about the MemCycle are **global** (total counts, per-copy deletion patterns, growth rates). The Twin Prime Conjecture requires a **positional** guarantee about a specific short interval $[p, p^2]$. Bridging this gap without assuming distributional uniformity is the core unsolved problem.

All current approaches either:
- Assume what needs to be proved (uniform distribution of 2-gaps), or
- Only prove global properties that don't constrain the safe zone

A genuinely new invariant is needed — one that tracks the **position** of 2-gaps relative to the cycle's head across layers, not just their count.

## 11. The Cluster Approach (Conditionally Valid)

A refined framing proposes isolating the problem to a single local cluster:

**Filter core constraint:** Stride = p ⇒ at most 1 strike in any window of width < p.

**Cluster blueprint for survival** (for any p > 8):
- Minimum 2-gaps: C ≥ 2
- Tightest spacing: 6 (due to 2-gap isolation, proven for k ≥ 2)
- Total cluster width: 8 units (e.g., {x, x+2} and {x+6, x+8})
- Filter p > 8 can strike at most 1 coordinate in this width-8 window
- Therefore at least 1 of the 2 2-gaps survives

**What makes this valid:** The arithmetic is correct. If such a cluster exists in the safe zone [p, p²], survival is guaranteed.

**What remains unproven:**

| Gap | Description |
|-----|-------------|
| **Cluster existence in window** | Even if the full cycle contains a width-8 2-gap pair, it could fall outside the first p² positions. With M_n ≫ p² for n ≥ 4 (M₄=210 > 121=p²), most of the cycle is outside the window. |
| **Cross-layer persistence** | If filter p kills one member, only {x+6, x+8} survives as a singleton. At the next layer, C=1 — the guarantee fails. The cluster must be *reconstructed* each layer, but the argument doesn't show how. |
| **Spacing is an upper bound, not a lower bound** | Isolation gives minimum spacing 6, but doesn't force 2-gaps to be close. A cycle could have 2-gaps every 1000 units (satisfying isolation), yet contain no width-8 cluster. For G_local ≤ p-1 (extinction), we only need <p distinct 2-gap starts in [p, p²], which requires at most ceil(p²/6) spacing — a trivially satisfied condition. |

**Bottom line:** The cluster approach is a structurally valid conditional, but proving the antecedent (a width-8 2-gap pair always exists in [p, p²]) is equivalent to proving G_local > p directly. It rephrases the problem as a spacing conjecture rather than solving it.

## 12. The Across-Copy Argument (Redundant)

A refinement of the cluster approach uses modular arithmetic across the p copies:

**Setup:** Cluster {r₁, r₁+6} in parent cycle. After p-fold expansion with 1-value rotation, positions in copy k are r₁ + k·Mₙ + k and r₁ + 6 + k·Mₙ + k.

**Filter condition:** T₁ dies in copy k when r₁ + k(Mₙ+1) ≡ 0 (mod p). T₂ dies when r₁ + 6 + k(Mₙ+1) ≡ 0 (mod p).

**Each has exactly one solution for k in [0, p-1]** (because Mₙ+1 is coprime to p). So:
- T₁ dies in exactly 1 copy
- T₂ dies in exactly 1 copy
- At most 2 copies are damaged
- **p-2 copies preserve the intact cluster** [Proven]

**The flaw: copies 1 through p-1 are outside the safe zone.**

| Layer | p | Mₙ₋₁ | Copy 1 starts at | Safe zone |
|------|---|------|-----------------|-----------|
| 4 | 11 | 210 | 211 | [11, 121] |
| 5 | 13 | 2310 | 2311 | [13, 169] |
| 6 | 17 | 30030 | 30031 | [17, 289] |

For all n ≥ 4, Mₙ₋₁ > p², so copies k ≥ 1 are entirely outside [p, p²]. The p-2 intact copies don't matter — only copy 0 does.

For copy 0 (k=0):
- T₁ dies if r₁ ≡ 0 (mod p)
- T₂ dies if r₁ ≡ -6 (mod p)
- These are distinct for p > 3, so at most 1 dies
- **At least 1 survives in copy 0** — if r₁ < p²

The across-copy machinery proves survival across all copies, but the safe zone only interrogates copy 0. The argument collapses to the same conditional: *if* the cluster exists at r₁ < p² in the parent cycle, then at least one 2-gap survives filtration. The modular arithmetic adds confidence but no new constraining power — it is a redundant proof of the same conditional.

**Lesson:** The error is tempting because "p-2 copies survive" sounds like overwhelming force, but it's directed at the wrong target. This pattern (proving a global property and assuming it constrains a local window) is the recurring obstacle across all approaches.

## 13. The Jacobsthal Function Approach (Promising Reframing)

**Core idea:** Instead of proving 2-gaps exist in [p, p²], bound the **maximum possible void** between survivors using Jacobsthal's function $h(M_n)$, and show the safe zone is too large to be consumed by such voids.

**Definition:** $h(M_n)$ = longest consecutive run of integers each divisible by some prime ≤ p_n (i.e., maximal gap between residues coprime to M_n).

**If $h(M_n) < p$**, then every interval of length p contains at least one survivor. The safe zone [p, p²] contains (p²-p)/p = p-1 disjoint intervals of length p, guaranteeing ≥ p-1 survivors.

**Empirical support (up to p=787):**

| p | M_{n-1} | p² − p | h(M_{n-1}) | h ≪ p²? |
|---|---------|--------|-------------|---------|
| 11 | 210 | 110 | 14 | [Holds] |
| 13 | 2310 | 156 | 22 | [Holds] |
| 17 | 30030 | 272 | 26 | [Holds] |
| 19 | 510510 | 342 | 34 | [Holds] |
| 97 | — | 9312 | ~86 | [Holds] |
| 787 | — | ~618k | ~382 (est.) | [Holds] |

**Remaining gaps:**

| Problem | Severity | Detail |
|---------|----------|--------|
| **From survivors to 2-gaps** | Bridgeable but unproven | ≥ p-1 survivors is enough raw count, but they could be spaced >2 apart. Need a second step: given many survivors, prove some form gap-2 pairs. |
| **Asymptotic Jacobsthal bound** | Open problem | Proven: $h(M_n) = O(n^2 \log^2 n)$. Conjectured: $O(n \log^2 n)$. Both could match $p_n^2 \sim n^2 \log^2 n$ asymptotically. No proven guarantee that $h(M_n) \ll p^2$ forever. |
| **From "not empty" to G_local > p** | Unproven | Even with many survivors, need >p 2-gaps specifically. Requires distributional argument on top of the void bound. |

**What this achieves:** Reframes the question from "does a cluster exist?" to "does the maximum void grow slower than the safe zone?" — a better-posed, researchable problem. The empirical data strongly supports the pattern up to p=787, but a proof requires either (a) a better bound on $h(M_n)$ than currently known, or (b) a different invariant that doesn't rely on Jacobsthal's open bounds.

## 14. Cluster Persistence Across Layers

**Question:** If a cluster C ≥ 2 within W ≤ 8 exists, can we prove it (1) survives the next filter, and (2) reaches and stays in the safe zone?

### Answer (1): Survival of a single filter

**Yes, provable.** For cluster {r, r+6} and filter p > 8:
- Stride p > cluster width W = 8 ⇒ at most 1 element hit
- Equations r ≡ 0 (mod p) and r ≡ -6 (mod p) are distinct for p > 3 ⇒ can't both hit
- At least 1 of 2 survives in copy 0 [Proven]

**But:** surviving cluster has C=1 after one layer. Next filter p' can kill a singleton (no protective redundancy). The cluster guarantee requires C ≥ 2 each layer — the cluster must be *reconstructed*, not just preserved.

### Answer (2): Reaching and staying in the safe zone

**Staying (once inside):** [Proven] If a 2-gap enters [p, p²], then after filtration:
- Minimum survivor H ≥ p (the filter head)
- 2-gap absolute coordinate R ≤ p²
- New position P' = R - H ≤ p² - p < p² < (p')² (since p' > p)
- **Once in safe zone, stays in safe zone forever** (unless destroyed)

**Reaching (getting inside initially):** [Open] Unprovable with current invariants.
- Copies k ≥ 1 are at positions ≥ M_n ≫ p² for n ≥ 4
- Only copy 0 (position r₁ < p²) can be in the safe zone
- No drift mechanism brings copies k ≥ 1 back toward position 0 in the gap sequence
- A 2-gap's index depends on how many preceding elements are filtered — the same hard distributional question

### Verdict

| Claim | Provable? | Reason |
|-------|-----------|--------|
| C ≥ 2 within W ≤ 8 ⇒ survive one filter | [Proven] | Filter stride > cluster width |
| Once in safe zone, stay there | [Proven] | Safe zone expands faster than backward drift |
| Surviving singleton C=1 persists indefinitely | [Open] | Next filter can kill singleton |
| Cluster at copies k ≥ 1 enters safe zone | [Open] | Copies k ≥ 1 are at positions ≫ p² with no drift mechanism |
| Cluster exists in copy 0 [0, p²) | [Open] | Equivalent to proving G_local > 0 — the original gap |

## 15. Architecture Verdict: Formal Boundary of the Engine

After exhaustive analysis of all approaches, the Parallax engine's formal boundary is precisely mapped:

### What is proven

| Property | Significance |
|----------|-------------|
| **Filter bound (p-1 strikes max)** | The giant is capacity-limited within the safe zone |
| **2-gap isolation** | No multi-kill per stride — at most one 2-gap destroyed per filter strike |
  | **Safe zone outruns backward drift** | Once a 2-gap enters [p, p²], it stays in all future safe zones (unless destroyed) |
| **Global growth T_{k+1} ≥ (p-2)·T_k** | Total 2-gap count in the full cycle explodes superlinearly |
| **1-value rotation cycles residues** | Uniform distribution of residues *across copies* at fixed index |

### What is not proven

| Claim | Why it fails |
|-------|-------------|
| **Local density (G_local > p)** | Requires a positional guarantee about 2-gaps in [0, p²) — a local property |
| **Jacobsthal void bound (h(M_n) ≪ p²)** | Renames the empirical gap; best proven bounds keep pace with p² asymptotically |
| **Across-copy uniformity ⇒ local density** | Proves global survival (p-2 copies), but copies 1..p-1 are at positions ≫ p² |
| **Cluster persistence across layers** | C=1 after one filter kills the guarantee; requires reconstruction each layer |

### Historical formulation of the single remaining question

The Twin Prime Conjecture for this sieve reduces to:

> **In A_k (the k-th gap cycle), some 2-gap exists at position < p_{k+1}².**

This is a claim about the *positional* distribution of 2-gaps within a single
copy of the cycle. At this stage of the investigation it was treated as the
remaining question. Sections 22--23 replace that compressed formulation with
the later signed quadratic boundary and the distinct almost-prime program.

### Two paths considered

| Path | Viability | Verdict |
|------|-----------|---------|
| **A: Jacobsthal Horizon** — bound h(M_n) via formal verification to force elements into [0, p²) | Not viable | Requires analytic number theory beyond Stainless's scope; best proven bounds don't guarantee the needed separation |
| **B: Accept the formal boundary** — document the engine's proven invariants and the remaining density claim as a known open problem | Clean | Honest, rigorous boundary. The engine doesn't *solve* the conjecture — it reduces it to a single well-posed distributional claim. |

### Recommendation

Do not continue optimizing the same unsigned capacity envelope. Later work
proved a sharp quadratic survival threshold and then showed that the separate
capacity/native-period relaxations cannot clear it on an unbounded family.
The productive continuation is signed: use actual interval order, residue
energy, and cross-layer composition. The exact current boundary is recorded in
Section 22. The earlier cluster condition remains a conditional sufficient
statement, not the final architecture verdict.

## 16. What the Previous Sequence Tells Us About the Safe Zone

The previous sequence L_k provides the **complete data** for determining which 2-gaps appear in the next layer's safe zone. The missing piece is a structural invariant linking these data across layers.

### Known quantities from L_k

| Quantity | Symbol | What it is |
|----------|--------|------------|
| **2-gap coordinates** | S_k = {r_1, ..., r_T_k} | Absolute coordinates where {r, r+2} are both coprime to M_k |
| **Rotation offset** | R_k | First gap value; smallest positive survivor coordinate |
| **Cycle length** | M_k | Length of one period of the gap cycle |
| **Total 2-gap count** | T_k = |S_k| | Number of 2-gaps in the full cycle |
| **Density** | d_k = T_k / M_k | Approx. frequency of 2-gaps in the cycle |

### Survival condition for next layer

A 2-gap at r ∈ S_k survives into L_{k+1} iff:

$$r \bmod p_{k+1} \notin \{0, p_{k+1} - 2\}$$

It falls in the safe zone [p_{k+1}, p_{k+1}²] iff:

$$r \in [p_{k+1}, p_{k+1}^2]$$

### The unproven invariant

$$\forall k: S_k \cap [p_{k+1}, p_{k+1}^2] \neq \emptyset$$

This is a claim about the **distribution** of the T_k elements of S_k. The elements themselves are known (computed from L_k), and their positions are invariant across layers (unless destroyed). No inductive invariant linking S_k to S_{k-1} has been found that forces some r to always land in the safe zone.

### Known global vs. unknown local

| What we know globally | What we can't prove locally |
|-----------------------|-----------------------------|
| T_k grows superlinearly (proven) | At least one r < p_{k+1}² |
| d_k shrinks slowly (proven) | r mod p_{k+1} ∉ {0, p-2} for some r < p² |
| |S_k ∩ [0, M_k)| = T_k (definition) | S_k ∩ [p, p²] ≠ ∅ |

The safe zone probes a tiny fraction of the cycle (≈ p²/M_k), and this fraction shrinks to 0 exponentially fast. The previous sequence reveals the exact data but offers no proven constraint on which positions are "lucky" enough to fall in the window. The gap is purely distributional, which is why it reduces to a known hard problem in analytic number theory.

### Proven properties of the engine (historical snapshot)

This table records the state when Section 16 was written. It is not the current
complete catalog; see Section 22 and the sieve-sequence property index for the
later quadratic, capacity-envelope, and signed-localization results.

| # | Property | Status |
|---|----------|--------|
| 1 | CycleIntegral equivalence (recursive ≡ modular) | [Verified] |
| 2 | Filter bound: max p−1 strikes in [p, p²] | [Proven] |
| 3 | 2-gap isolation: no adjacent 2-gaps (k ≥ 2) | [Proven] |
| 4 | Single-target deletion: at most 1 2-gap killed per strike | [Corollary of #3] |
| 5 | Global growth: T_{k+1} ≥ (p−2)·T_k | [Proven] |
| 6 | 1-value rotation cycles residues uniformly across copies | [Proven] |
| 7 | Once in safe zone, stays there forever (unless destroyed) | [Proven] |
| 8 | C ≥ 2 cluster within W ≤ 8 survives one filter (p > 8) | [Proven conditional] |
| 9 | Absolute coordinates are invariant under rotation | [Trivial — coordinates don't move] |
| 10 | S_k ∩ [p_{k+1}, p_{k+1}²] ≠ ∅ | [Open] — equivalent to TPC (empirically holds $p \le 997$: $G_{\text{local}} > p$ from $p=37$ onward) |

### Remaining open questions

| Question | Nature |
|----------|--------|
| Does a 2-gap always exist at gap-position < p²? | Density conjecture (≈ Jacobsthal) |
| Does S_k always intersect [p, p²]? | Same density conjecture, rephrased |
| Can an inductive invariant link S_k to S_{k-1}? | Unknown — no such invariant found |
| Can the safe zone guarantee be reduced to a weaker claim than TPC? | Partially decomposed — harmless-class energy `U_i` is a noncircular component and may vanish with the final population, but no independently proved weighted bound yet fits the complete survival budget |

## 17. Structural Impossibility: The Inter-Prime Window Cannot Host a Surviving 2-Gap

A recurring proposal (most recently framed as the "Black Hole" / "Front Zone" argument) attempts to bypass the local density problem by claiming: *if a 2-gap exists in the interval \([p_n, p_{n+1})\) before the filter's first strike point, it survives the filter and stays trapped in the safe zone forever.*

This is structurally impossible. We prove it formally.

### 17.1 Framework

At layer \(n\) with primorial \(M_n = \prod_{i=1}^n p_i\):
- **Head** = \(p_n\) (the \(n\)-th prime)
- **Survivors** = numbers \(r \ge 1\) such that \(\gcd(r, M_n) = 1\)
- **Next filter** = \(p_{n+1}\)
- **Safe zone for next filter** = \([p_{n+1}, p_{n+1}^2]\)

### 17.2 Lemma 1: No Survivors in \((p_n, p_{n+1})\)

**Claim:** There is no survivor \(r\) with \(p_n < r < p_{n+1}\).

**Proof:** Let \(r\) be an integer with \(p_n < r < p_{n+1}\). Consider two cases:

- **Case 1: \(r\) is prime.** Then \(r\) is a prime greater than \(p_n\) and less than \(p_{n+1}\). This contradicts the definition of \(p_{n+1}\) as the *smallest* prime greater than \(p_n\).

- **Case 2: \(r\) is composite.** For \(r\) to be a survivor, all its prime factors must be \(> p_n\). The smallest such prime is \(p_{n+1}\), so any prime factor of \(r\) is at least \(p_{n+1}\). Therefore \(r \ge p_{n+1}^2\) (at minimum, a product of two primes each \(\ge p_{n+1}\)). For \(n \ge 2\), \(p_{n+1} \ge 3\), so \(p_{n+1}^2 \ge 9\). But \(r < p_{n+1} \le p_{n+1}^2\) for all \(p_{n+1} \ge 2\), so \(r < p_{n+1}^2\). Contradiction. ∎

**Corollary:** The only survivor in \([p_n, p_{n+1})\) is \(p_n\) itself.

### 17.3 Lemma 2: No Surviving 2-Gap in \([p_n, p_{n+1})\)

**Claim:** No 2-gap with left coordinate \(r\) where \(p_n \le r < p_{n+1}\) can survive the filter \(p_{n+1}\).

**Proof:** Let \(r\) be the left coordinate of a 2-gap (the right coordinate is \(r+2\)). We exhaust all cases.

- **Case A: \(r = p_n\).** The 2-gap is at \((p_n, p_n+2)\). For this to be a 2-gap, \(p_n+2\) must be a survivor. By Lemma 1, the only survivor in \([p_n, p_{n+1})\) is \(p_n\), so \(p_n+2 \ge p_{n+1}\). If \(p_n+2 > p_{n+1}\), then \(p_n+2\) is outside the interval and might be a survivor — but then the gap from \(p_n\) to \(p_n+2\) is not a consecutive survivor gap (there's \(p_{n+1}\) in between). So for \((p_n, p_n+2)\) to be a *consecutive* 2-gap, we must have \(p_n+2 = p_{n+1}\).

  In this case, the right element of the 2-gap is at coordinate \(p_{n+1}\), which satisfies \(p_{n+1} \equiv 0 \pmod{p_{n+1}}\). The filter removes it. The 2-gap is destroyed. ∎

- **Case B: \(r > p_n\).** Both \(r\) and \(r+2\) must be survivors in \((p_n, p_{n+1})\). Lemma 1 states no survivor exists in this interval. Contradiction. ∎

All cases lead to contradiction or guaranteed destruction. ∎

### 17.4 Corollary: Filter Immunity Zone Is Empty

The "Front Zone" or "Black Hole" concept — attempting to find a 2-gap at coordinate \(r < p_{n+1}\) that the filter cannot reach — fails because:

1. The absolute coordinate of a 2-gap's left element satisfies \(r \ge p_n\).
2. If \(r < p_{n+1}\), Lemma 2 proves no surviving 2-gap exists.
3. If \(r \ge p_{n+1}\), the filter's first strike at \(p_{n+1}\) can reach it (specifically, if \(r \equiv 0\) or \(r \equiv -2 \pmod{p_{n+1}}\)).

### 17.5 Why This Differs from the Standard Safe Zone Argument

The standard safe zone \([p, p^2]\) works because it's a *large* interval: it contains \(p^2 - p \approx p^2\) coordinates, which can hold many survivors and 2-gaps. The inter-prime window \([p_n, p_{n+1})\) is *tiny* — average size \(\sim \log^2 p_n\), growing slowly. The quadratic expansion of the safe zone is the engine's key strength; the linear inter-prime gap is a structural constraint that no invariant can circumvent.

### 17.6 The Lesson for Future Proposals

Any argument that attempts to place a surviving 2-gap inside the interval \([p_n, p_{n+1})\) (or more generally, at a coordinate \(r < p_{n+1}\)) is provably futile. The inter-prime gap is not "real estate" available for occupancy — it is a topological void between consecutive primes that the sieve cannot populate.

Arguments of this form include:
- "Front Zone" immunity claims (cumulative distance from head < p)
- "Black hole" containment via the first filter stride
- Any approach requiring a survivor between \(p_n\) and \(p_{n+1}\)

These are not "hard to prove" — they are structurally impossible, and this proof closes that class of approaches definitively.

A valid approach must place the 2-gap at coordinate \(r \ge p_{n+1}\) and then prove it survives the filter conditions while staying within the safe zone \([p_{n+1}, p_{n+1}^2]\). This is precisely the original density problem (Property 10 in Section 16), which remains open.

## 18. Draft Gap-Dynamics Claims Removed from the Article

The `gap-dynamics.md` article now treats the local-density inequality as the main boundary and no longer publishes draft or failed gap claims as article properties. These claims are preserved here because they may still guide future work, but they are not article-grade under the three-representation rule until they have natural-language explanation, symbolic derivation, and source-linked Stainless verification code.

| Claim | Current status | Why it stays in learnings |
|-------|----------------|---------------------------|
| Worst-case 2-gap growth inequality | Draft mathematical argument | The text argument is plausible, but it still needs a symbolic derivation and a Stainless `.holds` proof before publication. |
| 2-gap isolation | Draft mathematical argument | The idea needs source-linked verification code and a complete symbolic proof before it can return to the article. |
| Structural dispersion invariant | Draft permutation idea | The permutation intuition is useful, but it is not yet formalized in mathematical and Scala verification form. |
| Safe-zone stability | Failed attempted proof | The lower-bound step from `r < p^2` to safe-zone persistence does not follow; this remains a failed approach, not a property. |

These claims can return to a publication article only after they satisfy the article standard directly, or after they are explicitly framed as draft work with a tracking ticket and all required caveats.

## 19. The Chain/Cascade Characterization (New, Partially Checked)

**Claim:** A merge cascades beyond a simple pairwise fusion (two old gaps combining into one) only when two *consecutive* old gaps are both divisible by the incoming filter $h$.

**Derivation:** installing filter $h$ assigns each base-cycle position $r$ (for $0 \le r < T$) to a unique copy index $i(r) \equiv -\ell_r \cdot M^{-1} \pmod h$ — the one copy where that residue's lift is a multiple of $h$ and gets removed. Two adjacent positions $r, r+1$ land in the *same* copy — and thus their removal fuses three old gaps into one instead of two separate pairwise merges — exactly when:

$$i(r+1) = i(r) \iff g_r \equiv 0 \pmod h$$

Since post-2-stage gaps are even and $h$ is an odd prime $\ge 5$, the smallest gap satisfying this is $2h$. So: **while every gap in the current cycle stays below $2h$, this layer's merges are all simple pairwise fusions**, giving a clean bound $\text{maxGap}_{\text{after}} \le 2 \cdot \text{maxGap}_{\text{before}}$.

**Empirical status: fails almost immediately.** Checked against the real Spark-generated cycles (`spark/data/sieve-df/`), the no-cascade precondition ($\text{maxGap} < 2h$) already breaks at $h=11$ (the 4th nontrivial stage): $\text{maxGap}=28 > 2h=22$. So while the derivation itself is correct, it does not extend into a usable bound past the first few stages — cascades of length $\ge 3$ become arithmetically possible almost immediately, and a general worst-case bound would need to handle arbitrarily long chains, reintroducing the same equidistribution difficulty (see Section 13, Jacobsthal Function Approach).

| $h$ | maxGap | $2h$ | no-cascade holds? |
|---|---|---|---|
| 3 | 2 | 6 | yes |
| 5 | 4 | 10 | yes |
| 7 | 10 | 14 | yes |
| 11 | 28 | 22 | **no** |
| 13 | 40 | 26 | no |
| 17 | 64 | 34 | no |
| 19 | 106 | 38 | no |
| 23 | 148 | 46 | no |
| 29 | 202 | 58 | no |
| 31 | 256 | 62 | no |

Data source: `spark/data/sieve-df/stage_000` through `stage_010`, computed via the project's own Spark pipeline (`SievePipelineDF.scala`).

## 20. Why Gentle Per-Step Density Loss Does Not Imply Stabilization

A recurring intuition: each new filter only removes a $1/p$ fraction of survivors, so gap statistics (average, max, spread) should "settle down" as $p$ grows, since each individual step's disruption becomes small.

**This is false for the average gap, provably.** The average gap is exactly $M_k/T_k$, and Mertens' Third Theorem gives:

$$T_k/M_k = \prod_{p<h}\left(1-\frac1p\right) \sim \frac{e^{-\gamma}}{\ln h}$$

so the average gap $M_k/T_k \sim e^{\gamma}\ln h \to \infty$ — it diverges, without bound, forever. This is a rigorously proven asymptotic (not a conjecture), and it is a clean counterexample to "small step ⇒ stable statistics": the disruption per step really is $O(1/p)$, and the cumulative product of many $(1-1/p)$ factors still drifts toward zero density (equivalently, an unboundedly growing average gap) rather than converging.

**Max gap does the same, empirically.** Checked against the real Spark cycles (same dataset as Section 19), $\text{maxGap}/h$ is *increasing* at every one of the ten stages checked ($h=3$ to $31$): $0.67, 0.8, 1.4, 2.5, 3.1, 3.8, 5.6, 6.4, 7.0, 8.3$. No sign of stabilization over this range.

**Lesson:** "each step is gentle" is true, and it is exactly why the *count*
of 2-gaps keeps growing rather than collapsing to zero (Section 6's exact CRT
product and `gap-dynamics-v2.md` §§3.1--3.3). It is not, by itself, evidence
that any statistic *stabilizes* — Mertens' theorem is the standing proof that
it does not, for the one statistic (average gap) where the asymptotic is fully
known.

## 21. Worst-Case Adversarial Merge Bounds Size, Not Position (Open — Needs Large-Scale Data)

A tempting proof strategy: construct a deliberately pessimistic ("fake") merge process — one that always fuses whichever gaps are biggest, rather than following the actual $h$-driven arithmetic — and show that even this adversarial worst case keeps gaps comfortably small. If the pessimistic model provably dominates the real process, and the pessimistic model still looks safe, the real process is safe too.

**Where this is valid:** as a bound on *magnitude* (how big can the single largest gap in the cycle get), a fully free adversarial choice of which points to remove (subject to the real constraint of exactly $T$ removals, one per residue class) is a legitimate upper bound, since the real process's actual choice is just one point in that same space of possibilities.

**Where this breaks:** as a bound on *position*. The danger window $[p, p^2)$ only overlaps one specific copy ("copy 0") of the $h$-fold expansion. A freely adversarial model — unconstrained by which copy each residue's removal actually lands in — could simply choose to dump all its damage into copy 0 specifically, since nothing stops it from doing so. That would make the pessimistic model "prove" local extinction is possible, which contradicts the empirical reality (survival is always observed) — meaning a fully free adversary is *too* pessimistic to say anything useful about *where* damage lands. The real process's rigidity (each residue's target copy is a fixed affine function of its value mod $h$, not a free choice) is exactly the structure a valid positional bound would need to exploit — the same equidistribution difficulty as everywhere else in this file.

**Status:** the *size*-bound direction (Section 19's chain characterization) is checked against real data and found to break down quickly. The *position* question here has not been checked at all beyond the existing $p \le 997$ / $h \le 31$ ranges. **Open item:** extend the Spark empirical run to much larger primes (the current dataset tops out at $h=31$, 429M gaps) and track max gap, average gap, and 2-gap count together, to see whether the "gentle per-step, but still growing" pattern in Sections 19-20 continues to hold, weakens, or reverses at scale far beyond what's been checked so far. Nothing here changes the open-problem status — it is a possible empirical extension, not a new argument.

## 22. Current Twin-Prime Boundary After The Quadratic Audit

The later algebra replaces the old single-capacity narrative with three
separate layers.

### 22.1 The terminal condition is quadratic and signed

Candidate #24 proves a sufficient survival threshold of the form

```math
E_b < \frac{T^2}{2W_-},
```

where $E_b$ is the weighted harmful-excess energy. This is strictly weaker
than controlling the full collision energy. It is already terminal: proving
the required aggregate bound forces survival rather than merely supplying a
soft intermediate estimate.

### 22.2 Separate capacity envelopes are exhausted

The properties from Terminal Harmful-Excess Energy through Capacity Stability Gap classify the conservation, capacity, native-period
Bessel, fixed-cut, moving-cut, and stability-gap variants. The important
lesson is not that capacity bounds are false. They are sharp for the limited
information they retain. The problem is that maximizing each layer
independently discards actual signs and residue order, producing an envelope
too large to certify the quadratic threshold on an unbounded family.

This closes further optimization of the same separate envelope unless a new
ingredient prevents the abstract maximizing profiles from occurring.

### 22.3 Exact interval order gives a real saving

The Filter-Seven Excess Bound property computes the filter-$7$ centered residue word modulo $210$. Its
cumulative sums range from $-8$ to $10$, proving

```math
|b_7(I)|\le\frac{18}{7}
```

for every interval. The corresponding energy is at most $54P_m/5$, replacing
the false impression of a charge proportional to $P_mD^2$. This proves that
the capacity obstruction at the first nontrivial layer is an artifact of
discarding interval order.

### 22.4 Complete blocks reduce to residue energy

For an incoming prime $r$, let $c_t$ be the old-start histogram modulo $r$,
$d_t=c_t-N/r$, and $V_r=\sum_td_t^2$. The Copy-Block Excess Control property proves that copy-block
harmful excess has the exact form

```math
B_j=d_{t_j}+d_{t_j-2}
```

and therefore

```math
\sum_{j=0}^{r-1}B_j^2
=2V_r+2\sum_td_td_{t-2}
\le4V_r.
```

This is the durable bridge from conditioned residue-collision energy to the
quadratic survival criterion. It controls runs of complete old-period blocks.

### 22.5 The remaining obstruction is now precise

An arbitrary square window contains a complete-block run plus at most two
partial old-period fragments. Late in the chain, the old period can exceed the
whole window, so the partial fragments dominate. The remaining twin-prime
program therefore needs all three of:

1. a relative bound for the actual residue energy $V_r$;
2. signed control of the partial old-period boundaries; and
3. composition of those estimates across the weighted filter chain.

Accepted-anchor recursion, generic Gram/Bessel algebra, and additional
capacity-only optimization do not add those ingredients. This is a sharper
boundary than the historical statement “prove local density.” The full
mathematical synthesis is in
[Structural Properties and Signed Boundaries of 2-Gaps in Sieve Sequences](
../chapter6/gap-dynamics-v2.md).

## 23. Distinct Relaxed Almost-Prime Program

Candidate #25 weakens the second endpoint: the square-safe survivor $p$ is
prime, while $p+2$ is required to have at most two prime factors. This does not
prove a 2-gap and should not be counted as another capacity route.

The properties from Divisor Local Factor through Cofactor Progression Discrepancy establish its current algebraic boundary:

- the final relaxed weight has an exact divisor-dependent local factor;
- the natural shifted divisor remainder is exactly
  $\pi(I;d,-2)-\pi(I)/\varphi(d)$;
- the scalar-centered bilinear remainder decomposes into nonprincipal
  character modes; and
- modulo-$3$ character coefficients refute complete-wheel scalar-density
  Type-II orthogonality at full survivor scale.

The next input is an averaged prime-progression theorem matched to the exact
divisor and interval range, followed by a pre-sieved or locally adapted
bilinear estimate. The complete analysis is in
[Relaxed Almost-Prime Production in Sieve Sequences](
../draft/draft-relaxed-almost-prime-sieve-sequence.md).
