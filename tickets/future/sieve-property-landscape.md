# Sieve Sequence Property Landscape

**Status:** Plan phase — property analysis, no code yet  
**Created:** 2026-06-27  
**Updated:** 2026-06-29 (merged extended property list)  
**Depends on:** `filter-merge-foundation-gaps.md` (complete, 10572 valid)  
**Goal:** Catalogue and prioritize provable properties around sieve sequence gap dynamics, twin-gap survival, and safe-zone behavior.

---

## Notation

Let $P_k = \prod_{i=1}^{k} p_i$ be the primorial after the first $k$ primes.

Let $S_k$ be the set of surviving residues modulo $P_k$ (the values that pass $k$ filters).

A **d-gap** is a pair $(r, r+d)$ where both residues survive in $S_k$.

$T_k$ = number of surviving 2-gap residues in one full primorial period $[0, P_k)$.

---

## Legend

| Mark | Meaning |
|------|---------|
| ✅ **Proved** | Verified in Stainless, proof exists in codebase |
| 🟢 **Likely provable** | Straightforward target — simple arithmetic, no new invariants needed |
| 🟡 **Potential target** | Requires some new machinery but plausible |
| 🔴 **Open** | Requires genuinely new idea or non-trivial combinatorial insight |

---

## Core Structural Properties (Proved ✅)

| # | Property | Proof | Notes |
|---|----------|-------|-------|
| 1 | **Exact periodicity**: $S_k$ is periodic with period $P_k$. Divisibility by any $p_i \le p_k$ depends only on residue modulo $p_i$, hence survival depends only on residue modulo $P_k$. | ✅ `assertGapPeriodicMatchesSpec` | Immediate from modular arithmetic. |
| 2 | **Boundary-free expansion + CRT uniformity**: When adding $q = p_{k+1}$, the new period $P_{k+1} = P_k \cdot q$ is an exact $q$-fold copy of $[0, P_k)$. Since $\gcd(P_k, q)=1$, lifted residues $r + i P_k$ cover every residue class modulo $q$ exactly once. **Consequence**: earlier filters do not bias later primes — removing multiples of 2 does not distort distribution modulo 3 or 5 over a full period. | ✅ `assertModPeriodicWithMultipleSum` | $[0, P_k q) = [0, P_k) \cup [P_k, 2P_k) \cup \cdots \cup [(q-1)P_k, qP_k)$. The sieve is deterministic but modularly unbiased. |
| 3 | **Exact removal rule for gap $d$**: New prime $q$ kills $(n, n+d)$ iff $n \equiv 0 \pmod q$ or $n \equiv -d \pmod q$. For $q \nmid d$, these are two distinct classes → $2/q$ of lifted copies removed, $q-2$ descendants survive. For $q \mid d$, one class → $1/q$ removed, $q-1$ descendants survive. **Corollary (2-gap case)**: each 2-gap has $q-2$ children, so $T_{k+1} = T_k (q-2)$, and $T_k = \prod_{i=2}^{k} (p_i-2)$. Since $q\ge5$ gives $q-2\ge3$, non-extinction in residue space follows. **Lemma**: odd $q$ cannot kill both $n$ and $n+2$ because $q \mid 2$ impossible for $q>2$. | ✅ `assertSurvivorGapEqualsSpecNextGap` | Core dynamics: $C_{k+1}^{(d)} = C_k^{(d)} \cdot (q - 1)$ if $q \mid d$, else $C_k^{(d)} \cdot (q - 2)$. The recurrence proves non-extinction and is exact over full periods. |
| 4 | **Composite filters are redundant**: Filtering by composite numbers is equivalent to filtering by primes. Every composite's filter is contained inside the filters of its prime divisors. | ✅ | Elementary divisibility. |
| 5 | **No new 2-gaps from merging**: In the twin-focused quotient, merging non-2 gaps cannot create a 2-gap because $a + b = 2$ is impossible when $a, b \ge 2$ and neither is 2. Filtering destroys 2-gaps but does not create new ones by merging dead regions. Growth comes from period expansion, not from merging. | ✅ | Quotient sequence structure. |

---

## Forbidden States / Dead Configurations 🟢

A structural insight: the sieve transition is not arbitrary — it only copies the period $q$ times and deletes divisible elements, which merges neighbouring gaps. Therefore some gap patterns can be classified as **impossible forever** once they disappear.

### Monotonic exclusion theorem

Define $\operatorname{Possible}_k(X)$ = "gap pattern $X$ occurs somewhere in $S_k$". The transition rule has the property that it **cannot create certain patterns** — only expand existing ones and delete elements. This gives:

> If $\neg \operatorname{Possible}_k(X)$ and the transition $S_k \to S_{k+1}$ cannot create $X$, then $\neg \operatorname{Possible}_{k+1}(X)$.

By induction: if $X$ is absent at stage $k$, it is absent in all $S_j$ for $j > k$.

### Already proved instance

| Property | Status |
|----------|--------|
| **New 2-gaps cannot be created by merging non-2 gaps** (#5) | ✅ Proved. Merging dead regions cannot produce a 2-gap because $a+b=2$ is impossible when $a,b\ge 2$ and neither is 2. |

### Further candidates

| # | Candidate | Notes |
|---|-----------|-------|
| A | **Maximal gap value** $E_k$: If a gap larger than $q$ is absent at stage $k$, can it reappear later? | Merging smaller gaps can produce larger gaps (e.g. $2+4=6$), so this is NOT a forbidden state — large gaps CAN be created. But the growth may have bounds. |
| B | **Small gap values 2,4,6,8,10**: Once a specific small gap value is absent, can it reappear? | If no two gaps in $S_k$ sum to $d$, then $d$ cannot appear in $S_{k+1}$ because new gaps are sums of consecutive old gaps. A useful predicate: $\operatorname{NoPairSummingTo}_k(d)$. |
| C | **Leftmost survivor position**: If no survivor exists in $[0, L)$ at stage $k$, can a survivor appear there later? | Period expansion moves everything right, so the leftmost survivor can only increase. This is already the $m_k$ invariant (#10). |
| D | **Gap parity**: If no odd gap exists at stage $k$, can an odd gap appear later? | Since gaps are sums of consecutive existing gaps, if all gaps are even, sums are even. Odd gaps would require an odd ancestor — so parity absence is likely preserved. |
| E | **Gap pattern "2, X, 2"**: If a specific 2-gap boundary pattern is absent, can it reappear? | Requires tracking specific gap neighborhoods. More complex but follows the same monotonic exclusion principle. |

### Proof structure (formalizable in Stainless)

1. Define the transition function $T : \text{GapList}_k \to \text{GapList}_{k+1}$ (already exists via `survivorValues` + `gapsFromValues`).
2. Define predicate $\operatorname{Possible}_k(X)$ for a pattern $X$.
3. Prove a **non-generation lemma**: for each candidate pattern $X$, prove:
   ```
   ∀ L. ¬Possible_k(X) ∧ T(L) = L' ⇒ ¬∃ position p. pattern X occurs in L' at p
   ```
4. Conclude by induction: once absent, never returns.

This framework reduces the search space: instead of tracking all theoretical gap configurations, we track only configurations reachable from the sieve transition. Several candidates (B, C, D) are likely provable with the existing lemmas.

---

## Clarifying Concepts (Proved or Obvious)

| # | Concept | Status | Notes |
|---|---------|--------|-------|
| 6 | **Twin candidate as a 2-gap**: A surviving $(n, n+2)$ is a twin prime candidate. If $n + 2 \le p_k^2$, then every possible prime divisor has been tested — $(n, n+2)$ are certified prime. | ✅ Definition | Not a property, a definition of the safe zone. |
| 7 | **Geometry model**: Residues modulo $P_k$ are points on a circle of circumference $P_k$. A 2-gap is a small marked arc $r \to r+2$. Adding $q$ creates a $q$-fold cover; each arc lifts to $q$ arcs, exactly 2 are removed. | ✅ | Visualization only. No new proof content. |
| 8 | **Survival tree**: 2-gaps form a deterministic branching tree. Each parent has $q-2$ children. $T_k$ grows exactly as $\prod (p_i - 2)$. | ✅ | Covered by #3 (recurrence corollary). |

---

## Likely Provable 🟢

| # | Property | Notes |
|---|----------|-------|
| 9 | **Quotient sequence**: Collapse maximal runs of non-2 gaps into `2 D 2 D 2 ...`. Dynamics become expand → delete → merge. | Modeling simplification. |
| 10 | **Projection maps $S_k \rightarrow S_j$**: For $j < k$, define natural projection from stage $k$ back to stage $j$. Surjective with known preimage size. | Direct from CRT lifting (#2). |
| 11 | **Pull-back window definition**: Fix final stage $N$. Define $D_{k,j}(a) =$ safe descendants of ancestor gap $a$ at stage $k$ that land in $[0, p_N^2]$. | Definition only. |
| 12 | **Leftmost surviving 2-gap**: Define $m_k = \min\{ n : (n, n+2) \text{ survives filters up to } p_k\}$. Prove $m_k$ has known bounds. | $m_k$ controls safe-zone crossing ($m_k + 2 \le p_k^2$). Might be easier than tracking all gaps. |
| 13 | **Maximum dead block $E_k$**: In the twin-focused quotient, define $E_k = \max_i D_i$. If $E_k < p_k^2$ infinitely often, every interval of length $p_k^2$ contains a 2-gap. | Stronger than needed but geometrically clean. |
| 14 | **Local filter bound**: Inside any interval of size $N$, prime $q$ removes at most $2 \lceil N / q \rceil$ candidate positions. | Easy bound, too weak alone. |

---

## Potential Proof Targets 🟡

| # | Property | Notes |
|---|----------|-------|
| 15 | **Full-block decomposition**: The final safe window $[0, p_N^2]$ can be decomposed into complete lifted blocks (from earlier stages) plus one boundary block. Complete blocks obey exact recurrence. | Boundary contains all difficulty. |
| 16 | **Boundary is the only source of uncertainty**: Inside complete lifted blocks everything is exact. All approximation comes from the boundary block. | Reduces to tracking one partial block. |
| 17 | **Windowed recurrence**: Prove $T^{(N)}_{k+1} = T^{(N)}_k + A_k - R_k$ where $A_k > R_k$ (counting descendants that land in $[0, p_N^2]$). | The windowed monotonicity theorem. Key unresolved sub-property. |
| 18 | **Lineage counting in windows**: Count descendants of an ancestor gap at stage $k$ that land in $[0, p_N^2]$, for each $k < N$. | Requires period alignment. Pull-back approach. |
| 19 | **Merge graph**: Track deletions, merges, and ancestry of each gap. Every gap has a creation history. Bound total merge complexity. | New data structure idea. Unknown whether bounded. |

---

## Open Problems 🔴

| # | Property | Notes |
|---|----------|-------|
| 20 | **Maximum dead interval $E_k < p_k^2$**: If true for all large $k$, every safe zone contains a 2-gap — proving twin primes. | This IS the twin prime conjecture. Equivalent to solving it. |
| 21 | **Safe-zone crossing**: Prove $\exists^\infty k$ such that $A_k(p_k^2) > 0$, where $A_k(x) = \#\{ n \le x : (n, n+2) \text{ survives filters up to } p_k\}$. | We don't need "always present" — just "infinitely often crossing." All current open problems reduce to this. |
| 22 | **Proof by contradiction**: Assume $A_k(p_k^2) = 0$ for all large $k$. Then every 2-gap approaching the safe zone must be killed before certification. Show this is impossible because growth exceeds removals in the window. | The structure of the contradiction — #17 (windowed recurrence) is the most concrete form. |
| 23 | **Location, not count**: Over a full primorial period $[0, P_k)$, the distribution is exact — CRT guarantees no bias, and $T_k$ grows as $\prod(p_i-2)$. But the safe zone $[0, p_k^2]$ is tiny ($p_k^2 \ll P_k$). The uniformity claim does not fail; it simply does not apply to subintervals. Counting over the full period does not guarantee safe-zone presence. | This is the real obstruction. $\|S_k\| \gg p_k^2$ does not imply $S_k \cap [0, p_k^2] \ne \emptyset$. The distribution over a full period is exact; the difficulty is entirely about partial-period behavior. |
| 24 | **CRT covers full periods only**: For any current primorial $P_k$ and unused prime $q \nmid P_k$, lifted residues $r + iP_k$ cover all classes modulo $q$ exactly once. There is **no counterexample** in the full period model — the distribution property is exact. The only way it "fails" is if we leave complete periods and look at arbitrary subintervals like $[0, p_k^2]$. The problem is not unbiased filters combining into bias; it is that modular uniformity does not control the absolute position of the smallest survivor. | Key insight: the obstacle is about the position of the leftmost survivor crossing into $[0, p_k^2]$, not about any modular bias. The safe zone is a partial-period window, so CRT guarantees alone are insufficient. |

---

## Strongest Current Research Direction

The current primary direction is the weighted harmless-class energy isolated
by candidates #21 and #22. At incoming prime `r_i`, the full residue energy
has the exact orthogonal decomposition

```math
V_i
=
U_i
+
\frac{r_i}{2(r_i-2)}b_i^2
+
\frac12\Delta_i^2.
```

Here `U_i` is dispersion among the `r_i-2` harmless survivor classes, `b_i`
is total harmful excess, and `Delta_i` is left/right harmful-class imbalance.
The immediate target is the weakest aggregate bound on

```math
\sum_iw_iU_i
```

that fits candidate #21 after endpoint-sampling and accepted-strike density
errors are subtracted. Candidate #22's pointwise benchmark `U_i<=N_{i+1}` is
a convenient stronger statement, not a mandatory premise. It is noncircular
in isolation because it remains true when `N_{i+1}=0`.

The earlier final-stage pullback remains an alternative geometric direction:
fix `N`, pull `[0,p_N^2]` back through `S_N,...,S_1`, and seek the windowed
monotonicity theorem (#17). The leftmost-gap, maximum-dead-block, and
anti-concentration invariants remain possible inputs to that alternative, but
none currently controls the three orthogonal energy components at the
required weighted scale.

---

## What Can Be Verified in Stainless Today

| # | Property | Difficulty | Dependencies |
|---|----------|------------|--------------|
| 1-8 | Already proved or clarifying | — | — |
| 9 | Quotient sequence model | Easy | Gap cycle definitions |
| 10 | Projection maps $S_k \rightarrow S_j$ | Easy | `indexOfAccepted`, `assertApplyMatches` |
| 11 | Pull-back window definitions | Easy | Definitional only |
| 12 | Leftmost 2-gap $m_k$ bounds | Medium | Requires period alignment + CRT |
| 13 | Maximum dead block $E_k$ | Medium | Requires quotient sequence + period alignment |
| 14 | Local filter bound | Easy | Arithmetic bound |
| 15 | Full-block decomposition | Medium | Requires period alignment lemmas |
| 16 | Boundary uncertainty | Medium | Follows from 15 |
| 17 | Windowed recurrence | Hard | Requires new counting invariant |
| 18 | Lineage counting in windows | Medium | Pull-back + period alignment |
| 19 | Merge graph | Unknown | New concept |

---

## Related Files

- `src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala` — canonical bridge, home of `assertSurvivorGapEqualsSpecNextGap`
- `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala` — survivor filter, gap derivation, composition theorem
- `src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala` — the mathematical spec, gap periodicity, modular arithmetic
- `tickets/active/filter-merge-foundation-gaps.md` — completed ticket, foundation for all gap reasoning
