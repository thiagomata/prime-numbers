# Gap Dynamics and Twin Prime Candidates in Sieve Sequences

**Author:** Mata, T. H.  
Independent Researcher  
**Email:** [thiago.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

This article studies gap dynamics as the behavior induced by the Sieve Sequence transition. Each sequence state is a finite list of survivors that can generate the next state; across all states, this construction generates the prime sequence. The gap cycle is the compressed form of that finite transition, so conclusions about 2-gaps come from how `nextFiltered` determines `nextGaps`. After the verified sieve foundations are in place, the remaining question is whether the local safe zone $[p, p^2]$ always contains enough 2-gaps to survive the next filter. Empirical data supports this local-density inequality up to $p=997$, but no formal proof is claimed here.

---

## Boundary Index

| # | Claim | Statement | Status |
|---|-------|-----------|--------|
| 1 | Neighbor-merge evolution | Filtering changes gaps only by preserving them or merging adjacent gaps | [Draft — verification pending] |
| 2 | Local density question | $G_{\text{local}}(p) > p$ for all sufficiently large $p$ | [Open] |
| 3 | Empirical support | $G_{\text{local}}(p) > p$ for tested $37 \le p \le 997$ | [Empirical] |

Status key: `[Draft — verification pending]` = mathematically stated here, but not yet backed by a dedicated Stainless `.holds` proof. `[Open]` = not proven. `[Empirical]` = supported by computation, not a proof.

---

## 1. Introduction

The Sieve of Eratosthenes filters composite numbers by iteratively removing multiples of each prime. In this project, the Sieve Sequence makes that process finite and constructive: one finite survivor list generates the next finite survivor list, and the chain of such lists generates the primes. The gaps between consecutive survivors encode the structure of each finite state. A gap of size 2 (a "2-gap") corresponds to a pair of consecutive survivors $(r, r+2)$, which is exactly the form of twin prime candidates.

This article analyzes the local boundary that remains after the verified sieve foundations are established. It does not claim a proof of the Twin Prime Conjecture.

The `SieveSequence.next` pipeline first expands the current residues, then filters the expanded survivors, sorts the survivors, computes the next gaps, and rotates the gap cycle around the next head. Gap dynamics is therefore not separate from the Sieve Sequence: it is the induced effect of `nextFiltered` on `nextGaps`. The core unresolved question is not whether a global periodic cycle contains many 2-gaps, but whether enough of them occur in the small front interval where the next finite computation matters.

### Cross-Reference

This article builds on the [Learnings: Capacity Argument](../articles/learnings/learnings-capacity-argument.md), which records failed approaches and the current boundary map.

---

## 2. Gap Evolution by Neighbor Merges

When a Sieve Sequence step filters the expanded survivor list, it does not create a new gap by an arbitrary operation. It removes survivor points from a finite ordered list, and `nextGaps` is then computed from the remaining consecutive survivors. Removing an endpoint between two neighboring gaps replaces the two gaps on either side by their sum. Gaps not touching the deleted survivor remain unchanged. If several consecutive survivors are deleted, the resulting gap is the sum of the whole contiguous block of old gaps between the surviving endpoints.

This matters because it turns future gap creation into a reachability question. A future gap value can only come from an existing gap or from the sum of a contiguous block of existing neighboring gaps. Therefore, if a value cannot be represented by any such block, it cannot appear at the next step. In the post-2 sieve layers used for twin-prime analysis, gaps are positive even values, so once all 2-gaps are absent, neighbor merges cannot recreate a 2-gap: preserving a gap keeps it non-2, and merging positive even gaps produces a value at least 4.

### Mathematical Form

Let the current survivors be ordered as

```math
\begin{aligned}
s_0 < s_1 < \cdots < s_n
\end{aligned}
```

and let the gaps between consecutive survivors be

```math
\begin{aligned}
g_i &= s_{i+1} - s_i. && [By Definition]
\end{aligned}
```

If the filter removes the middle survivor $s_{i+1}$ while preserving $s_i$ and $s_{i+2}$, the two adjacent gaps merge:

```math
\begin{aligned}
g'_i
  &= s_{i+2} - s_i && [By Definition] \\
  &= (s_{i+2} - s_{i+1}) + (s_{i+1} - s_i) && [Algebra] \\
  &= g_{i+1} + g_i && [Substitution] \\
  &= g_i + g_{i+1}. && [Simplification]
\end{aligned}
```

If the filter removes a consecutive block $s_{i+1}, \ldots, s_{j-1}$ while preserving $s_i$ and $s_j$, the same argument telescopes:

```math
\begin{aligned}
g'_{i,j}
  &= s_j - s_i && [By Definition] \\
  &= \sum_{k=i}^{j-1}(s_{k+1} - s_k) && [Telescoping] \\
  &= \sum_{k=i}^{j-1} g_k. && [Substitution]
\end{aligned}
```

Thus every new gap is either an old gap whose endpoints both survive, or the sum of a contiguous block of old neighboring gaps whose interior endpoints are removed.

For post-2 layers, suppose every existing gap is positive and even, and no existing gap equals 2. Then no future merge can create a 2-gap:

```math
\begin{aligned}
h &= g_i && [Preserved Gap] \\
g_i &\ne 2 && [Assumption]
\end{aligned}
```

or

```math
\begin{aligned}
h &= \sum_{k=i}^{j-1} g_k && [Neighbor Merge] \\
g_k &\ge 2 \text{ and even} && [Post\text{-}2 Gap Property] \\
g_k &\ne 2 && [Assumption] \\
g_k &\ge 4 && [Simplification] \\
h &\ge 4. && [Q.E.D.] \blacksquare
\end{aligned}
```

### Scala Verification Status

This property is not yet verified by a dedicated Stainless `.holds` lemma. The implementation computes new gaps from filtered survivors in [
  `SieveUtils::calculateGaps`
](../src/main/scala/v1/chapter6/seq/sieve/SieveUtils.scala) and [
  `SieveUtils::pairwiseGaps`
](../src/main/scala/v1/chapter6/seq/sieve/SieveUtils.scala). The walking construction in [
  `SieveSequenceNextLevel::collectGapsV2`
](../src/main/scala/v1/chapter6/seq/sieve/SieveSequenceNextLevel.scala) skips deleted values and records the distance to the next survivor.

Draft verification target:

```scala
// DRAFT — not yet verified through Stainless
def assertDeletedMiddleMergesNeighborGaps(
  left: BigInt,
  middle: BigInt,
  right: BigInt
): Boolean = {
  require(left < middle)
  require(middle < right)

  val leftGap = middle - left
  val rightGap = right - middle
  val mergedGap = right - left

  mergedGap == leftGap + rightGap
}.holds
```

The broader contiguous-block and post-2 no-recreation corollaries should be tracked as follow-up verification work before this section is promoted from draft to verified.

---

## 3. The Open Local Density Question

The neighbor-merge rule constrains how gaps can change, but it does not by itself prove that 2-gaps persist in the local safe zone. The Twin Prime Conjecture requires a local guarantee: that a 2-gap exists in the specific interval $[p, p^2]$.

### The Question

Let $G_{\text{local}}(p)$ be the number of 2-gaps in $[p, p^2]$ after sieving by all primes less than $p$. The filter at this layer has exactly $p-1$ bullets (strikes at $p, 2p, \dots, (p-1)p$).

**Open Question:** Does $G_{\text{local}}(p) > p$ hold for all sufficiently large $p$?

If yes, the sieve lacks the capacity to destroy all local 2-gaps, and twin primes persist indefinitely.

### Status

This question remains **open** in the formal verification sense. It is equivalent to the Twin Prime Conjecture in this framework. See [Learnings: Capacity Argument](../articles/learnings/learnings-capacity-argument.md) Sections 10, 16, and 18 for detailed analysis.

### Empirical Evidence

The inequality $G_{\text{local}} > p$ holds for all tested primes $p \ge 37$ up to $p = 997$. The ratio $G_{\text{local}}/p$ grows monotonically from 1.14 to 8.09, suggesting the inequality is structural, not coincidental.

| $p$ | $G_{\text{local}}$ | $\delta = G_{\text{local}} - p$ | $G/p$ |
|-----|-------------------|----------------------------------|-------|
| 37 | 42 | +5 | 1.14 |
| 71 | 122 | +51 | 1.72 |
| 173 | 456 | +283 | 2.64 |
| 353 | 1484 | +1125 | 4.20 |
| 607 | 3590 | +2977 | 5.91 |
| 997 | 8016 | +7025 | 8.09 |

However, empirical evidence is not a formal proof. The local density question remains open.

---

## 4. Conclusion

The article's result is a boundary statement, not a proof of persistence. The neighbor-merge rule explains the limited ways gaps can change under filtering, and the local-density inequality $G_{\text{local}}(p) > p$ is the central open question. Empirical data supports the local-density inequality for the tested range.

A publication-ready proof must either verify a local-density invariant directly or prove a weaker invariant that still forces 2-gap survival inside the safe zone.

---

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*. Proceedings of the ACM on Programming Languages, OOPSLA Issue.

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Learnings: Capacity Argument for Twin Prime Persistence*. Available at: [articles/learnings/learnings-capacity-argument.md](../articles/learnings/learnings-capacity-argument.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Empirical Analysis of $G_{\text{local}}$: The Local 2-Gap Density in Sieve Sequences*. Available at: [articles/draft/draft-empirical-g-local-analysis.md](../articles/draft/draft-empirical-g-local-analysis.md)

---

## Appendix A: Verification Status

This article does not introduce a new verified property. It relies on the verified foundations cited in the companion articles, includes the neighbor-merge rule as a draft verification target, and marks the local-density statement as open.
