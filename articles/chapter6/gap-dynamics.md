# Gap Dynamics and Twin Prime Candidates in Sieve Sequences

**Author:** Mata, T. H.  
Independent Researcher  
**Email:** [thiago.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

This article studies gap dynamics as the behavior induced by the Sieve Sequence transition. Each sequence state is a finite list of survivors that can generate the next state; across all states, this construction generates the prime sequence. The gap cycle is the compressed form of that finite transition, so conclusions about gaps come from how filtering determines the next gaps. We derive general structural properties — the copy-or-merge rule, the non-generation of absent gap values, full-period survival via CRT, and the boundary between global and local survival — then specialize to 2-gaps (twin prime candidates). After these structural foundations, the remaining open question is whether the local safe zone $[p, p^2]$ always contains enough 2-gaps to survive the next filter. Empirical data supports this local-density inequality up to $p=997$, but no formal proof is claimed here.

---

## 1. Introduction

The Sieve of Eratosthenes filters composite numbers by iteratively removing multiples of each prime. In this project, the Sieve Sequence makes that process finite and constructive: one finite survivor list generates the next finite survivor list, and the chain of such lists generates the primes. The gaps between consecutive survivors encode the structure of each finite state. A gap of size 2 (a "2-gap") corresponds to a pair of consecutive survivors $(r, r+2)$, which is exactly the form of twin prime candidates.

This article proves properties of gap evolution under sieve transitions, then analyzes the local boundary that remains after those foundations are established. It does not claim a proof of the Twin Prime Conjecture.

The `SieveSequence.next` pipeline first expands the current residues, then filters the expanded survivors, sorts the survivors, computes the next gaps, and rotates the gap cycle around the next head. Gap dynamics is therefore not separate from the Sieve Sequence: it is the induced effect of filtering on gaps. The core unresolved question is not whether a global periodic cycle contains many 2-gaps, but whether enough of them occur in the small front interval where the next finite computation matters.

This article covers:

- The copy-or-merge rule — §2
- Non-generation of absent gap values — §3
- Full-period gap survival — §4
- Global versus local survival — §5
- Local density question and empirical support — §6

---

## 2. The Copy-or-Merge Rule

When a Sieve Sequence step filters the expanded survivor list, it does not create new gaps by an arbitrary operation. It removes survivor points from a finite ordered list, and the next gaps are computed from the remaining consecutive survivors. There are only two ways the new gaps relate to the old.

Let the current expanded survivors be ordered as

```math
\begin{aligned}
e_0 < e_1 < \cdots < e_{n-1}
\end{aligned}
```

and let the gaps between consecutive expanded survivors be

```math
\begin{aligned}
g_i &= e_{i+1} - e_i. && [By Definition]
\end{aligned}
```

If the filter removes one or more consecutive survivors while preserving the surrounding endpoints, the new gap is the sum of the old gaps spanned by the removal.

### 2.1 Single Removal

If the filter removes $e_{i+1}$ while preserving $e_i$ and $e_{i+2}$, the two adjacent gaps merge:

```math
\begin{aligned}
g'_i
  &= e_{i+2} - e_i && [By Definition] \\
  &= (e_{i+2} - e_{i+1}) + (e_{i+1} - e_i) && [Algebra] \\
  &= g_{i+1} + g_i && [Substitution] \\
  &= g_i + g_{i+1}. && [Simplification]
\end{aligned}
```

### 2.2 Block Removal

If the filter removes a consecutive block $e_{i+1}, \ldots, e_{j-1}$ while preserving $e_i$ and $e_j$, the same argument telescopes:

```math
\begin{aligned}
g'_{i,j}
  &= e_j - e_i && [By Definition] \\
  &= \sum_{k=i}^{j-1}(e_{k+1} - e_k) && [Telescoping] \\
  &= \sum_{k=i}^{j-1} g_k. && [Substitution]
\end{aligned}
```

### 2.3 The Rule

Thus every next-stage gap is either:

- **Copy**: an old gap $g_i$ whose endpoints both survive, or
- **Merge**: the sum of a contiguous block of old gaps whose interior endpoints are removed.

No other operation produces a new gap. This is the only way filtering transforms the gap structure.

```math
\begin{aligned}
g' \in G_{k+1}
  \;\Longrightarrow\;
  \bigl( \exists i,\; g' = g_i \bigr)
  \;\lor\;
  \bigl( \exists i < j,\; g' = \sum_{r=i}^{j-1} g_r \bigr).
\end{aligned}
```

### Implementation Notes

The implementation computes new gaps from filtered survivors in [
  `SieveUtils::calculateGaps`
](
  ../../src/main/scala/v1/chapter6/seq/sieve/SieveUtils.scala
), [
  `SieveUtils::pairwiseGaps`
](
  ../../src/main/scala/v1/chapter6/seq/sieve/SieveUtils.scala
), and the walking construction in [
  `SieveUtils::collectGapsV2`
](
  ../../src/main/scala/v1/chapter6/seq/sieve/SieveUtils.scala
) which skips deleted survivors and records the distance to the next one.

---

## 3. Non-Generation of Absent Gap Values

The copy-or-merge rule gives a useful negative principle. Let $d$ be a positive gap value. If the current stage has no copied source gap equal to $d$, and no contiguous block of old gaps sums to $d$, then $d$ cannot appear in the next stage.

```math
\begin{aligned}
d \notin G_k
\quad\land\quad
\forall i < j,\; \sum_{r=i}^{j-1} g_{r} \ne d
\quad\Longrightarrow\quad
d \notin G_{k+1}.
\end{aligned}
```

### 3.1 Induction Forward

If the condition holds at stage $k$, then $d \notin G_{k+1}$. Now suppose the same condition also holds at stage $k+1$ — that is, $d$ is absent and no merge of $G_{k+1}$ gaps sums to $d$. Then $d$ is absent from $G_{k+2}$, and so on. By induction, once both conditions are satisfied at any stage, $d$ never appears in any later stage.

This is a powerful tool. It says certain gap values can become permanently absent.

### 3.2 Example: Gap Value 1

The simplest instance of permanent absence is gap value 1 at the first sieve stage. Stage 1 has head $h=2$, modulus $M=1$ (empty product), and gap list $G_1 = [1]$ because the only emitted values below $2^2$ are $2$ and $3$. After the filter for prime 2 is applied, every survivor is odd, so every gap between consecutive survivors is at least 2 and even. Gap 1 cannot return:

- **Copy**: no gap in the current list equals 1.
- **Merge**: every gap is even, so the sum of two or more even gaps is even, never 1.

Thus gap 1 is permanently absent after stage 1. This is the concrete starting case of the non-generation principle.

### 3.3 Specialization to 2-Gaps

After the sieve has applied the filter for prime 2, every survivor is odd. Therefore every gap between consecutive survivors is positive and even. The smallest possible gap is 2, but if 2 is absent at some post-2 stage, then no later stage can recreate it.

**Proof.** Let $G_k$ be a post-2 gap list with $2 \notin G_k$. For any $g' \in G_{k+1}$, there are two cases:

- **Copy**: $g' = g_i$ for some $g_i \in G_k$. Since $2 \notin G_k$, $g' \ne 2$.
- **Merge**: $g' = \sum_{r=i}^{j-1} g_r$ with $j > i+1$. Each $g_r$ is even and at least 2. The merge involves at least two summands, so $g' \ge 4$.

Thus $2 \notin G_{k+1}$. The same argument applies to every subsequent stage by induction. Hence, absence of 2 is a permanent configuration under post-2 filtering.

```math
\begin{aligned}
2 \notin G_k,\; k \ge k_2
\quad\Longrightarrow\quad
2 \notin G_{k+m} \;\; \forall m \ge 0.
\end{aligned}
```

This does not prove twin primes exist. It gives the opposite kind of tool: if a computation ever found a post-2 stage with no 2-gaps, that absence would persist forever. Consequently, any proof of twin-prime persistence must explain why the sieve never reaches that dead configuration.

### 3.4 Generalization to Arbitrary d

The same reasoning applies to any gap value $d$. Whether $d$ can become permanently absent depends on whether contiguous blocks of the current gaps can sum to $d$. For odd values, the parity constraint is even stronger: in a post-2 stage, every gap is even, so no odd gap can ever appear at any stage.

```math
\begin{aligned}
\forall d \text{ odd},\quad d \notin G_{k_2}
\quad\Longrightarrow\quad
d \notin G_{k} \;\; \forall k \ge k_2.
\end{aligned}
```

This follows directly from the parity of all post-2 gaps: odd values cannot result from sums of even numbers, nor from copying even numbers.

---

## 4. Full-Period Gap Survival

Over a complete expanded period, a single d-gap has a simple survival law. Let $(r, r+d)$ be a d-gap in the current stage. Its lifted copies under expansion are

```math
\begin{aligned}
(r + iM,\; r + d + iM), \qquad 0 \le i < h,
\end{aligned}
```

where $M$ is the current modulus (the product of all active primes) and $h$ is the current head prime.

A lifted copy is destroyed by the new filter $h$ exactly when one endpoint is divisible by $h$:

```math
\begin{aligned}
r + iM \equiv 0 \pmod h
\quad\text{or}\quad
r + d + iM \equiv 0 \pmod h.
\end{aligned}
```

### 4.1 CRT Argument

Since $M$ is coprime to $h$ (all primes are distinct), the mapping $i \mapsto r + iM$ is a bijection on residue classes modulo $h$. Therefore each of the two endpoint conditions has exactly one solution for $i$ in $\{0, \dots, h-1\}$.

For $h > d$, the two solutions are distinct. If they coincided, we would have

```math
\begin{aligned}
r + iM \equiv r + d + iM \pmod h
\quad\Longrightarrow\quad
d \equiv 0 \pmod h,
\end{aligned}
```

which is impossible because $d < h$ (the gap is smaller than the filter prime in a well-formed stage).

Thus each current d-gap has exactly

```math
\begin{aligned}
h - 2
\end{aligned}
```

surviving lifted d-gap descendants over the complete expanded period. For $h = 3$ (the first odd prime filter), this gives $3 - 2 = 1$ survivor. For $h = 997$, it gives $995$ survivors.

### 4.2 Specialization to 2-Gaps

The same formula applies directly to 2-gaps. Each 2-gap at a post-2 stage has exactly $h - 2$ surviving descendants over a full expanded period after filtering by $h$. This is a global, full-period statement: 2-gaps are not globally extinguished by any single transition once $h > 2$.

```math
\begin{aligned}
\text{Each 2-gap at stage } k
\;\longrightarrow\;
h-2 \text{ descendant 2-gaps at stage } k+1
\quad\text{(over the full period)}.
\end{aligned}
```

It does not say where those descendants land in the next stage. The distinction between global survival and local safe-window survival is the subject of the next section.

---

## 5. Global versus Local Survival

The CRT argument in Section 4 is exact but uniform only over a complete period. It says nothing about the distribution of gap positions inside a short initial fragment of the next stage's sequence.

### 5.1 The Safe Window

The safe window for a sieve stage with head $h$ is

```math
\begin{aligned}
W_h = [h, h^2).
\end{aligned}
```

A d-gap with both endpoints in $W_h$ is immediately certified as a d-twin prime pair: every emitted value below $h^2$ is prime, and consecutive emitted values below $h^2$ correspond to consecutive integers (no composites are skipped within this range).

### 5.2 The Square Boundary

The next stage's head $h'$ satisfies $h' > h$. If a d-gap $(x, x+d)$ survives the transition and had $x + d < h^2$, then it remains below the next square boundary:

```math
\begin{aligned}
x + d < h^2 < (h')^2.
\end{aligned}
```

The lower edge is automatic: the next stage begins at $h'$, and any emitted value at or above $h'$ is a viable candidate. Thus a surviving emitted gap whose endpoints were already below $h^2$ stays below the next square boundary. The safe-window obstruction is not that local candidates drift too far right; it is that they may be destroyed, or that no local candidate existed in the first place.

### 5.3 Global Does Not Imply Local

The full-period survival count (Section 4) is a global statement. It ensures that across the entire expanded period (length $hM$), there are many surviving d-gap descendants. But the safe window $W_h$ has length roughly $h^2$, while the period $M$ grows primorially — after the early stages, $M$ is vastly larger than $h^2$.

```math
\begin{aligned}
\text{global survival}
\quad\not\Longrightarrow\quad
\text{safe-window survival}.
\end{aligned}
```

The safe window sees only a small initial fragment of the full period. CRT uniformity guarantees that lifted copies of a d-gap are spread evenly across residue classes, but it does not control whether the first few copies fall inside $W_h$.

### 5.4 Summary

The structural facts established so far are:

| Property | Scope | Status |
|----------|-------|--------|
| Copy-or-merge rule | Any stage | Proved in §2 |
| Non-generation of absent gap values | Any stage | Proved in §3 |
| Full-period d-gap survival (h-2 copies) | Global, over full period | Proved in §4 |
| Global does not imply local | Boundary statement | Proved in §5.3 |
| Local candidates stay under next square | Conditional | Proved in §5.2 |

The gap that remains is positional: proving that enough d-gaps fall inside the safe window $[h, h^2)$ at each stage. For $d=2$, this is the Twin Prime Conjecture in this framework.

---

## 6. The Open Local Density Question

The copy-or-merge rule constrains how gaps can change, but it does not by itself prove that 2-gaps persist in the local safe zone. The Twin Prime Conjecture requires a local guarantee: that a 2-gap exists in the specific interval $[p, p^2]$.

### The Question

Let $G_{\text{local}}(p)$ be the number of 2-gaps in $[p, p^2]$ after sieving by all primes less than $p$. The filter at this layer has exactly $p-1$ bullets (strikes at $p, 2p, \dots, (p-1)p$).

**Open Question:** Does $G_{\text{local}}(p) > p$ hold for all sufficiently large $p$?

If yes, the sieve lacks the capacity to destroy all local 2-gaps, and twin primes persist indefinitely.

### Status

This question remains **open** in the formal verification sense. It is equivalent to the Twin Prime Conjecture in this framework.

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

However, empirical evidence is not a formal proof. The local density question remains open. Full data from $p=3$ to $p=997$ is available in the companion [Empirical Analysis](../draft/draft-empirical-g-local-analysis.md).

---

## 7. Conclusion

The article proves several structural facts about gap evolution under sieve transitions:

1. **Copy-or-merge rule**: every new gap is either a copied old gap or the sum of a contiguous block of old gaps (§2).
2. **Non-generation**: if a gap value $d$ is absent and not representable as a contiguous sum, it stays absent forever (§3). For $d=2$ in post-2 stages, absence is permanent.
3. **Full-period survival**: each d-gap has exactly $h-2$ surviving descendants over a full expanded period (§4).
4. **Global-local boundary**: full-period survival does not imply safe-window survival, because the period grows primorially while the safe window grows quadratically (§5).

The remaining open question is positional: whether enough 2-gaps fall inside $[p, p^2]$ at each stage to survive the next filter. Empirical data supports the inequality $G_{\text{local}}(p) > p$ for all tested primes $p \ge 37$ up to $p=997$, but this is not a formal proof.

---

## 8. Future Work

Formalizing the twin-prime persistence boundary and the G-local crossover point requires either a verified local-density inequality or a constructive upper bound on how far a gap can grow before the copy-or-merge rule guarantees a 2-gap survives. This remains open and is equivalent to the Twin Prime Conjecture in this framework.

---

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*. Proceedings of the ACM on Programming Languages, OOPSLA Issue.

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Empirical Analysis of $G_{\text{local}}$: The Local 2-Gap Density in Sieve Sequences*. Available at: [articles/draft/draft-empirical-g-local-analysis.md](../draft/draft-empirical-g-local-analysis.md)

---

## Appendix A: Verification Status

This article does not introduce a new verified property. It relies on the verified foundations cited in the companion articles, describes the copy-or-merge rule mathematically, proves full-period survival via CRT, and marks the local-density statement as open.
