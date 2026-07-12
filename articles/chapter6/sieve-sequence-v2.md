# Formal Verification of the Sieve Sequence

**Author:** Mata, T. H.
Independent Researcher
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

This article defines the **Sieve Sequence**, a mathematical object that
captures one step of Eratosthenes' sieve as a finite structure: a head
(the current prime), a tail prime list (the active filters), a modulus
(their product), and a gap cycle (the compressed transition to the next
stage). We prove three theorems: (1) the current stage faithfully
generates all values accepted by its filters; (2) the gap cycle
reconstructs the full infinite sequence via a cycle integral; (3) the
next stage — its head, its gap cycle, and therefore all its values —
can be computed from the current stage's structural data alone, without
re-evaluating modularity per candidate. Together, these establish that
the Sieve Sequence is self-contained: each stage carries enough
information to construct the next stage, and the chain of stages
generates the primes.

## 1. Introduction

Eratosthenes' sieve generates primes by iteratively filtering a sequence
of natural numbers. At each step, we remove all multiples of the current
smallest element (which is prime). Proving its correctness requires
establishing three facts:

1. The generator faithfully produces every value accepted by the
   active filters.
2. The gap cycle — the list of adjacent differences between consecutive
   accepted values within one period — reconstructs the full infinite
   generator.
3. The next stage's gap cycle can be constructed from the current
   stage's structural data, without re-running the linear scan.

This article formalizes and verifies these facts using
[Scala Stainless](https://epfl-lara.github.io/stainless/intro.html).
Our approach follows the zero-prior-knowledge methodology established in
companion articles: modulo arithmetic [[1]](../chapter2/modulo.md),
list operations [[2]](../chapter3/list.md), cycles [[3]](../chapter4/cycle.md),
and cycle integrals [[4]](../chapter4/integral-cycle.md).

## 2. Preliminaries

### 2.1 Notation

A sieve stage $S$ is defined by three fields:

| Symbol | Meaning |
|--------|---------|
| $h$ | The head — a prime, and the largest known prime so far |
| $\overline{P}$ | The list of all primes strictly smaller than $h$, in descending order |
| $G$ | The gap list — the adjacent differences between consecutive survivors in the interval $[h,\ h + \prod \overline{P})$. Each $g_i > 0$ and $\sum G = \prod \overline{P}$ |

The modulus $M = \prod \overline{P}$ is a derived abbreviation, with
$M = 1$ when $\overline{P}$ is empty (the empty product convention).

```math
\begin{aligned}
M = \begin{cases}
1 & \text{if } \overline{P} = [] \\
\displaystyle\prod_{p \in \overline{P}} p & \text{otherwise}
\end{cases}
\end{aligned}
```

### 2.2 Dependencies

This article relies on verified lemmas from companion articles:
- Modulo properties (shift from zero, quotient invariance, unit-step increment) [[1]](../chapter2/modulo.md)
- List properties (sum, product, concatenation, rotation) [[2]](../chapter3/list.md)
- Cycle properties (element access, periodicity, repeated-cycle invariance) [[3]](../chapter4/cycle.md)
- Cycle integral properties (sum, step, modulo periodicity, cycle shifts) [[4]](../chapter4/integral-cycle.md)

## 3. Definition of a Sieve Stage

A Sieve Stage is $\{h, \overline{P}, G\}$ where:

1. $h$ is prime and exceeds every $p \in \overline{P}$ (all previous primes are strictly smaller)
2. $\overline{P}$ is the list of all primes strictly less than $h$, in descending order
3. $G$ is the gap list — the adjacent differences between consecutive values accepted by the filters $\overline{P}$ in the interval $[h,\ h + M)$, where $M = \prod \overline{P}$ (with $M = 1$ when $\overline{P}$ is empty). Each $g_i > 0$ and $\sum G = M$.

From $S$, we define the linear scan generator:

```math
\begin{aligned}
\text{Spec}_0 &= h \\
\text{Spec}_{k+1} &= \min\{\, v > \text{Spec}_k \mid \text{accepts}(S, v) \,\}
\end{aligned}
```

And the gap-cycle integral:

```math
\begin{aligned}
\text{Cycle}_k &= \text{CycleIntegral}(h, G)_k
               = h + \sum_{i=0}^{k-1} G_{i \,\text{mod}\, n}
\end{aligned}
```

From $S$ we define the acceptance predicate and the gap list:

| Notation | Definition |
|----------|------------|
| $\text{accepts}(S, v)$ | $v$ passes all tail filters: $\forall p \in \overline{P},\ \text{mod}(v, p) \neq 0$ |
| $\text{gaps}(S)$ | The gaps of a sequence $S$, with $\text{gaps}(S)_k = S_{k+1} - S_k$ |
| $\text{Spec}'_k$, $\text{Cycle}'_k$ | The next stage's sequences (prime notation) |

When the stage is clear from context, we write $\text{Spec}_k$ and
$\text{gaps}(\text{Spec})_k$ without decoration.

The main theorem of this article is that these two definitions
coincide:

```math
\begin{aligned}
\text{Cycle}_k = \text{Spec}_k \quad \text{for all } k \ge 0
\end{aligned}
```

We prove this in stages: first establishing the spec's properties (§4),
then proving the gap cycle reconstructs the spec (§5), then establishing
equivalence (§6).

### 3.1 The Base Stage

The base stage $S_0 = \{h: 2,\ \overline{P}: [],\ G: [1]\}$ contains no
known primes: the filter list is empty ($\overline{P} = []$), the modulus
is $M = 1$ (by the empty product convention), and the single gap of size
$1$ generates all integers $2, 3, 4, \dots$ via the unit cycle — no
filtering occurs.

The first non-trivial stage $S_1 = \{h: 3,\ \overline{P}: [2],\ G: [2]\}$
contains one known prime (2) as its filter, with head 3 and a single
gap of size 2 — the distance from 3 to the next survivor 5.

Every subsequent stage is built from the previous one via the pipeline
construction (§7). By induction on the base, all stages are well-defined.

## 4. Spec Sequence Properties

### 4.1 Soundness

Every value emitted by the spec passes all tail filters.

```math
\begin{aligned}
\forall k \ge 0,\ \text{accepts}(S, \text{Spec}_k)
\quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

**Proof.** By definition, $\text{Spec}_0 = h$ and $h > p$ for every
$p \in \overline{P}$. Since all tail primes are larger than $h$,
$\text{mod}(h, p) = h \neq 0$ for every $p$ (small dividend property).
For $\text{Spec}_{k+1}$, the linear scan only advances to a value
that satisfies the acceptance predicate, so soundness holds by
construction.

This property is verified in the [
  SpecSieveSequence::apply
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
)
function.

### 4.2 Completeness

Every value accepted by the tail filters eventually appears in the
spec sequence.

```math
\begin{aligned}
\text{accepts}(S, v) \implies \exists\, k \ge 0,\ \text{Spec}_k = v
\quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

**Proof.** The linear scan starts at $h$ and advances until it reaches
the next survivor. Over the current period $[h, h + M)$, the gap list
represents exactly the values that survive filtering by the primes in
$\overline{P}$. Periodicity then repeats this survivor pattern every
$M$ positions, so every accepted value is eventually reached by the
scan. The scan terminates when it reaches that survivor.

This property is verified in the [
  SpecSieveSequence::indexOfAccepted
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
)
function.

### 4.3 Strict Monotonicity

The spec sequence is strictly increasing.

```math
\begin{aligned}
\forall k \ge 0,\ \text{Spec}_{k+1} > \text{Spec}_k
\quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

**Proof.** By definition, $\text{Spec}_{k+1}$ is the *first* value
greater than $\text{Spec}_k$ that is accepted. Therefore
$\text{Spec}_{k+1} \ge \text{Spec}_k + 1 > \text{Spec}_k$.

This property is verified in the [
  SpecSieveSequence::applyStrictlyIncreases
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
)
function.

### 4.4 Gap Positivity

Every adjacent difference in the spec is strictly positive.

```math
\begin{aligned}
\forall k \ge 0,\ \text{gaps}(\text{Spec})_k = \text{Spec}_{k+1} - \text{Spec}_k > 0
\quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

This follows immediately from strict monotonicity (§4.3).

This property is verified in the [
  SpecSieveSequence::assertGapPositive
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
)
function.

## 5. Gap-Cycle Reconstruction

### 5.1 Periodic Structure

The spec sequence is periodic with period $n = |G|$ and offset $M$:
after one full gap cycle, the value advances by exactly the modulus.

```math
\begin{aligned}
\text{Spec}_{n} = h + M \quad &\text{[Period bound]} \\
\text{Spec}_{k+n} = \text{Spec}_k + M \quad &\text{[Periodic shift]}
\end{aligned}
```

This follows from the residue periodicity lemma: the total sum of
one gap cycle equals $M$, so adding one cycle adds exactly $M$ to
the cumulative value.

### 5.2 Gap-Cycle Integral Reconstructs the Spec

The cycle integral built from the gap cycle — starting at $h$ and repeatedly
adding the gaps — produces exactly the same sequence as the spec's linear
scan. This is the bridge between the two representations: from this point
on, every fact about the spec holds for the cycle integral as well.

```math
\begin{aligned}
\text{CycleIntegral}(h, G)_{k-1} = \text{Spec}_k \quad \text{for all } k \ge 1
\quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

**Proof.** By induction on $k$.

**Base case** ($k = 1$):
```math
\begin{aligned}
\text{CycleIntegral}(h, G)_0 &= h + 0 && \text{[By definition of CycleIntegral]} \\
  &= h && \text{[Simplification]} \\
  &= \text{Spec}_1 && \text{[Since Spec}_1 = h + G_0 \text{ and } G_0 = 0 \text{ by the unit-gap property]} \\
  &\quad\blacksquare && \text{[Q.E.D. — Base case holds]}
\end{aligned}
```

**Inductive case** ($k > 1$). Assume the claim holds for $k - 1$.
```math
\begin{aligned}
\text{CycleIntegral}(h, G)_{k-1}
  &= \text{CycleIntegral}(h, G)_{k-3} + G_{k-2} + G_{k-1}
   && \text{[By gap telescoping, §5.5 of the integral-cycle article]} \\
  &= \text{Spec}_{k-2} + G_{k-2} + G_{k-1}
   && \text{[By induction hypothesis for } k-2 \text{]} \\
  &= \text{Spec}_{k-2} + (\text{Spec}_{k-1} - \text{Spec}_{k-2}) + (\text{Spec}_k - \text{Spec}_{k-1})
   && \text{[By definition of gaps: } G_i = \text{Spec}_{i+1} - \text{Spec}_i \text{]} \\
  &= \text{Spec}_k
   && \text{[Simplification — telescopic cancellation]} \\
  &\quad\blacksquare && \text{[Q.E.D. — Inductive case holds]}
\end{aligned}
```

The gap telescoping lemma proves that two consecutive gaps $G_{k-2} + G_{k-1}$
sum to the integral difference $\text{CycleIntegral}(h, G)_{k-1} - \text{CycleIntegral}(h, G)_{k-3}$.
The induction hypothesis identifies $\text{CycleIntegral}(h, G)_{k-3}$ with
$\text{Spec}_{k-2}$, and each gap equals a spec adjacent difference by
definition of $G$. The telescopic sum collapses to $\text{Spec}_k$.

This property is verified in the [
  SpecSieveSequence::assertSpecGapCycleIntegralMatchesApply
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
)
function.

## 6. Current-Stage Equivalence

The spec generator and the gap-cycle integral produce identical
sequences.

```math
\begin{aligned}
\text{Cycle}_k = \text{Spec}_k \quad \text{for all } k \ge 0
\quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

**Proof.** **Base case** ($k = 0$): $\text{Cycle}_0 = h = \text{Spec}_0$.

**Inductive case** ($k > 0$):
```math
\begin{aligned}
\text{Cycle}_k &= \text{CycleIntegral}(h, G)_{k-1}
  && \text{[By definition]} \\
  &= \text{Spec}_k
  && \text{[By gap-cycle reconstruction, §5.2]} \\
  &\quad\blacksquare && \text{[Q.E.D. — Inductive case holds]}
\end{aligned}
```

The equivalence means every property proven for the spec (soundness,
completeness, monotonicity, gap positivity) holds for the cycle
representation as well.

This property is verified in the [
  SpecDerivedSieveSequence::assertApplyMatches
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala
)
function.

## 7. Next-Stage Construction

Given a valid sieve stage $S = \{h, \overline{P}, G\}$, the next
stage $S' = \{h', \overline{P}', G'\}$ can be constructed from
$G$ alone, without re-evaluating $\text{accepts}$ per candidate.

### 7.1 The Pipeline

**1. Residues.** Evaluate the cycle integral at each position within
one gap period:
```math
\begin{aligned}
\text{residues} = [\text{Cycle}_0, \text{Cycle}_1, \dots, \text{Cycle}_{n-1}]
\end{aligned}
```

**2. Expand.** Lift the current-period residues through the next
period of length $h \cdot M$:
```math
\begin{aligned}
\text{expanded} =
  [\, r + iM \mid r \in \text{residues},\ 0 \le i < h \,]
\end{aligned}
```

**3. Filter.** Remove values divisible by $h$:
```math
\begin{aligned}
\text{survivors} = [\, v \in \text{expanded} \mid v \bmod h \neq 0 \,]
\end{aligned}
```

**4. Sort.** The survivors are already in index order; sort preserves
the scan order:
```math
\begin{aligned}
\text{sorted} = [s_0, s_1, \dots, s_{n-1}],\ s_i = \text{Cycle}_{\text{pos}_i}
\end{aligned}
```

**5. Gaps.** Adjacent differences between sorted survivors form the
next gap cycle:
```math
\begin{aligned}
\text{candidateGaps} = [s_1 - s_0,\ s_2 - s_1,\ \dots,\ s_{n-1} - s_{n-2}]
\end{aligned}
```

**6. Rotate.** Shift the gap list by one position so the head's gap
moves to the end, aligning the next stage:
```math
\begin{aligned}
G' = \text{rotateAt}(\text{candidateGaps},\ 1)
\end{aligned}
```

The new head is the first survivor: $h' = s_0$. The new tail primes
are $\overline{P}' = [h] \mathbin{+\!+} \overline{P}$. The new modulus
is $M' = h \cdot M$.

### 7.2 Pipeline Correctness Theorem

The pipeline output equals the next spec's gap list.

```math
\begin{aligned}
\text{gaps}(\text{Cycle}') = \text{gaps}(\text{Spec}') \quad
\blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

**Proof sketch.** Each step preserves correctness against $\text{Spec}'$:

- **Residues:** By current-stage equivalence (§6), $\text{Cycle}_k = \text{Spec}_k$
  for $k = 0,\dots,n-1$. The residues are exactly the spec values
  within one gap period.

- **Expand:** Repeating residues $h$ times covers $h \cdot n$ positions.
  By the survivor exactness lemmas (§5.9 of the integral-cycle article),
  a survivor is always found within $h$ copies of the gap cycle.

- **Filter:** Removes values divisible by $h$. Since $h$ is prime and
  exceeds every tail prime, it is coprime to all values that survive
  the tail filters: $\text{mod}(\text{Cycle}_k, h) \neq 0$ for every
  $k$ (individual coprime property, §2.2). The survivors are exactly
  the next-stage spec values.

- **Sort:** The spec's completeness establishes the bijection between
  scan order and $\text{Spec}'$'s index order.

- **Gaps:** $\text{Spec}'_{k+1} - \text{Spec}'_k = \text{gaps}(\text{Spec}')_k$
  by definition of gaps. The pipeline's adjacent-difference computation
  matches.

- **Rotate:** A one-position rotation shifts the gap list forward, moving
  the head's gap to the end so the new stage's head is at position $0$.
  matching $\text{Spec}'$'s canonical gap ordering.

The pipeline correctness is verified in the [
  SieveSequenceNextLevel
](
  ../src/main/scala/v1/chapter6/seq/sieve/SieveSequenceNextLevel.scala
) and [
  SpecCycleSieveEquivalence
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecCycleSieveEquivalence.scala
) modules. The next-stage gap equality lemma
$\text{gaps}(\text{Cycle}') = \text{gaps}(\text{Spec}')$ is verified in [
  SpecDerivedSieveSequence::assertNextCycleGapsMatchSpecNext
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala
), and the value equality
$\text{Cycle}'_k = \text{Spec}'_k$ in [
  SpecDerivedBySurvivors::assertCycleNextApplyEqualsSpecNext
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedBySurvivors.scala
).

### 7.3 Additional Structural Facts

The pipeline verifies two additional properties:

```math
\begin{aligned}
h' < h \cdot M \quad &\text{[Applied head bound]} \\
\text{mod}(\text{Cycle}_1, h \cdot M) = h' \quad &\text{[Head residue identity]}
\end{aligned}
```

The first guarantees a finite scan range. The second proves the next
head can be located by computing a residue modulo the expanded modulus.

The head bound is verified in [
  SpecDerivedSieveSequence::assertNextHeadLessThanNewModulus
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala
), and the residue identity in [
  SpecDerivedBySurvivors::assertNextHeadResidueIsSpecNextHead
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedBySurvivors.scala
).

The pipeline is expected to determine the next-stage gap count exactly:

```math
\begin{aligned}
|G'| = |G| \cdot (h - 1)
\end{aligned}
```

The intended proof is an exact finite count over the lifted residues,
not an asymptotic density argument. For each current survivor residue
$r$, the $h$ lifted values
$r,\ r + M,\ \dots,\ r + (h - 1)M$ should cover every residue class
modulo $h$ when $M$ is coprime to $h$. Exactly one lift is then
divisible by $h$ and removed. Summed over the current survivors, this
would remove $|G|$ values from the $h \cdot |G|$ expanded candidates,
leaving $|G| \cdot (h - 1)$ survivors.

This closed-form count is therefore best read as
**Draft - mathematically motivated, Stainless verification pending**.
The verified pipeline proves the construction and its local structural
facts above; the standalone `.holds` proof for the explicit count still
needs the modular uniqueness lemma and the corresponding list/count
bridge.

## 8. Unproven Axioms

The next-stage construction currently carries Bertrand's postulate as
an external number-theoretic precondition:

```math
\begin{aligned}
h' < h^2 \quad \text{[Bertrand's postulate]}
\end{aligned}
```

This says there is always a prime between $h$ and $h^2$. It is required
to prove that the first pipeline value $\text{Cycle}_1$ is prime. The
conditional form — *if* $h' < h^2$, then $\text{Cycle}_1$ is prime — is
fully verified. Making the theorem unconditional requires formalizing
Bertrand's postulate in Stainless; this is beyond the current scope.

The conditional form is verified in [
  SpecSieveSequence::assertApplyOneIsPrimeIfBelowHeadSq
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
).

The individual coprime property - $h$ is coprime to every tail prime -
is verified via the definition of $\text{isPrime}$. The closed-form
size theorem discussed in Section 7.3 still needs additional
Stainless work: in particular, it must establish the relevant
coprimality of $M$ and $h$ and connect the exact lifted-residue count
to the pipeline's lists.

## 9. Conclusion

We have defined the Sieve Sequence as a finite mathematical structure
and proven three fundamental properties:

1. The linear scan generator faithfully produces all accepted values.
2. The gap cycle reconstructs the full infinite sequence.
3. The next stage can be constructed from the current stage's gap
   cycle alone.

Together, these establish the Sieve Sequence as a self-contained
mathematical object: each stage carries enough structural information
to compute the next stage without linear search, and the chain of
stages generates the primes.

The core construction proofs described above are verified through
Stainless, with Bertrand's postulate (§8) appearing as an explicit
precondition where primality of the next head is needed. The explicit
closed-form size theorem in Section 7.3 remains pending until its
modular-counting and list-counting obligations are verified.

Computationally, the Sieve Sequence is a static state machine: once the
gap cycle is built, generating the next accepted value requires only a
single addition — `Cyclex_{k+1} = Cyclex_k + G_{k mod n}` — with no
modulo or division operations. The Sieve Stage avoids the candidate
testing cost of Eratosthenes' sieve entirely while producing an
identical output.

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). *Proving Properties of Division and Modulo using Formal Verification*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter2/modulo.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter2/modulo.md)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Formal Verification of Cyclic Lists*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from First Principles*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral-cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral-cycle.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Hardy, G. H. & Wright, E. M. (1979). *An Introduction to the Theory of Numbers* (5th ed.). Oxford University Press. §5.4 (Chinese Remainder Theorem), §15.1 (Sieve of Eratosthenes).
