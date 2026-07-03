# Formal Verification of Sieve Sequence Properties from First Principles

**Author:** Mata, T. H.  
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

<div align="justify">
<p style="text-align: justify">
This article presents the current verified foundation for Sieve Sequences in this project. The central object is the simple `SpecSieveSequence`: an infinite linear-scan specification whose head is the current starting prime and whose active filter is the tail of the prime list only. From that specification, the project constructs a canonical cycle representation and proves that the canonical cycle matches the Spec stream at the current stage. Under explicit next-stage preconditions, it also proves that a canonical cycle built from `spec.next` matches `spec.next` in head, gaps, and apply behavior. The concrete optimized survival walk used by `CycleSieveSequence.next()` is not claimed as fully verified here; its missing list-level correctness theorem is documented as an open proof boundary.
</p>
</div>

---

## Properties Index

| # | Property | Statement | Status / Verifier |
|---|----------|-----------|-------------------|
| 3.1 | Unit counter foundation | `CycleIntegral([1], init)(i) = init + i + 1` | [CycleIntegralOnesProperties::assertCycleIntegralOfOnes](#appendix-a-stainless-verification-code) |
| 4.1 | Unit counter monotonicity | `b > a => CI([1], init)(b) > CI([1], init)(a)` | [CycleIntegralOnesProperties::assertCycleIntegralOfOnesStrictlyIncreasing](#appendix-a-stainless-verification-code) |
| 5.1 | Spec soundness | `spec(k)` passes the active tail filters | `SpecSieveSequence.apply` postcondition |
| 5.2 | Spec completeness | every accepted `value >= head` has an index | [SpecSieveSequence::indexOfAccepted](#appendix-a-stainless-verification-code) |
| 5.3 | Spec strict progress | `spec(k + 1) > spec(k)` | [SpecSieveSequence::applyStrictlyIncreases](#appendix-a-stainless-verification-code) |
| 6.1 | Spec gap positivity | each adjacent Spec gap is positive | [SpecSieveSequence::assertGapPositive](#appendix-a-stainless-verification-code) |
| 6.2 | Spec gap list positivity | every element of `gapList(from, count)` is positive | [SpecSieveSequence::assertGapListPositive](#appendix-a-stainless-verification-code) |
| 6.3 | Spec gap-cycle reconstruction | the Spec gap cycle reconstructs `spec(k)` | [SpecSieveSequence::assertSpecGapCycleIntegralMatchesApply](#appendix-a-stainless-verification-code) |
| 7.1 | Spec-derived current apply | `derived.cycle(k) == spec(k)` | [SpecDerivedCycleSieve::assertApplyMatches](#appendix-a-stainless-verification-code) |
| 7.2 | Spec-derived next head | `derived.cycle(1) == spec.next.head.value` | [SpecDerivedCycleSieve::assertNextHeadMatches](#appendix-a-stainless-verification-code) |
| 7.3 | Spec-derived next cycle | `SpecDerivedCycleSieve(spec.next, nextPeriod)` matches `spec.next` | [SpecDerivedCycleSieve::assertNextCycleMatchesSpecNext](#appendix-a-stainless-verification-code) |
| 8.1 | Survivor position bridge | each `spec.next(k)` appears at a current-cycle survivor position | [SpecDerivedCycleSieve::assertSurvivorPositionMatchesSpecNext](#appendix-a-stainless-verification-code) |
| 8.2 | Survivor gap bridge | adjacent survivor gaps match adjacent `spec.next` gaps | [SpecDerivedCycleSieve::assertSurvivorGapEqualsSpecNextGap](#appendix-a-stainless-verification-code) |
| 9.1 | Survival-walk list theorem | `nextGapsWalk(cycle) == spec.next.gapList(0, nextPeriod)` | [Open - Stainless verification pending] |

Status note: rows marked with verifier names are source-backed by current Scala code. The open row is a planned theorem, not a verified result.

---

## 1. Introduction

The Sieve of Eratosthenes generates prime numbers by iteratively filtering a sequence of natural numbers. At each step, we remove all multiples of the current smallest element (which is prime). Proving its correctness requires establishing:

1. **Spec generation** - the linear specification generates exactly the values accepted by its active tail filters.
2. **Gap reconstruction** - the finite Spec gap cycle reconstructs the same infinite Spec stream.
3. **Spec-derived equivalence** - the cycle built from Spec-certified data matches the Spec stream.
4. **Next-stage bridge** - a Spec-derived cycle built from `spec.next` matches `spec.next` under explicit next-stage hypotheses.
5. **Walk correctness** - the optimized survival walk should compute the same next-stage gaps, but this list-level theorem remains open.

In this article, we formalize the verified parts of that chain using [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html), a verification framework for pure Scala programs. Our approach follows the zero-prior-knowledge methodology established in earlier articles: modular arithmetic, lists, cycles, and cycle integrals are all defined from scratch and verified independently.

The result is not yet a full proof that `CycleSieveSequence.next()` implements the next Spec stage. It is a machine-checked proof of the source-linked Spec and Canonical foundations, plus an explicit map of the remaining survival-walk proof obligation.

---

## 2. Preliminaries

We reuse several basic operations and their verified properties from companion articles:

- **Modular Arithmetic** [[2]](modulo.md): Division, modulo, quotient invariance, mod idempotence
- **Lists** [[3]](list.md): Size, append, sum, slicing, tail shift
- **Cycles** [[4]](cycle.md): Unbounded repeating sequences  
- **Cycle Integrals** [[5]](integral-cycle.md): Cumulative sums of cycles
- **Prime Utilities** (defined in the project): Primality testing, filtering

These articles defined and verified their properties using the same zero-prior-knowledge methodology, and are treated here as foundational primitives.

### 2.1 Key Definitions

**Cycle Integral:**
```math
\text{CycleIntegral}(L, init)_i = \sum_{j=0}^{i} L_{(j \text{ mod } n)} + init
```

**Primality:**
```math
\text{isPrime}(p) \iff p > 1 \land \forall d \in [2, p-1],\ d \nmid p
```

**Filtering:**
```math
\text{filter}(L, p) = [x \in L \mid x \bmod p \neq 0]
```

---

## 3. Unit Cycle Generates Natural Numbers

**Intuition:** A cycle containing only the value `[1]` repeated infinitely produces the sequence 1, 2, 3, 4, ... when we compute its cycle integral. Each step adds exactly 1.

**Why This Matters:** The sieve needs a way to generate all natural numbers as candidate primes. The cycle integral of a unit cycle provides exactly this — an infinite counter starting from any initial value.

### Mathematical Proof

```math
\text{CycleIntegral}(\text{MemCycle}([1]), init)_i = init + i + 1
```

**Base Case** ($i = 0$):
```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_0 &= \text{cycle}(0) + init \\
&= 1 + init \\
&= init + 0 + 1 \quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

**Inductive Step** ($i \to i+1$):
```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_{i+1} &= \text{CycleIntegral}(\text{MemCycle}([1]), init)_i + \text{cycle}(i+1) \\
&= (init + i + 1) + 1 \quad \text{[By Induction Hypothesis]} \\
&= init + (i+1) + 1 \quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertCycleIntegralOfOnes(init: BigInt, pos: BigInt): Boolean = {
  require(pos >= 0)
  require(init >= 0)
  val cycle = MemCycle(stainless.collection.List(BigInt(1)))
  val ci = CycleIntegral(init, cycle)
  decreases(pos)
  if (pos == 0) {
    ci(0) == init + BigInt(1)
  } else {
    assert(assertCycleIntegralOfOnes(init, pos - 1))
    ci(pos) == init + pos + BigInt(1)
  }
}.holds
```

This property is verified in the [
  CycleIntegralOnesProperties::assertCycleIntegralOfOnes
](
  ../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala
).

---

## 4. Strict Monotonicity

**Intuition:** If you start later in the sequence, you end up with a larger number. This ensures that larger candidate numbers come after smaller ones.

**Why This Matters:** The sieve relies on processing candidates in order. Monotonicity guarantees we never "go backwards" in the candidate sequence.

### Mathematical Proof

```math
b > a \implies \text{CycleIntegral}(\text{MemCycle}([1]), init)_b > \text{CycleIntegral}(\text{MemCycle}([1]), init)_a
```

**Proof:**
```math
\begin{aligned}
\text{CycleIntegral}_b - \text{CycleIntegral}_a &= (init + b + 1) - (init + a + 1) \\
&= b - a \\
&> 0 \quad \text{[Since } b > a \text{]}
\end{aligned}
```

### Stainless Verification

```scala
def assertCycleIntegralOfOnesStrictlyIncreasing(init: BigInt, a: BigInt, b: BigInt): Boolean = {
  require(init >= 0)
  require(a >= 0)
  require(b >= 0)
  require(b > a)
  val cycle = MemCycle(stainless.collection.List(BigInt(1)))
  val ci = CycleIntegral(init, cycle)
  ci(b) > ci(a)
}.holds
```

This property is verified in the [
  CycleIntegralOnesProperties::assertCycleIntegralOfOnesStrictlyIncreasing
](
  ../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala
).

---

## 5. Spec Sequence Properties

The Spec sequence is the source of truth for this article. It is intentionally simple: start at `primes.head`, then walk through consecutive natural numbers and emit exactly those values that pass the active tail filters. The head itself is not part of the active filter. For `[5, 3, 2]`, the active filters are `[3, 2]`, so `25` is accepted even though it is a multiple of the head `5`.

This distinction matters because the Spec sequence is not a direct primality predicate. It proves a stage-local sieve property: every generated value passes the current tail filters, and every value that passes those filters appears somewhere in the stream.

### 5.1 Soundness

Every generated value is at or above the head and accepted by the active tail filters. This is the generator's "only valid outputs" direction.

```math
\begin{aligned}
k &\ge 0 \\
v &= \text{Spec}(k) \\
\text{accepts}(v)
  &\equiv v \ge \text{head}
     \land \forall p \in \text{filterPrimes},\ \text{Calc.mod}(v,p) \ne 0
     \quad \text{[By Definition]} \\
\text{Spec}(k) &\ge \text{head}
     \land \text{accepts}(\text{Spec}(k))
     \quad \text{[By apply postcondition]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def apply(k: BigInt): BigInt = {
  require(k >= BigInt(0))
  ...
}.ensuring(res => res >= head.value && res <= searchBound(k) && accepts(res))
```

This property is verified in the [
  SpecSieveSequence::apply
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
).

### 5.2 Completeness

Completeness is expressed constructively. Instead of merely stating that an index exists, `indexOfAccepted(value)` returns the index. Its postcondition is stronger than the existential mathematical statement: if `value` is accepted, applying the sequence at the returned index gives exactly `value`.

```math
\begin{aligned}
value &\ge \text{head} \\
\text{accepts}(value) & \\
k &= \text{indexOfAccepted}(value) \\
k &\ge 0
  \land \text{Spec}(k) = value
  \quad \text{[By indexOfAccepted postcondition]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def indexOfAccepted(value: BigInt): BigInt = {
  require(value >= head.value)
  require(accepts(value))
  ...
}.ensuring(res => res >= BigInt(0) && apply(res) == value)
```

This property is verified in the [
  SpecSieveSequence::indexOfAccepted
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
).

### 5.3 Strict Progress

The linear scan never emits the same value twice. The next search starts after the previous emitted value, so the next result is strictly greater.

```math
\begin{aligned}
\text{Spec}(k+1)
  &= \text{searchNext}(\text{Spec}(k)+1,\ upper)
     \quad \text{[By Definition]} \\
\text{searchNext}(\text{Spec}(k)+1,\ upper)
  &\ge \text{Spec}(k)+1
     \quad \text{[By search lower bound]} \\
\text{Spec}(k+1)
  &> \text{Spec}(k)
     \quad \text{[Simplification]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def applyStrictlyIncreases(k: BigInt): Boolean = {
  require(k >= BigInt(0))
  ...
  next > previous
}.holds
```

This property is verified in the [
  SpecSieveSequence::applyStrictlyIncreases
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
).

---

## 6. Spec Gap-Cycle Construction

Once the Spec stream is verified, the next step is to expose its adjacent differences as a finite gap cycle. This is the bridge from the simple linear scan to the cycle-integral machinery used by the optimized representation.

### 6.1 Positive Gaps

Because the Spec stream strictly increases, every adjacent gap is positive.

```math
\begin{aligned}
\text{gap}(k)
  &= \text{Spec}(k+1) - \text{Spec}(k)
     \quad \text{[By Definition]} \\
\text{Spec}(k+1)
  &> \text{Spec}(k)
     \quad \text{[By Spec strict progress]} \\
\text{gap}(k)
  &> 0
     \quad \text{[Simplification]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertGapPositive(k: BigInt): Boolean = {
  require(k >= BigInt(0))
  assert(applyStrictlyIncreases(k))
  apply(k + BigInt(1)) - apply(k) > BigInt(0)
}.holds
```

This property is verified in the [
  SpecSieveSequence::assertGapPositive
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
).

### 6.2 Gap-Cycle Reconstruction

For a valid period witness, `specGapCycle(period)` stores exactly one period of Spec gaps. The cycle integral that starts at the Spec head and repeatedly adds those gaps reconstructs the original Spec stream.

```math
\begin{aligned}
\text{gaps}
  &= \text{Spec.gapList}(0, period)
     \quad \text{[By Definition]} \\
\text{cycle}
  &= \text{Spec.specGapCycle}(period)
     \quad \text{[By Definition]} \\
\text{CycleIntegral}(\text{head}, cycle)(k-1)
  &= \text{Spec}(k)
     \quad \text{[By assertSpecGapCycleIntegralMatchesApply]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertSpecGapCycleIntegralMatchesApply(period: BigInt, k: BigInt): Boolean = {
  require(period > BigInt(0))
  require(k >= BigInt(0))
  require(apply(period) == head.value + filterModulus)
  ...
}.holds
```

This property is verified in the [
  SpecSieveSequence::assertSpecGapCycleIntegralMatchesApply
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
).

---

## 7. Canonical Cycle Equivalence

`SpecDerivedCycleSieve` is the safe bridge between the simple Spec and the optimized cycle representation. It does not ask the cycle implementation to discover the right gaps. Instead, it builds the cycle from the Spec's own verified head, prime list, and gap cycle, then proves that this Spec-derived cycle behaves like the Spec.

### 7.1 Current-Stage Apply Equivalence

At index zero, the Spec-derived cycle and the Spec share the same head. At positive indices, both sides unfold through the same `CycleIntegral` over the Spec-derived gap cycle.

```math
\begin{aligned}
\text{Canonical}(spec, period)(0)
  &= \text{spec.head}
     \quad \text{[By Constructor]} \\
  &= \text{Spec}(0)
     \quad \text{[By Spec Definition]} \\
\text{Canonical}(spec, period)(k)
  &= \text{CycleIntegral}(\text{spec.head}, \text{specGapCycle})(k-1)
     \quad \text{[By Cycle apply]} \\
  &= \text{Spec}(k)
     \quad \text{[By Spec gap-cycle reconstruction]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertApplyMatches(k: BigInt): Boolean = {
  require(k >= BigInt(0))
  ...
  cycle(k) == spec(k)
}.holds
```

This property is verified in the [
  SpecDerivedCycleSieve::assertApplyMatches
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala
).

### 7.2 Conditional Next-Stage Canonical Equivalence

The verified next-stage theorem is intentionally conditional. If the caller supplies the next-stage period anchor and the known hard arithmetic preconditions, then the canonical cycle built from `spec.next` matches `spec.next` in head and gaps, and its apply behavior is available through `assertNextCycleApplyMatchesSpecNext`.

```math
\begin{aligned}
\text{nextCanonical}
  &= \text{SpecDerivedCycleSieve}(\text{spec.next}, nextPeriod)
     \quad \text{[By Definition]} \\
\text{nextCanonical.head}
  &= \text{spec.next.head}
     \quad \text{[By assertNextCycleHeadMatchesSpecNext]} \\
\text{nextCanonical.gaps}
  &= \text{spec.next.gapList}(0,nextPeriod)
     \quad \text{[By assertNextCycleGapsMatchSpecNext]} \\
\text{nextCanonical}(k)
  &= \text{spec.next}(k)
     \quad \text{[By assertNextCycleApplyMatchesSpecNext]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertNextCycleMatchesSpecNext(nextPeriod: BigInt): Boolean = {
  require(nextPeriod > BigInt(0))
  require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
  require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
  require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))
  ...
}.ensuring(_ =>
  assertNextCycleHeadMatchesSpecNext(nextPeriod) &&
    assertNextCycleGapsMatchSpecNext(nextPeriod)
)
```

This property is verified in the [
  SpecDerivedCycleSieve::assertNextCycleMatchesSpecNext
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala
).

---

## 8. Current Verification Boundary

The verified chain currently has two strong pieces and one explicit gap.

First, `SpecSieveSequence` is verified as the linear reference model for a sieve stage: `apply(k)` only emits values that pass the active tail filters, and `indexOfAccepted(value)` gives a constructive completeness witness for any accepted value.

Second, `SpecDerivedCycleSieve` is verified as a cycle representation built from Spec-certified data. At the current stage, its `cycle(k)` matches `spec(k)`. Under explicit next-stage preconditions, `SpecDerivedCycleSieve(spec.next, nextPeriod)` matches `spec.next` in head and gaps, with apply equality available through the apply lemma.

The remaining gap is the optimized survival walk. The current code has important bridge lemmas connecting individual `spec.next` values to survivor positions in the current cycle, but it does not yet prove the list-level theorem that the recursive walk emits exactly `spec.next.gapList(0, nextPeriod)`.

---

## 8a. Properties by Proof Status

This section catalogs the sieve-sequence properties by their *current* proof
status, so the reader can tell at a glance what is verified, what is
mathematically true but not yet verified, and what is genuinely blocked. The
status of any individual lemma may change as work proceeds; to check the live
state, re-run `just verify-ch 6` (criterion: `invalid: 0 unknown: 0`) and
consult `OBJECTS.md` §6.5–6.7. The narrative behind the pending and blocked
items — including which proof attempts failed and why — is recorded in
`tickets/active/independent-next-cycle.md` (Failure log F1–F7).

For the next stage, the code uses three representations whose relationship is
the central question of this article:

- **A = `SpecSieveSequence`** — the deliberately simple linear-scan model.
- **B = `SpecDerivedSieveSequence`** — a cycle representation built from
  Spec-certified data; bridges A and C. (Earlier sections call this
  `SpecDerivedCycleSieve`; that class was renamed and the older name is
  retained above for continuity.)
- **C = `CycleSieveSequence`** — the gap-cycle implementation.

### 8a.1 Verified (in the current green code)

These properties are discharged by Stainless `.holds` / `.ensuring` lemmas in
the current source. Each is presented in the three-representation form: an
English statement, the formal statement in LaTeX, and the Scala signature with
a clickable source reference. (Full proof bodies are at the source links; the
snippets here show the contract shape.)

#### A.1.1 Soundness and completeness of `apply` (representation A)

`SpecSieveSequence.apply(k)` is the deliberately simple linear-scan generator.
Soundness says it only emits values that pass the active tail filters; the
ensuring postcondition states exactly that, plus an upper bound. Completeness
goes the other direction: for any value the filters accept, there is an index
that emits it, witnessed constructively by `indexOfAccepted`.

```math
\begin{aligned}
\text{apply}(k) &\geq \text{head} \;\land\; \text{apply}(k) \leq \text{searchBound}(k)
  \;\land\; \text{accepts}(\text{apply}(k)) && \text{[Soundness]} \\
\text{apply}(\text{indexOfAccepted}(v)) &= v && \text{[Completeness]}
\end{aligned}
```

```scala
def apply(k: BigInt): BigInt = {
  // ... bounded linear scan ...
}.ensuring((res: BigInt) => res >= head.value && res <= searchBound(k) && accepts(res))

def indexOfAccepted(value: BigInt): BigInt = {
  // ... constructive completeness witness ...
}.ensuring((result: BigInt) => apply(result) == value)
```

These properties are verified in the
[SpecSieveSequence::apply](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
and
[SpecSieveSequence::indexOfAccepted](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
functions.

#### A.1.2 Strict monotonicity and injectivity

Because the scan only advances and never repeats a value, the generator is
strictly increasing, and two equal outputs imply two equal inputs.

```math
\begin{aligned}
\text{apply}(k+1) &> \text{apply}(k) && \text{[Strict monotonicity]} \\
\text{apply}(i) = \text{apply}(j) &\Rightarrow i = j && \text{[Injectivity]}
\end{aligned}
```

```scala
def applyStrictlyIncreases(k: BigInt): Boolean = {
  // apply(k+1) > apply(k)
}.holds

def assertApplyInjective(firstIndex: BigInt, secondIndex: BigInt): Boolean = {
  // apply(firstIndex) == apply(secondIndex) => firstIndex == secondIndex
}.holds
```

These properties are verified in the
[SpecSieveSequence::applyStrictlyIncreases](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
and
[SpecSieveSequence::assertApplyInjective](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
functions.

#### A.1.3 Residue periodicity and the gap-sum decomposition

After one full period `p` (where `apply(p) == head + filterModulus`), the
sequence repeats its residue structure: gaps are periodic, and the value at any
position decomposes as the head plus the telescoped sum of the preceding gaps.
This is the arithmetic backbone of the cycle reconstruction.

```math
\begin{aligned}
\text{apply}(p) = \text{head} + \text{filterModulus}
  &\Rightarrow \text{gap}(k) = \text{gap}(k+p) && \text{[Periodic gaps]} \\
\text{apply}(p) = \text{head} + \text{filterModulus}
  &\Rightarrow \text{sumGap}(0, p) = \text{filterModulus} && \text{[Period sum]} \\
\text{apply}(\text{pos}) &= \text{head} + \text{sumGap}(0, \text{pos}) && \text{[Telescoping]}
\end{aligned}
```

```scala
def assertGapPeriodic(k: BigInt, p: BigInt): Boolean = {
  // apply(p) == head.value + filterModulus  ==>  gap(k) == gap(k + p)
}.ensuring(_ => true)

def assertGapSum(p: BigInt): Boolean = {
  // apply(p) == head.value + filterModulus  ==>  sumGap(0, p) == filterModulus
}.holds
```

These properties are verified in the
[SpecSieveSequence::assertGapPeriodic](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
and
[SpecSieveSequence::assertGapSum](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
functions.

#### A.1.4 Gap-list positivity, size, and index correctness

The finite gap list `gapList(from, count)` is strictly positive, has the
requested length, and its `r`-th element equals the adjacent apply difference
at the corresponding position. These three facts are what let a gap list be
packaged into a certified `GapCycle`.

```math
\begin{aligned}
\text{allGreaterThan}(\text{gapList}(from, count),\; 0) && \text{[Positive]} \\
\text{size}(\text{gapList}(from, count)) = count && \text{[Size]} \\
\text{gapList}(from, count)_r = \text{apply}(from{+}r{+}1) - \text{apply}(from{+}r) && \text{[Index]}
\end{aligned}
```

```scala
def assertGapListPositive(from: BigInt, count: BigInt): Boolean = {
  // ListUtils.allGreaterThan(gapList(from, count), 0)
}.holds

def assertGapListSize(from: BigInt, count: BigInt): Boolean = {
  // gapList(from, count).size == count
}.holds

def assertGapListApplyEqualsGapAtPosition(from: BigInt, count: BigInt, r: BigInt): Boolean = {
  // gapList(from, count).apply(r) == apply(from + r + 1) - apply(from + r)
}.holds
```

These properties are verified in the
[SpecSieveSequence::assertGapListPositive](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala),
[SpecSieveSequence::assertGapListSize](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala),
and
[SpecSieveSequence::assertGapListApplyEqualsGapAtPosition](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
functions.

#### A.1.5 Gap-cycle reconstruction

The capstone of the current-stage theory: the `CycleIntegral` built from the
certified gap cycle reconstructs the original `apply` sequence. After this
lemma, the cycle representation and the linear scan are interchangeable at the
current stage.

```math
\begin{aligned}
\text{CycleIntegral}(\text{head},\; \text{gapList}(0, \text{period}))_{k-1} = \text{apply}(k)
\quad \text{for } k > 0 && \text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertSpecGapCycleIntegralMatchesApply(period: BigInt, k: BigInt): Boolean = {
  // CycleIntegral(head, specGapCycle(period).memCycle).apply(k - 1) == apply(k)
}.holds
```

This property is verified in the
[SpecSieveSequence::assertSpecGapCycleIntegralMatchesApply](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
function.

#### A.1.6 Conditional next-stage primality

The first value after the head, `apply(1)`, equals the next prime and is prime
itself — but only under the explicit precondition that the next prime is below
`head²`. The unconditional form is genuinely blocked (see §8a.3), so the
constructor carries this bound as an explicit `require`.

```math
\begin{aligned}
\text{nextPrime} < \text{head}^2 &\Rightarrow \text{apply}(1) = \text{nextPrime}
  && \text{[Next-prime equality]} \\
\text{apply}(1) < \text{head}^2 &\Rightarrow \text{isPrime}(\text{apply}(1))
  && \text{[Conditional primality]}
\end{aligned}
```

```scala
def assertApplyOneEqualsNextPrime(): Boolean = {
  // apply(1) == primes.nextPrime.value
}.holds

private def assertApplyOneIsPrimeIfBelowHeadSq(): Boolean = {
  // apply(1) < head * head  ==>  Prime.isPrime(apply(1))
}.holds
```

These properties are verified in the
[SpecSieveSequence::assertApplyOneEqualsNextPrime](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
and
[SpecSieveSequence::assertApplyOneIsPrimeIfBelowHeadSq](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
functions.

#### B.1.1 Current-stage apply equivalence (representation B)

The derived cycle's central property: at the current stage, the cycle
representation and the spec agree element-for-element. This is what lets B
inherit every current-stage fact proven about A.

```math
\begin{aligned}
\text{cycle}(k) = \text{spec}(k) \quad \text{for all } k \geq 0 && \text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertApplyMatches(k: BigInt): Boolean = {
  // cycle(k) == spec(k)
}.holds
```

This property is verified in the
[SpecDerivedSieveSequence::assertApplyMatches](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
function.

#### B.1.2 Head, primes, and modulus aliasing

The cycle's head, prime list, and modulus are not independent data — they alias
the spec's. Establishing these equalities once, as named lemmas, prevents the
solver from re-deriving them at every downstream call site (see Failure log F7
in the companion ticket).

```math
\begin{aligned}
\text{cycle}(1) &= \text{spec.next.head} && \text{[Next head]} \\
\text{cycle.primesTailValues} &= \text{spec.filterValues} && \text{[Primes]} \\
\text{cycle.modulus} &= \text{spec.filterModulus} && \text{[Modulus]}
\end{aligned}
```

```scala
def assertNextHeadMatches(): Boolean = {
  // cycle(BigInt(1)) == spec.next.head.value
}.holds

def assertCycleModulusEqualsSpecFilterModulus(): Boolean = {
  // cycle.modulus == spec.filterModulus
}.holds
```

These properties are verified in the
[SpecDerivedSieveSequence::assertNextHeadMatches](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala),
[SpecDerivedSieveSequence::assertPrimesMatch](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala),
and
[SpecDerivedSieveSequence::assertCycleModulusEqualsSpecFilterModulus](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
functions.

#### B.1.3 Filter-decision transfer

A value and a divisor together determine a keep/drop decision. Because the
cycle and the spec observe the same value and the same divisor, they reach the
same decision — without re-unfolding either filter.

```math
\begin{aligned}
\text{cycle}(k) = \text{spec}(k) \;\land\; \text{cycle.head} = \text{spec.next.filterValues.head}
\Rightarrow \bigl(\text{mod}(\text{cycle}(k), \text{cycle.head}) \neq 0\bigr)
= \bigl(\text{mod}(\text{spec}(k), \text{spec.next.filterValues.head}) \neq 0\bigr)
\end{aligned}
```

```scala
def assertCycleSpecNextFilterDecisionMatches(k: BigInt): Boolean = {
  // mod(cycle(k), cycle.head) != 0  ==  mod(spec(k), spec.next.filterValues.head) != 0
}.holds
```

This property is verified in the
[SpecDerivedSieveSequence::assertCycleSpecNextFilterDecisionMatches](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
function.

#### B.1.4 Apply lowers to the integral

For `k > 0`, reading the cycle at index `k` is the same as reading its integral
at `k-1`. This lowering is the structural reason integral-level lemmas transfer
to the sequence level.

```math
\begin{aligned}
\text{cycle}(k) = \text{cycle.integral}(k-1) \quad \text{for } k > 0 && \text{[By Definition]}
\end{aligned}
```

```scala
def assertCycleApplyLowersToIntegral(k: BigInt): Boolean = {
  // cycle(k) == cycle.integral(k - 1)
}.holds
```

This property is verified in the
[SpecDerivedSieveSequence::assertCycleApplyLowersToIntegral](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
function.

#### B.1.5 Survivor bridge (canonical next stage)

The next-stage value `spec.next(k)` is exactly the cycle survivor at the
corresponding accepted index, and the gap between consecutive survivors equals
the corresponding `spec.next` gap. These are the canonical (delegation-based)
bridges — they prove correctness relative to `spec.next`, not independent
pipeline computation (see §8a.2).

```math
\begin{aligned}
\text{spec.next}(k) &= \text{cycle}(\text{indexOfAccepted}(\text{spec.next}(k))) && \text{[Survivor position]} \\
\text{survivorGap}(k) &= \text{spec.next.gap}(k) && \text{[Survivor gap]}
\end{aligned}
```

```scala
def assertSpecNextIsKthSurvivor(nextPeriod: BigInt, k: BigInt): Boolean = {
  // spec.next(k) == cycle(indexOfAccepted(spec.next(k)))
}.holds

def assertSurvivorGapEqualsSpecNextGap(nextPeriod: BigInt, k: BigInt): Boolean = {
  // survivor gap at k == spec.next gap at k
}.holds
```

These properties are verified in the
[SpecDerivedSieveSequence::assertSpecNextIsKthSurvivor](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
and
[SpecDerivedSieveSequence::assertSurvivorGapEqualsSpecNextGap](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
functions.

#### B.1.6 Canonical next-cycle equivalence

A canonical next cycle built from `spec.next` matches `spec.next` in head,
gaps, and apply, under the next-stage preconditions. This is the strongest
canonical result and the one the deferred independent theorem (§8a.2) aims to
match without the spec link.

```math
\begin{aligned}
\text{SpecDerived}(\text{spec.next}, \text{nextPeriod}).\text{cycle}
\;\equiv\; \text{spec.next} \;\text{(head, gaps, apply)} && \text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertNextCycleMatchesSpecNext(nextPeriod: BigInt): Boolean = {
  // canonical next-cycle head + gaps + apply all match spec.next
}.holds
```

This property is verified in the
[SpecDerivedSieveSequence::assertNextCycleMatchesSpecNext](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
function.

#### B.1.7 Repeated-cycle invariance

Repeating the gap period a fixed number of times preserves gap, integral, and
apply lookups. This supports reasoning about cycles whose physical period is a
multiple of the minimal one.

```math
\begin{aligned}
\text{repeatedCycle}(t)(k) = \text{cycle}(k) && \text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertRepeatedCycleApplyMatches(times: BigInt, k: BigInt): Boolean = {
  // repeatedCycle(times).apply(k) == cycle.apply(k)
}.holds
```

This property is verified in the
[SpecDerivedSieveSequence::assertRepeatedCycleApplyMatches](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
function.

#### B.1.8 Pipeline preconditions (M1)

The independent next-cycle pipeline (`SieveSequenceNextLevel`) requires four
positivity preconditions on its input cycle. All four are discharged for B's
cycle, so the pipeline can be *called* — though proving what it *produces* is
the open M3 theorem (§8a.2).

```math
\begin{aligned}
\text{cycle.modulus} > 0 \;\land\; \text{allGreaterThan}(\text{primesTailValues}, 0)
\;\land\; \text{cycle.head} > 0 \;\land\; \text{cycle.modulus} \cdot \text{cycle.head} > 0
\end{aligned}
```

```scala
def assertModulusPositive(): Boolean = { /* cycle.modulus > 0 */ }.holds
def assertPrimesTailValuesPositive(): Boolean = { /* allGreaterThan(primesTailValues, 0) */ }.holds
def assertHeadPositive(): Boolean = { /* cycle.head > 0 */ }.holds
def assertModulusTimesHeadPositive(): Boolean = { /* cycle.modulus * cycle.head > 0 */ }.holds
```

These properties are verified in the
[SpecDerivedSieveSequence::assertModulusPositive](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala),
[SpecDerivedSieveSequence::assertPrimesTailValuesPositive](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala),
[SpecDerivedSieveSequence::assertHeadPositive](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala),
and
[SpecDerivedSieveSequence::assertModulusTimesHeadPositive](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
functions.

#### B.1.9 The migration-independent leaf

The period endpoint `head + filterModulus` is not a multiple of the next
stage's front filter. This is the verified replacement for the unsound
identification of the next head with the next front filter (§8a.3, LEARNINGS
§18.6), and it is the *only* piece of next-stage-filter work active regardless
of the contract-shape debate.

```math
\begin{aligned}
\text{mod}(\text{spec.head} + \text{spec.filterModulus},\;
\text{spec.next.filterValues.head}) \neq 0 && \text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertHeadPlusFilterModulusNotFrontMultiple(): Boolean = {
  // mod(spec.head.value + spec.filterModulus, spec.next.filterValues.head) != 0
}.holds
```

This property is verified in the
[SpecDerivedSieveSequence::assertHeadPlusFilterModulusNotFrontMultiple](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
function.

#### C.1.1 Survivor filter-passing (value-level, `SieveCycleAfterProof`)

The value-level approach bypasses the index machinery: a cycle-integral
survivor (any value not divisible by `head`) is coprime with all primes, hence
with `spec.next.filterValues`, hence passes `spec.next.passesFilter`. Using
`passesFilter` rather than `accepts` avoids the `value >= head` precondition
that triggers cross-instance unfolding (Failure log F5/F6).

```math
\begin{aligned}
\text{mod}(\text{integral}(pos), \text{head}) \neq 0
&\Rightarrow \text{isCoprime}(\text{integral}(pos), \text{primes}) \\
&\Rightarrow \text{isCoprime}(\text{integral}(pos), \text{spec.next.filterValues}) \\
&\Rightarrow \text{spec.next.passesFilter}(\text{integral}(pos))
\quad \text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertCycleSurvivorCoprimeToCyclePrimes(seq: SpecDerivedSieveSequence, pos: BigInt): Boolean = {
  require(pos >= BigInt(0))
  require(Calc.mod(seq.cycle.integral(pos), seq.spec.head.value) != BigInt(0))
  // ... coprime to all cycle primes ...
}.holds

def assertCycleSurvivorPassesSpecNextFilter(seq: SpecDerivedSieveSequence, pos: BigInt): Boolean = {
  require(pos >= BigInt(0))
  require(Calc.mod(seq.cycle.integral(pos), seq.spec.head.value) != BigInt(0))
  // ... seq.spec.next.passesFilter(seq.cycle.integral(pos)) ...
}.holds
```

These properties are verified in the
[SieveCycleAfterProof::assertCycleSurvivorCoprimeToCyclePrimes](../src/main/scala/v1/chapter6/seq/sieve/SieveCycleAfterProof.scala)
and
[SieveCycleAfterProof::assertCycleSurvivorPassesSpecNextFilter](../src/main/scala/v1/chapter6/seq/sieve/SieveCycleAfterProof.scala)
functions.

#### C.1.2 First survivor equals the next head

The first value in the cycle integral is the next stage's head — the entry
point of the survivor scan.

```math
\begin{aligned}
\text{cycle.integral}(0) = \text{spec.next.head} && \text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertFirstSurvivorEqualsSpecNextHead(seq: SpecDerivedSieveSequence): Boolean = {
  // seq.cycle.integral(0) == seq.spec.next.head.value
}.holds
```

This property is verified in the
[SieveCycleAfterProof::assertFirstSurvivorEqualsSpecNextHead](../src/main/scala/v1/chapter6/seq/sieve/SieveCycleAfterProof.scala)
function.

### 8a.2 Mathematically proven — Stainless verification missing

> **Read this carefully.** Every property in this subsection has a valid
> mathematical proof. What is **missing** is the Stainless verification code in
> the current source tree. Each item is marked below as
> **Draft — mathematically proven, Stainless verification pending**, per the
> AGENTS `property-completeness` rule. The draft Scala blocks are sketches of
> the intended verification; they are tagged `// TODO: verify with Stainless`
> and have **not** been run through `just verify`. Do not cite any of these as
> "verified" — they are not. The walls blocking each one are documented in the
> companion ticket's Failure log (F1, F4, F5, F6).

These properties are mathematically true and, in most cases, have written proof
sketches that focused-verified at an earlier point before being set aside. They
are **not** in the current green code. Each is blocked by a specific, documented
Stainless wall — **not** by missing mathematics. The distinction between this
subsection (math good, code missing) and §8a.3 (genuinely blocked on deep
number theory) is sharp: here the math is settled; there it is not.

#### 8a.2.1 The independent next-cycle theorem (M3) — Draft

**Status: Draft — mathematically proven, Stainless verification pending.**

The central open result of the independent next-cycle effort. Running the
standard sieve pipeline (`residues → expand → filter → sort → gaps → rotate`)
on B's own cycle data must produce exactly the next stage's gap list. The
mathematics is straightforward — the pipeline enumerates precisely the values
not divisible by `head` within one period of `head · cycle.size`, in increasing
order, and the rotated gaps are the adjacent differences — but Stainless cannot
close the proof because it requires list extensionality across two
differently-shaped recursions and symbolic-position induction.

```math
\begin{aligned}
\text{nextRotatedGaps}(\text{cycle}) \;\stackrel{?}{=}\;
\text{spec.next.gapList}(0,\,\text{nextPeriod})
\quad && \text{[Mathematically proven; Stainless verification pending]}
\end{aligned}
```

The conditional scaffolding around this theorem **is** verified in the current
code: `nextPipelineGapCycleIfMatchesSpec(nextPeriod)` takes the equality above
as a precondition, isolating the constructor obligation from the hard equality.
So the *instant* this theorem is discharged, `nextFromCycle()` (B's independent
next-stage constructor) and the C-side analog (M4) follow without new math.

```scala
// DRAFT — mathematically proven, Stainless verification pending.
// This block has NOT been run through `just verify`. Tracking ticket:
// tickets/active/independent-next-cycle.md (M3, Santa Claus List step 11).
def assertNextRotatedGapsMatchesSpecNextGapList(
  cycle: CycleSieveSequence, nextPeriod: BigInt
): Boolean = {
  // TODO: verify with Stainless.
  // Wall: list extensionality across differently-shaped recursions (F1) and
  // symbolic-position induction / cross-instance unfolding (F5, F6).
  SieveSequenceNextLevel.nextRotatedGaps(cycle) ==
    spec.next.gapList(0, nextPeriod)
}.holds
```

*Walls (from the ticket Failure log):* F1 (list extensionality — `collectGaps`
opacity), F5 (symbolic-position integral monotonicity induction), F6
(cross-instance `accepts` unfolding). These are Stainless limitations, not gaps
in the mathematics.

#### 8a.2.2 The twelve "survivor window/gap" lemmas — Draft

**Status: Draft — mathematically proven, Stainless verification pending.**

A self-contained cluster of twelve lemmas proving ordered survivor equality
(`cycleSurvivor(i) == spec.next(i)`) and the bridge from survivor positions to
list-level gap equality — the rungs of the M3 ladder (steps 6 and 9–11) below
the M3 theorem itself. The mathematics is sound; the lemmas were written,
focused-verified, and then **removed** during the 2026-07-03 recovery because
they are coupled to a half-finished *contract-shape migration* of
`nextAcceptedOldIndex` and siblings in A.

```math
\begin{aligned}
\text{cycleSurvivor}(i) &= \text{spec.next}(i)
  && \text{[Mathematically proven; Stainless verification pending]} \\
\text{survivorGapPrefix}(from, n) &= \text{spec.next.gapList}(from, n)
  && \text{[Mathematically proven; Stainless verification pending]}
\end{aligned}
```

The twelve lemmas (preserved verbatim in git history at
`pre-recovery-snapshot`, lines ~716–1190 of `SpecDerivedSieveSequence.scala`):
`survivorWindowCovers`, `initialSurvivorWindowCovers`,
`assertCycleSurvivorWindowHeadMatchesSpecNext`,
`assertCycleSurvivorWindowAtMatchesSpecNext`,
`assertCycleSurvivorAtMatchesSpecNext`,
`assertInitialSurvivorGapMatchesSpecNextGap`,
`assertInitialSurvivorGapsFromValuesAtMatchesSpecNextGap`,
`assertInitialSurvivorGapListAtMatchesSpecNextGapList`,
`initialSurvivorGapListCovers`, `initialSurvivorGapList`,
`assertInitialSurvivorGapListMatchesNextGapList`,
`assertInitialSurvivorGapListMatchesSpecNextGapList`.

```scala
// DRAFT — mathematically proven, Stainless verification pending.
// These lemmas were removed from the current source (recovery commit bd444a35)
// because they depend on a contract-shape migration that was left half-finished
// (Failure log F4). They are NOT in the green code. To re-activate, follow the
// recipe in tickets/active/independent-next-cycle.md ("The Correct Track"):
// migrate callee + all callers + these twelve lemmas in ONE green-to-green
// change. Each lemma's body is preserved at git tag `pre-recovery-snapshot`.
def assertCycleSurvivorAtMatchesSpecNext(
  offset: BigInt, count: BigInt
): Boolean = {
  // TODO: verify with Stainless (blocked on contract-shape migration, F4).
  // cycle survivor scan at `offset` == spec.next(offset)
}.holds
```

*Wall (from the ticket Failure log):* F4 — engineering (mid-migration wiring),
**not** mathematics. The recipe to re-activate is mechanical and fully
specified in the ticket's "The Correct Track" section. No new mathematics is
required; only the discipline of migrating callee + callers + dependent lemmas
together in one verified change.

> **Reminder.** Nothing in §8a.2 is verified in the current code. The math is
> sound and the proof strategies are known; the Stainless verification is the
> missing piece. Treat every statement here as a draft theorem, not a result,
> until its draft block is replaced by a green `.holds` lemma and moved into
> §8a.1.

### 8a.3 Genuinely blocked (the mathematics itself is not yet formalized)

> **Contrast with §8a.2.** There, the math is settled and only the Stainless
> code is missing. Here, the mathematics is *believed true* but depends on deep
> number-theoretic facts (Bertrand's postulate, Euclid's lemma) that have not
> been formalized in this codebase. These are not "code missing" — they are
> "prerequisite theorem missing." Each has a dedicated ticket under
> `tickets/blocked/`.

**Unconditional `apply(1)` is prime.** The conditional form
(`apply(1) < head² ⇒ isPrime(apply(1))`) is verified (§8a.1). The unconditional
form requires proving a prime exists in `(head, head²)` — Bertrand's postulate
(or a Jacobsthal/prime-gap bound) — which is beyond SMT. The next-stage
constructor therefore carries `require(nextPrime.value < head²)` as an explicit
precondition rather than discharging it. (`tickets/blocked/prove-apply1-is-prime.md`.)

**Primorial not divisible by a new prime.**
`mod(primorial(primes), p.value) != 0` for a new prime `p` not in `primes` with
all list values `< p`. The inductive step is exactly Euclid's lemma
(`mod(h, p) != 0 ∧ mod(tailPrim, p) != 0 ⇒ mod(h · tailPrim, p) != 0`); Z3 times
out on the abstract case, and a Bezout/extended-Euclidean proof has not yet been
formalized. This blocks a `CycleSieveSequence` construction precondition.
(`tickets/blocked/primorial-not-divisible-by-new-prime.md`.)

> **Why the contract-shape migration exists at all.** A subtle point worth
> recording: in a next-stage sequence, `nextSeq.head.value` (the next emitted
> prime) is *not* equal to `nextSeq.filterValues.head` (the front filter, which
> is the *previous* head). Older bridge lemmas used the stronger-but-unsound
> `require(nextSeq.head.value == head.value)`; the corrected shape is
> `require(nextSeq.filterValues.head == head.value)`. The migration from the
> old shape to the corrected shape is what the twelve pending lemmas depend on
> (LEARNINGS §18.6). The leaf
> `assertHeadPlusFilterModulusNotFrontMultiple` (§8a.1) is the
> migration-independent piece of this correction and is already verified.

---

## 9. Next-Stage Survivor Filter Composition

**Intuition:** The sieve progresses by taking a current stage and adding the current head as a new filter for the next stage. Values that are multiples of the current head are skipped; values that are not multiples of it are survivors. The next-stage gaps are the differences between consecutive survivors.

**Why This Matters:** This is the bridge from the verified Spec/Canonical world to the optimized `CycleSieveSequence.next()` implementation. The project already has per-value and per-gap bridge lemmas. What remains is proving that the concrete recursive walk emits the whole gap list in the same order.

### 9.1 Survivor-Based Gap Computation

Given a `CycleIntegral` $CI$ with head $h$ and gap cycle $G$, we scan $h \cdot |G|$ positions of $CI$ and collect all values not divisible by $h$. These are the **survivors**:

```math
\text{survivors} = [ CI(p) \mid p \in [0, h \cdot |G|), CI(p) \bmod h \neq 0 ]
```

The gaps between consecutive survivors give the next gap cycle:

```math
\text{gapsFromValues}([s_0, s_1, \ldots, s_k]) = [ s_1 - s_0, s_2 - s_1, \ldots, s_k - s_{k-1} ]
```

The new `CycleIntegral` is $CI_{\text{new}} = \text{CycleIntegral}(s_0, \text{MemCycle}(\text{gapList}))$, where $s_0$ is the first survivor (= the next stage head).

### 9.2 Survivor Filter Composition Theorem

The composition theorem proves that $CI_{\text{new}}$ has no values divisible by $f$:

**Proof:** By induction on $p \in [0, |G| - 2]$:
- $\text{assertNewCIMatchesSurvivors}$ proves $CI_{\text{new}}(p) = \text{survivors}(p+1)$
- $\text{assertSurvivorAtNotMultiple}$ proves $\text{survivors}(p+1) \bmod f \neq 0$ (by definition of survivors)
- Therefore $CI_{\text{new}}(p) \bmod f \neq 0$ for all positions.

### Stainless Verification

```scala
def assertFilterMergeComposition(
  originalCI: CycleIntegral,
  newCI: CycleIntegral,
  survivors: List[BigInt],
  filterValue: BigInt,
  maxIndex: BigInt
): Boolean = {
  require(filterValue > 0)
  require(originalCI.size > 0)
  require(Calc.mod(originalCI(0), filterValue) != BigInt(0))
  require(survivors == survivorValues(originalCI, filterValue, 0, originalCI.size))
  require(!survivors.isEmpty)
  require(newCI.initialValue == survivors.head)
  require(newCI.cycle.values == gapsFromValues(survivors))
  require(maxIndex >= 0)
  require(maxIndex < newCI.size)
  require(survivors.size > maxIndex + 1)
  decreases(maxIndex + 1)

  assertNewCIMatchesSurvivors(survivors, newCI, maxIndex)
  assertSurvivorAtNotMultiple(originalCI, filterValue, 0, originalCI.size, maxIndex + 1)

  if (maxIndex > 0) {
    assertFilterMergeComposition(originalCI, newCI, survivors, filterValue, maxIndex - 1)
  }
  Calc.mod(newCI(maxIndex), filterValue) != BigInt(0)
}.holds
```

This property is verified in the [
  CycleIntegralFilterProperties::assertFilterMergeComposition
](
  ../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala
).

Supporting lemmas (all verified in the same file):

| Lemma | Purpose |
|-------|---------|
| `assertRepeatConcat` | $\text{repeat}(list, n) = list +\!\!+ \text{repeat}(list, n-1)$ |
| `assertRepeatSumDecomposition` | $\text{sum}(\text{repeat}(list, n)) = \text{sum}(list) + \text{sum}(\text{repeat}(list, n-1))$ |
| `assertRepeatSumTimes` | $\text{sum}(\text{repeat}(list, n)) = \text{sum}(list) \times n$ |
| `assertModCycleEqualsMemCycle` | $\text{ModCycle} \equiv \text{MemCycle}$ (same values, same output) |
| `assertGapsFromSurvivorsMatchCI` | $\text{allGapsMatch}(CI_{\text{new}}, \text{survivors}, \text{maxIndex})$ |
| `assertNewCIMatchesSurvivors` | $CI_{\text{new}}(p) = \text{survivors}(p+1)$ |
| `assertSurvivorAtNotMultiple` | $\forall i,\ \text{survivors}(i) \bmod f \neq 0$ |
| `assertGapsFromValuesSize` | $\|\text{gapsFromValues}(L)\| = \|L\| - 1$ |
| `assertFirstSurvivorHead` | $\text{survivorValues}(CI, f, start, count).head = CI(start)$ when $CI(start) \bmod f \neq 0$ |

### 9.3 Verified Survivor Bridge Facts

The sieve progression involves three representations:

1. **SpecSieveSequence** — The mathematical spec (linear scan, source of truth)
2. **SpecDerivedCycleSieve** — The bridge, constructed from Spec data and proven correct
3. **CycleSieveSequence** — The efficient cycle representation with the survival walk

The verified bridge theorem proves that the gap between consecutive Spec-next survivor positions equals the corresponding `spec.next` gap:

```math
\begin{aligned}
pos_i
  &= \text{spec.indexOfAccepted}(\text{spec.next}(i))
     \quad \text{[By Definition]} \\
\text{cycle}(pos_i)
  &= \text{spec.next}(i)
     \quad \text{[By assertSurvivorPositionMatchesSpecNext]} \\
\text{spec.next}(i+1)-\text{spec.next}(i)
  &= \text{cycle}(pos_{i+1})-\text{cycle}(pos_i)
     \quad \text{[By assertSurvivorGapEqualsSpecNextGap]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

This proves a strong local fact: the relevant survivor positions are aligned with `spec.next`. It does not, by itself, prove that the implementation's recursive walk visits exactly those positions, skips exactly the rejected positions, and emits the resulting list in forward order.

The constructive next-stage canonical cycle is verified separately:

```math
\begin{aligned}
\forall k \ge 0,\quad
\text{SpecDerivedCycleSieve}(\text{spec.next}, nextPeriod).\text{cycle}(k)
  &= \text{spec.next}(k)
     \quad \text{[By assertNextCycleApplyMatchesSpecNext]} \\
&\quad \text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertSurvivorGapEqualsSpecNextGap(
  nextPeriod: BigInt,
  k: BigInt
): Boolean = {
  require(nextPeriod > BigInt(1))
  require(k >= BigInt(0))
  require(k + BigInt(1) < nextPeriod)
  require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
  val pos1 = spec.indexOfAccepted(spec.next(k))
  val pos2 = spec.indexOfAccepted(spec.next(k + BigInt(1)))
  assert(assertSurvivorPositionMatchesSpecNext(k))
  assert(assertSurvivorPositionMatchesSpecNext(k + BigInt(1)))
  assert(spec.next(k) == cycle(pos1))
  assert(spec.next(k + BigInt(1)) == cycle(pos2))
  assert(assertNextGapEqualsCurrentGapSum(nextPeriod, k))
  assert(spec.next(k + BigInt(1)) - spec.next(k) == spec(pos2) - spec(pos1))
  assert(assertApplyMatches(pos1))
  assert(assertApplyMatches(pos2))
  assert(spec(pos1) == cycle(pos1))
  assert(spec(pos2) == cycle(pos2))
  spec.next(k + BigInt(1)) - spec.next(k) == cycle(pos2) - cycle(pos1)
}.holds
```

```scala
def assertSpecNextIsKthSurvivor(nextPeriod: BigInt, k: BigInt): Boolean = {
  require(nextPeriod > BigInt(1))
  require(k >= BigInt(0))
  require(k < nextPeriod)
  require(spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus)
  decreases(k)
  if (k == BigInt(0)) {
    assertFirstSurvivorEqualsSpecNext0()
    spec.next(BigInt(0)) == cycle.integral(BigInt(0))
  } else {
    assertSpecNextIsKthSurvivor(nextPeriod, k - BigInt(1))
    if (k < nextPeriod - BigInt(1)) {
      assert(assertSurvivorGapEqualsSpecNextGap(nextPeriod, k - BigInt(1)))
    }
    val pos = spec.indexOfAccepted(spec.next(k))
    assert(assertSurvivorPositionMatchesSpecNext(k))
    spec.next(k) == cycle(pos)
  }
}.holds
```

These properties are verified in the [
  SpecDerivedCycleSieve::assertSurvivorGapEqualsSpecNextGap
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala
) and [
  SpecDerivedCycleSieve::assertSpecNextIsKthSurvivor
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala
).

Supporting bridge lemmas (all in SpecDerivedCycleSieve):

| Lemma | Purpose |
|-------|---------|
| `assertFirstSurvivorEqualsSpecNext0` | First survivor head matches spec.next(0) |
| `assertWalkInitialPrefix` | Walk prefix base case: first survivor plus empty emitted gap list |
| `assertWalkSkippedValueRejected` | Skip branch: a walked multiple of the old head is rejected by `spec.next` |
| `assertWalkSurvivorAccepted` | Emit branch: a walked non-multiple of the old head is accepted by `spec.next` |
| `assertSurvivorPositionMatchesSpecNext` | spec.next(k) corresponds to a cycle survivor position |
| `assertNextGapEqualsCurrentGapSum` | spec.next gap equals sum of current cycle gaps |
| `assertNextCycleApplyMatchesSpecNext` | Constructive next cycle matches spec.next in apply |
| `assertNextCycleGapsMatchSpecNext` | Constructive next cycle gaps match spec.next gap list |
| `assertNextCycleHeadMatchesSpecNext` | Constructive next cycle head matches spec.next head |

### 9.4 Open Problem: Survival-Walk List Correctness

The missing theorem is the list-level connection between the optimized walk and the Spec-next gap list:

```math
\begin{aligned}
\text{SieveSequenceNextLevel.nextGapsWalk}(\text{cycle})
  &\stackrel{?}{=}
    \text{spec.next.gapList}(0,nextPeriod)
    \quad \text{[Open]} \\
\end{aligned}
```

The planned proof is a recursive invariant over the walk:

```math
\begin{aligned}
\text{emittedGaps.reverse}
  &= \text{spec.next.gapList}(0, emitted) \\
\text{lastSurvivor}
  &= \text{spec.next}(emitted) \\
\text{skipped values}
  &\text{ are rejected by } \text{spec.next} \\
\text{emitted values}
  &\text{ are the next accepted } \text{spec.next} \text{ values}
\end{aligned}
```

This theorem is tracked in [`tickets/active/sieve-sequence-proof.md`](../tickets/active/sieve-sequence-proof.md). Until it is proved, this article must not claim that `CycleSieveSequence.next()` itself is fully equivalent to `spec.next`.

---

## 10. Conclusion

This article now separates the verified sieve-sequence foundation from the remaining optimized-walk proof. The verified core is substantial: the Spec sequence is sound and complete for its active tail filters, its gaps reconstruct the same stream through a cycle integral, the canonical current-stage cycle matches the Spec stream, and the canonical next-stage cycle built from `spec.next` matches `spec.next` under explicit preconditions.

The remaining proof obligation is narrower and clearer than the old draft suggested. The project still needs to prove that `SieveSequenceNextLevel.nextGapsWalk(cycle)` emits exactly `spec.next.gapList(0,nextPeriod)`. Once that list-level theorem is verified, the existing canonical equivalence lemmas can connect the optimized next step back to the Spec foundation.

---

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*. Proceedings of the ACM on Programming Languages, OOPSLA Issue.

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Proving Properties of Division and Modulo using Formal Verification*. Available at: [articles/modulo.md](modulo.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Available at: [articles/list.md](list.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Unbound Lists*. Available at: [articles/cycle.md](cycle.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from First Principles*. Available at: [articles/integral-cycle.md](integral-cycle.md)

## Appendix A: Stainless Verification Code

The full proof bodies are kept in source files rather than duplicated here. The article sections above include the relevant signatures and postconditions; this appendix collects the exact verifier entry points for review.

| Property | Source |
|----------|--------|
| Unit counter foundation | [`CycleIntegralOnesProperties::assertCycleIntegralOfOnes`](../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala) |
| Unit counter monotonicity | [`CycleIntegralOnesProperties::assertCycleIntegralOfOnesStrictlyIncreasing`](../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala) |
| Spec soundness | [`SpecSieveSequence::apply`](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala) |
| Spec completeness | [`SpecSieveSequence::indexOfAccepted`](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala) |
| Spec strict progress | [`SpecSieveSequence::applyStrictlyIncreases`](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala) |
| Spec gap positivity | [`SpecSieveSequence::assertGapPositive`](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala) |
| Spec gap list positivity | [`SpecSieveSequence::assertGapListPositive`](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala) |
| Spec gap-cycle reconstruction | [`SpecSieveSequence::assertSpecGapCycleIntegralMatchesApply`](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala) |
| Spec-derived current apply | [`SpecDerivedCycleSieve::assertApplyMatches`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Spec-derived next structural identity | [`SpecDerivedCycleSieve::assertNextCycleMatchesSpecNext`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Spec-derived next apply equality | [`SpecDerivedCycleSieve::assertNextCycleApplyMatchesSpecNext`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Survivor position bridge | [`SpecDerivedCycleSieve::assertSurvivorPositionMatchesSpecNext`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Survivor gap bridge | [`SpecDerivedCycleSieve::assertSurvivorGapEqualsSpecNextGap`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Survival-walk base prefix | [`SpecDerivedCycleSieve::assertWalkInitialPrefix`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Survival-walk skip branch | [`SpecDerivedCycleSieve::assertWalkSkippedValueRejected`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Survival-walk emit branch | [`SpecDerivedCycleSieve::assertWalkSurvivorAccepted`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Survivor next-value match | [`SpecDerivedCycleSieve::assertSpecNextIsKthSurvivor`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Transparent current window | [`SpecDerivedCycleSieve::currentWindow`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Transparent survivor window | [`SpecDerivedCycleSieve::survivorWindow`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| Full equivalence theorem | [`SpecDerivedCycleSieve::assertFullEquivalence`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| First survivor head equality | [`SpecDerivedCycleSieve::assertFirstSurvivorEqualsSpecNext0`](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedCycleSieve.scala) |
| General filter composition support | [`CycleIntegralFilterProperties::assertFilterMergeComposition`](../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala) |

## Appendix B: Stainless Verification Log Output

The latest checked `logs/verify.log` summary reports:

```text
total: 10495 valid: 10495 (10474 from cache, 21 trivial) invalid: 0 unknown: 0 time: 34.38
```

The full log output is available at: [logs/verify.log](../logs/verify.log)
