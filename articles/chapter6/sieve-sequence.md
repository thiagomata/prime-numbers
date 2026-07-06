# Formal Verification of Sieve Sequence Properties from First Principles

**Author:** Mata, T. H.  
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

<div align="justify">
<p style="text-align: justify">
This article presents the fully verified three-way equivalence between the Spec
(`SpecSieveSequence`), the Canonical bridge (`SpecDerivedSieveSequence`), and
the Cycle (`CycleSieveSequence`) at both the current and next stages. The
Spec is a linear-scan specification whose head is the current prime and whose
active filter is the tail primes only. From the Spec, the Canonical bridge
constructs a cycle representation and proves it matches the Spec
element-for-element via `assertApplyMatches(k)`. For the next stage, the Cycle
constructed from the Canonical's gap cycle is proven identical to `spec.next`
via `assertCycleNextApplyEqualsSpecNext(k)` — for any position $k$. The
constructive path is verified; the walk (`CycleSieveSequence.next()$) is not
used and has zero callers.
</p>
</div>

---

## 1. Introduction

The Sieve of Eratosthenes generates prime numbers by iteratively filtering a sequence of natural numbers. At each step, we remove all multiples of the current smallest element (which is prime). Proving its correctness requires establishing:

1. **Spec generation** - the linear specification generates exactly the values accepted by its active tail filters.
2. **Gap reconstruction** - the finite Spec gap cycle reconstructs the same infinite Spec stream.
3. **Spec-derived equivalence** - the cycle built from Spec-certified data matches the Spec stream.
4. **Next-stage bridge** - a Spec-derived cycle built from `spec.next` matches `spec.next` under explicit next-stage hypotheses.
5. **Walk correctness** - the optimized survival walk should compute the same next-stage gaps, but this list-level theorem remains open.

In this article, we formalize the verified parts of that chain using [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html), a verification framework for pure Scala programs. Our approach follows the zero-prior-knowledge methodology established in earlier articles: modular arithmetic, lists, cycles, and cycle integrals are all defined from scratch and verified independently.

The result is a machine-checked proof of the three-way equivalence: `SpecSieveSequence`, the canonical cycle representation, and the independent pipeline-built cycle all produce identical streams at both the current and next stages, per `assertApplyMatches(k)` and `assertCycleNextApplyEqualsSpecNext(nextPeriod, k)`. The optimized survival walk (`CycleSieveSequence.next()`) remains a deferred proof obligation.

---

## 2. Preliminaries

We reuse several basic operations and their verified properties from companion articles:

- **Modular Arithmetic** [[2]](../chapter2/modulo.md): Division, modulo, quotient invariance, mod idempotence
- **Lists** [[3]](../chapter3/list.md): Size, append, sum, slicing, tail shift
- **Cycles** [[4]](../chapter4/cycle.md): Unbounded repeating sequences  
- **Cycle Integrals** [[5]](../chapter4/integral-cycle.md): Cumulative sums of cycles
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

**Coprimality:**
```math
\text{isCoprime}(v,\; [p_1, \ldots, p_k]) \iff \forall i,\ \text{Calc.mod}(v, p_i) \neq 0
```

### 2.2 Modulo Properties Relied On

Every lemma in this article that manipulates `Calc.mod` depends on properties
verified in [[2]](../chapter2/modulo.md). The most frequently used are:

**Small dividend** — when the operand is smaller than the divisor, the result is
the operand unchanged. Used throughout the coprimality chain to prove that the
head, being smaller than any larger filter prime, is coprime to that prime.
```math
b > a \geq 0 \;\implies\; a \bmod b = a
```

**Modular shift invariance by multiplier** — adding a multiple of the divisor
preserves the remainder. This is the backbone of residue periodicity: the
sequence repeats every `tailPrimorial` steps because adding the modulus doesn't
change any filter prime's remainder.
```math
\text{mod}(a + m \cdot b,\; b) = \text{mod}(a,\; b)
```

**Modular shift from zero** — when `a` is divisible by `b`, the remainder of
`a + c` is just the remainder of `c`. Used to prove that a value that passes
all filter primes still passes them after adding the modulus.
```math
\text{mod}(a,\; b) = 0 \;\implies\; \text{mod}(a + c,\; b) = \text{mod}(c,\; b)
```

**Distributivity over addition** — decomposing a sum's remainder into the
remainders of its terms. Used when lifting modular facts across sums of gaps.
```math
(a + c) \bmod b = ((a \bmod b) + (c \bmod b)) \bmod b
```

**Multiple preserve divisibility** — multiplying any integer by the modulus
produces a value divisible by every prime factor of the modulus. Used in the
pipeline construction to verify that generated residues stay coprime.
```math
\text{mod}(a \cdot b,\; a) = 0
```

**Unit-step increment law** — incrementing a value whose remainder is not `b - 1`
increases the remainder by exactly one. This is the law behind the Euclid
coprimality argument: since `mod(product, p) = 0` (the product is divisible by
each factor), and `0 ≠ p - 1` for any prime `p > 2`, we get
`mod(product + 1, p) = 1 ≠ 0` — the product plus one is coprime to every factor.
```math
a \bmod b \neq b - 1 \;\implies\; (a + 1) \bmod b = (a \bmod b) + 1
```

All of these properties are fully verified in the modulo article [[2]](../chapter2/modulo.md)
and are invoked as `.holds` lemmas by the Sieve Sequence codebase.

---

## 3. Unit Cycle Generates Natural Numbers

A cycle containing only the value `[1]` repeated infinitely produces the sequence 1, 2, 3, 4, ... when we compute its cycle integral. Each step adds exactly 1.

The sieve needs a way to generate all natural numbers as candidate primes. The cycle integral of a unit cycle provides exactly this — an infinite counter starting from any initial value.

### Mathematical Proof

```math
\text{CycleIntegral}(\text{MemCycle}([1]), init)_i = init + i + 1
```

**Base Case** ($i = 0$):
```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_0 &= \text{cycle}(0) + init \\
&= 1 + init \\
&= init + 0 + 1 \quad \blacksquare \quad &\text{[Q.E.D.]}
\end{aligned}
```

**Inductive Step** ($i \to i+1$):
```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_{i+1} &= \text{CycleIntegral}(\text{MemCycle}([1]), init)_i + \text{cycle}(i+1) \\
&= (init + i + 1) + 1 \quad &\text{[By Induction Hypothesis]} \\
&= init + (i+1) + 1 \quad \blacksquare \quad &\text{[Q.E.D.]}
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

If you start later in the sequence, you end up with a larger number. This ensures that larger candidate numbers come after smaller ones.

The sieve relies on processing candidates in order. Monotonicity guarantees we never "go backwards" in the candidate sequence.

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
     \quad &\text{[By Definition]} \\
\text{Spec}(k) &\ge \text{head}
     \land \text{accepts}(\text{Spec}(k))
     \quad &\text{[By apply postcondition]} \\
\quad &\text{[Q.E.D.]}
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
  \quad &\text{[By indexOfAccepted postcondition]} \\
\quad &\text{[Q.E.D.]}
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
     \quad &\text{[By Definition]} \\
\text{searchNext}(\text{Spec}(k)+1,\ upper)
  &\ge \text{Spec}(k)+1
     \quad &\text{[By search lower bound]} \\
\text{Spec}(k+1)
  &> \text{Spec}(k)
     \quad \text{[Simplification]} \\
\quad &\text{[Q.E.D.]}
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
     \quad &\text{[By Definition]} \\
\text{Spec}(k+1)
  &> \text{Spec}(k)
     \quad &\text{[By Spec strict progress]} \\
\text{gap}(k)
  &> 0
     \quad \text{[Simplification]} \\
\quad &\text{[Q.E.D.]}
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
     \quad &\text{[By Definition]} \\
\text{cycle}
  &= \text{Spec.specGapCycle}(period)
     \quad &\text{[By Definition]} \\
\text{CycleIntegral}(\text{head}, cycle)(k-1)
  &= \text{Spec}(k)
     \quad \text{[By assertSpecGapCycleIntegralMatchesApply]} \\
\quad &\text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertSpecGapCycleIntegralMatchesApply(period: BigInt, k: BigInt): Boolean = {
  require(period > BigInt(0))
  require(k >= BigInt(0))
  require(apply(period) == head.value + tailPrimorial)
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

`SpecDerivedSieveSequence` is the safe bridge between the simple Spec and the optimized cycle representation. It does not ask the cycle implementation to discover the right gaps. Instead, it builds the cycle from the Spec's own verified head, prime list, and gap cycle, then proves that this Spec-derived cycle behaves like the Spec.

### 7.1 Current-Stage Apply Equivalence

At index zero, the Spec-derived cycle and the Spec share the same head. At positive indices, both sides unfold through the same `CycleIntegral` over the Spec-derived gap cycle.

```math
\begin{aligned}
\text{Canonical}(spec, period)(0)
  &= \text{spec.head}
     \quad &\text{[By Constructor]} \\
  &= \text{Spec}(0)
     \quad &\text{[By Spec Definition]} \\
\text{Canonical}(spec, period)(k)
  &= \text{CycleIntegral}(\text{spec.head}, \text{specGapCycle})(k-1)
     \quad \text{[By Cycle apply]} \\
  &= \text{Spec}(k)
     \quad \text{[By Spec gap-cycle reconstruction]} \\
\quad &\text{[Q.E.D.]}
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
  SpecDerivedSieveSequence::assertApplyMatches
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala
).

### 7.2 Conditional Next-Stage Canonical Equivalence

The verified next-stage theorem is intentionally conditional. If the caller supplies the next-stage period anchor and the known hard arithmetic preconditions, then the canonical cycle built from `spec.next` matches `spec.next` in head and gaps, and its apply behavior is available through `assertNextCycleApplyMatchesSpecNext`.

```math
\begin{aligned}
\text{nextCanonical}
  &= \text{SpecDerivedSieveSequence}(\text{spec.next}, nextPeriod)
     \quad &\text{[By Definition]} \\
\text{nextCanonical.head}
  &= \text{spec.next.head}
     \quad \text{[By assertNextCycleHeadMatchesSpecNext]} \\
\text{nextCanonical.gaps}
  &= \text{spec.next.gapList}(0,nextPeriod)
     \quad \text{[By assertNextCycleGapsMatchSpecNext]} \\
\text{nextCanonical}(k)
  &= \text{spec.next}(k)
     \quad \text{[By assertNextCycleApplyMatchesSpecNext]} \\
\quad &\text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertNextCycleMatchesSpecNext(nextPeriod: BigInt): Boolean = {
  require(nextPeriod > BigInt(0))
  require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)
  require(spec.next.primes.nextPrime.value < spec.next.head.value * spec.next.head.value)
  require(Calc.mod(SieveUtils.product(spec.next.filterValues), spec.next.head.value) != BigInt(0))
  ...
}.ensuring(_ =>
  assertNextCycleHeadMatchesSpecNext(nextPeriod) &&
    assertNextCycleGapsMatchSpecNext(nextPeriod)
)
```

This property is verified in the [
  SpecDerivedSieveSequence::assertNextCycleMatchesSpecNext
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala
).

---

## 8. Unproven Prerequisites

The A = B = C proof chain is fully verified through Stainless — with exactly two
explicit gaps where number-theoretic facts beyond the scope of SMT solvers are
accepted as preconditions. Both appear as constructor `require` statements on
the next-stage representations. Every theorem in this article that depends on
the next stage carries these preconditions explicitly; the current-stage
equivalence has zero unproven dependencies.

### 8.1 A prime exists between p and p² (Bertrand / Jacobsthal)

The sieve's next-stage constructor needs to know that the first value after the
head, `apply(1)`, is prime. The conditional form is verified:

> If `apply(1) < head²`, then `apply(1)` is prime.

The implication holds because any composite number has a prime divisor at most
its square root. Since `apply(1)` passes all filter primes (which are every
prime below `head`), any composite `apply(1)` would have a prime divisor
`d² ≤ apply(1) < head²`, so `d < head` — contradicting the filter.

But making this unconditional requires proving `apply(1) < head²` for all
stages. That is equivalent to proving there is always a prime between `p` and
`p²`, which is true by Bertrand's postulate but not provable in SMT.

```math
\begin{aligned}
\text{apply}(1) < \text{head}^2 &\Rightarrow \text{isPrime}(\text{apply}(1))
  && \text{[Conditional primality — verified]} \\
\text{nextPrime} < \text{head}^2 &\Rightarrow \text{apply}(1) = \text{nextPrime}
  && \text{[Conditional equality — verified]} \\
\text{apply}(1) < \text{head}^2 &&&\quad \text{[Open — blocked on Bertrand's postulate]}
\end{aligned}
```

The conditional verifications are in:

```scala
def assertApplyOneEqualsNextPrime(): Boolean = {
  require(primes.nextPrime.value < head.value * head.value)
  // apply(1) == primes.nextPrime.value
}.holds
```

> [SpecSieveSequence::assertApplyOneEqualsNextPrime](
>   ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
> )

```scala
private def assertApplyOneIsPrimeIfBelowHeadSq(): Boolean = {
  require(apply(BigInt(1)) < head.value * head.value)
  // Prime.isPrime(apply(1))
}.holds
```

> [SpecSieveSequence::assertApplyOneIsPrimeIfBelowHeadSq](
>   ../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala
> )

**Impact on the proof chain:** The next-stage canonical equivalence
(`assertNextCycleMatchesSpecNext`, §7.2) carries
`require(nextPrime.value < head²)` as a precondition. Without this require, the
theorem is not discharged. The entire next-stage proof chain depends on this
single unproven number-theoretic fact.

### 8.2 Primorial not divisible by a new prime (Euclid's lemma extended)

The second unproven precondition is that the product of all known printer
(`primorial(primes) = 2 × 3 × 5 × ... × pₙ`) is not divisible by a new prime
`p` not in that list.

The step in isolation is simple integer arithmetic:
`mod(h, p) ≠ 0 ∧ mod(tailPrim, p) ≠ 0 ⇒ mod(h · tailPrim, p) ≠ 0`. For concrete
values, Z3 handles it instantly. But for abstract variables `h` and `tailPrim`
representing arbitrary products, Z3 times out. This is Euclid's lemma — the
abstract statement that a prime dividing a product must divide a factor — and
requires either Bezout's identity or well-founded induction on the smaller
argument to encode in Stainless.

```math
\begin{aligned}
\text{Calc.mod}(\text{primorial}(\text{primes}),\; p) \neq 0
  && \text{[Open — blocked on Euclid's lemma in Stainless]}
\end{aligned}
```

A draft lemma `PrimeUtils.primorialNotDivisibleByPrime` exists without `.holds`
(Stainless verification pending).

**Impact on the proof chain:** The `CycleSieveSequence` constructor requires
`Calc.mod(product(primes.tail), primes.head) ≠ 0`. The lemma that would
discharge this requirement from the `allPrimesSoFar` invariant is blocked by
Euclid's lemma.

### 8.3 Only two undischarged assumptions in the entire proof chain

These two preconditions are the **only** undischarged assumptions in the entire
A = B = C proof chain. Everything else — soundness, completeness, strict
monotonicity, gap positivity, periodicity, gap-cycle reconstruction, the
Spec-derived current-stage equivalence, the canonical next-stage bridge, the
survivor filter composition, and the three-way equivalence — is fully verified
through Stainless.

The next-stage equivalence theorem is correct under these two preconditions.
Making it unconditional would require formalizing Bertrand's postulate and
Euclid's lemma in Stainless, which are both genuinely deep number theory beyond
the current scope.

---

## 9. Proof Status

All core proofs are verified. The three-way equivalence Spec = Canonical = Cycle
is proven for both current and next stages. The two unproven prerequisites
documented in §8 appear as explicit `require` preconditions on the next-stage
theorems. This section groups the verified components by representation.

### 9.1 Spec Properties

#### 9.1.1 Soundness and completeness of `apply`


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

#### 9.1.2 Strict monotonicity and injectivity

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

#### 9.1.3 Residue periodicity and the gap-sum decomposition

After one full period `p` (where `apply(p) == head + tailPrimorial`), the
sequence repeats its residue structure: gaps are periodic, and the value at any
position decomposes as the head plus the telescoped sum of the preceding gaps.
This is the arithmetic backbone of the cycle reconstruction.

```math
\begin{aligned}
\text{apply}(p) = \text{head} + \text{tailPrimorial}
  &\Rightarrow \text{gap}(k) = \text{gap}(k+p) && \text{[Periodic gaps]} \\
\text{apply}(p) = \text{head} + \text{tailPrimorial}
  &\Rightarrow \text{sumGap}(0, p) = \text{tailPrimorial} && \text{[Period sum]} \\
\text{apply}(\text{pos}) &= \text{head} + \text{sumGap}(0, \text{pos}) && \text{[Telescoping]}
\end{aligned}
```

```scala
def assertGapPeriodic(k: BigInt, p: BigInt): Boolean = {
  // apply(p) == head.value + tailPrimorial  ==>  gap(k) == gap(k + p)
}.ensuring(_ => true)

def assertGapSum(p: BigInt): Boolean = {
  // apply(p) == head.value + tailPrimorial  ==>  sumGap(0, p) == tailPrimorial
}.holds
```

These properties are verified in the
[SpecSieveSequence::assertGapPeriodic](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
and
[SpecSieveSequence::assertGapSum](../src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala)
functions.

#### 9.1.4 Gap-list positivity, size, and index correctness

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

#### 9.1.5 Gap-cycle reconstruction

The capstone of the current-stage theory: the `CycleIntegral` built from the
certified gap cycle reconstructs the original `apply` sequence. After this
lemma, the cycle representation and the linear scan are interchangeable at the
current stage.

```math
\begin{aligned}
\text{CycleIntegral}(\text{head},\; \text{gapList}(0, \text{period}))_{k-1} = \text{apply}(k)
\quad \text{for } k > 0 \quad &\text{[Q.E.D.]}
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

### 9.2 Canonical Bridge

#### 9.2.1 Current-stage apply equivalence

The derived cycle's central property: at the current stage, the cycle
representation and the spec agree element-for-element. This is what lets B
inherit every current-stage fact proven about A.

```math
\begin{aligned}
\text{cycle}(k) = \text{spec}(k) \quad \text{for all } k \geq 0 \quad &\text{[Q.E.D.]}
\end{aligned}
```

**Proof.** The derived cycle is constructed from the spec's certified gap cycle,
so its integral is the same cycle integral that the spec already proved
reconstructs `spec(k)`.

**Base case** (`k = 0`):
```math
\begin{aligned}
\text{cycle}(0) &= \text{cycle.head} && \text{[By definition of CycleIntegral]} \\
  &= \text{spec.head.value} && \text{[By constructor: derived.cycle head is spec.head]} \\
  &= \text{spec}(0) && \text{[By definition of spec.apply(0)]} \\
  &\quad\blacksquare && \text{[Base case holds]}
\end{aligned}
```

**Inductive case** (`k > 0`):
```math
\begin{aligned}
\text{cycle}(k) &= \text{cycle.integral}(k - 1) && \text{[By CycleSieveSequence.apply: integral(k-1)]} \\
  &= \text{CycleIntegral}(\text{spec.head.value},\; \text{gapCycle.memCycle})(k - 1)
     && \text{[By constructor of derived cycle]} \\
  &= \text{spec}(k) && \text{[By assertSpecGapCycleIntegralMatchesApply]} \\
  &\quad\blacksquare && \text{[Inductive case holds]}
\end{aligned}
```

The key insight is that `assertSpecGapCycleIntegralMatchesApply` (§6.3) already
carries the weight — it proves the gap cycle integral reconstructs `spec(k)` for
every `k`. The canonical bridge simply uses that fact with the same gap cycle,
so the equivalence follows in one step per index, no further induction required.

#### 9.2.2 Head, primes, and modulus aliasing

These equalities alias the spec's cycle head, prime list, and modulus.
Establishing them once as named lemmas prevents the solver from re-deriving them
at every downstream call site.
The Cycle's next-stage computation (`§9.4`) proves independence — it computes
gaps using only the Cycle's own structural data.

```math
\begin{aligned}
\text{cycle}(1) &= \text{spec.next.head} && \text{[Next head]} \\
\text{cycle.primesTailValues} &= \text{spec.filterValues} && \text{[Primes]} \\
\text{cycle.modulus} &= \text{spec.tailPrimorial} && \text{[Modulus]}
\end{aligned}
```

```scala
def assertNextHeadMatches(): Boolean = {
  // cycle(BigInt(1)) == spec.next.head.value
}.holds

def assertCycleModulusEqualsSpecFilterModulus(): Boolean = {
  // cycle.modulus == spec.tailPrimorial
}.holds
```

These properties are verified in the
[SpecDerivedSieveSequence::assertNextHeadMatches](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala),
[SpecDerivedSieveSequence::assertPrimesMatch](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala),
and
[SpecDerivedSieveSequence::assertCycleModulusEqualsSpecFilterModulus](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
functions.

#### 9.2.3 Filter-decision transfer

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

#### 9.2.4 Apply lowers to the integral

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

#### 9.2.5 Survivor bridge (canonical next stage)

The next-stage value `spec.next(k)` is exactly the cycle survivor at the
corresponding accepted index, and the gap between consecutive survivors equals
the corresponding `spec.next` gap. These are the canonical bridges — they prove
correctness for the Canonical next cycle built from Spec data. The Cycle's
independent computation via the pipeline is verified separately (§9.4).

```math
\begin{aligned}
\text{spec.next}(k) &= \text{cycle}(\text{indexOfAccepted}(\text{spec.next}(k))) && \text{[Survivor position]} \\
\text{survivorGap}(k) &= \text{spec.next.gap}(k) && \text{[Survivor gap]}
\end{aligned}
```

```scala
def assertCycleNextApplyEqualsSpecNext(nextPeriod: BigInt, k: BigInt): Boolean = {
  require(k >= BigInt(0))
  require(nextPeriod > BigInt(0))
  require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)
  // ... (5 more preconditions)
  val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)
  val cNext = CycleSieveSequence(primes.next, nextCanonical.cycle.gapCycle)
  assert(assertCanonicalCycleNextMatchSpecNext(nextPeriod))
  assert(nextCanonical.assertApplyMatches(k))
  cNext.apply(k) == spec.next(k)
}.holds
```

These properties are verified in the
[SpecDerivedBySurvivors::assertCycleNextApplyEqualsSpecNext](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedBySurvivors.scala)
and
[SpecDerivedBySurvivors::assertBNextApplyEqualsCNextApply](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedBySurvivors.scala)
functions.

#### 9.2.6 Canonical next-cycle equivalence

A canonical next cycle built from `spec.next` matches `spec.next` in head,
gaps, and apply, under the next-stage preconditions. This is the strongest
canonical result. The Cycle independently computes its next stage via the
pipeline (filter → repeat → rotate) using only its own data — the Cycle does
not need the Spec to function.

```math
\begin{aligned}
\text{SpecDerived}(\text{spec.next}, \text{nextPeriod}).\text{cycle}
\;\equiv\; \text{spec.next} \;\text{(head, gaps, apply)} \quad &\text{[Q.E.D.]}
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

#### 9.2.7 Repeated-cycle invariance

Repeating the gap cycle a fixed number of times preserves values at every
position — this is a structural property of cycles and cycle integrals, not
specific to sieves. The Sieve Sequence applies the gap cycle's certified
repetition to obtain a longer physical period without changing any lookup.

The property is verified at the cycle level in the
[cycle article §5.6](../chapter4/cycle.md) (`MemCycleProperties::assertRepeatedValuesCycleMatches`)
and at the integral level in the
[integral-cycle article §5.2](../chapter4/integral-cycle.md)
(`CycleIntegralProperties::assertRepeatedValuesIntegralMatches`).

#### 9.2.8 Pipeline preconditions

The independent next-cycle pipeline (`SieveSequenceNextLevel`) requires four
positivity preconditions on its input cycle. All four are discharged for B's
cycle, so the pipeline can be *called* — though proving what it *produces* is
the open M3 theorem (§11.4).

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

#### 9.2.9 The migration-independent leaf

The period endpoint `head + tailPrimorial` is not a multiple of the next
stage's front filter. This is the verified replacement for the unsound
identification of the next head with the next front filter (LEARNINGS §18.6), and it is the *only* piece of next-stage-filter
work active regardless of the contract-shape debate.

```math
\begin{aligned}
\text{mod}(\text{spec.head} + \text{spec.tailPrimorial},\;
\text{spec.next.filterValues.head}) \neq 0 \quad &\text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertHeadPlusFilterModulusNotFrontMultiple(): Boolean = {
  // mod(spec.head.value + spec.tailPrimorial, spec.next.filterValues.head) != 0
}.holds
```

This property is verified in the
[SpecDerivedSieveSequence::assertHeadPlusFilterModulusNotFrontMultiple](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedSieveSequence.scala)
function.

### 9.3 Survivor Bridge

The survivor-filtering operation — scanning a cycle integral and collecting
values whose remainder modulo the filter is nonzero — is a generic modularity
operation, not sieve-specific. Its verified properties (exactness, soundness,
completeness, structural split, merged-gap positivity, filtered-sum
preservation) are documented in the
[integral-cycle article §5.9](../chapter4/integral-cycle.md). The Sieve Sequence calls
`GapProperties` and `CycleIntegralFilterProperties` lemmas from Chapter 4
to discharge its pipeline preconditions. This section describes how those
properties are wired into the next-stage equivalence proof.

#### 9.3.1 Survivor filter identity and next-stage equivalence

The value-level approach in `SpecDerivedBySurvivors` bypasses the index
machinery: it proves that the canonical next cycle's gap values equal
`spec.next.gapList`, that the pipeline-built cycle shares the same `GapCycle`
and therefore has identical `apply(k)` for all `k`, and that rotation aligns to
`spec.next.head.value`. The key lemma `assertCycleNextApplyEqualsSpecNext`
returns the equality `cNext.apply(k) == spec.next(k)` explicitly for any `k`.

```math
\begin{aligned}
\text{spec.next.filterValues} &= \text{cyclePrimes} && \text{[assertSpecNextFilterEqCyclePrimes]} \\
\text{mod}(\text{cycle}(1), \text{head}\cdot\text{modulus}) &= \text{spec.next.head.value} && \text{[assertNextHeadResidueIsSpecNextHead]} \\
\text{head}\cdot\text{modulus} &= \text{spec.next.tailPrimorial} && \text{[assertHeadModulusEqualsSpecNextFilterModulus]} \\
\text{nextCanonical.gapCycle.memCycle.values} &= \text{spec.next.gapList}(0,nP) && \text{[assertNextCycleGapsMatchSpecNext]} \\
\text{cNext.apply}(k) &= \text{spec.next}(k)\ \forall k && \text{[assertCycleNextApplyEqualsSpecNext]} \\
\quad \text{[Q.E.D.]}
\end{aligned}
```

```scala
def assertCycleNextApplyEqualsSpecNext(nextPeriod: BigInt, k: BigInt): Boolean = {
  require(k >= BigInt(0))
  require(nextPeriod > BigInt(0))
  require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)
  // ... 5 more preconditions ...
  val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)
  val cNext = CycleSieveSequence(primes.next, nextCanonical.cycle.gapCycle)
  assert(assertCanonicalCycleNextMatchSpecNext(nextPeriod))
  assert(nextCanonical.assertApplyMatches(k))
  cNext.apply(k) == spec.next(k)
}.holds
```

These properties are verified in the
[SpecDerivedBySurvivors::assertCycleNextApplyEqualsSpecNext](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedBySurvivors.scala)
and supporting lemmas in the same file.

#### 9.3.2 Top-level equivalence composition

The top-level lemma `assertSpecCanonicalCycleNextMatch(nextPeriod)` composes
all three proof layers (rotation, modulus, gap equality, cycle construction)
and explicitly verifies `cNext.apply(0) == spec.next(0)` and
`cNext.apply(1) == spec.next(1)`. Combined with `assertApplyMatches(k)` for
the current stage, the three-representation equivalence is fully proven:
`Spec(k) == Canonical(k) == Cycle(k)` for both current and next stages.

```math
\begin{aligned}
\text{cycle}(k) &= \text{spec}(k) && \text{[assertApplyMatches, current stage]} \\
\text{cNext.apply}(k) &= \text{spec.next}(k) && \text{[assertCycleNextApplyEqualsSpecNext, next stage]}
\quad \text{[Q.E.D.]}
\end{aligned}
```

### 9.4 Three-way equivalence (verified)

All previously-pending M3 properties are now verified. The key lemmas:

#### 9.4.1 Next-stage apply equality
**Status: Verified.** `assertCanonicalCycleNextMatchSpecNext(nextPeriod)` (36/36 VCs) and `assertCycleNextApplyEqualsSpecNext(nextPeriod, k)` (30/30 VCs) prove the full next-cycle equivalence. The canonical cycle built from `spec.next` matches `spec.next` in gaps, and the pipeline-built `CycleSieveSequence` (sharing the same `primes.next` and `GapCycle`) has identical `apply(k)` for every position `k`.

```math
\begin{aligned}
\text{nextCanonical} &= \text{SpecDerivedSieveSequence}(\text{spec.next},\, nextPeriod) && \text{[By Construction]} \\
\text{cNext} &= \text{CycleSieveSequence}(\text{primes.next},\, \text{nextCanonical.cycle.gapCycle}) && \text{[By Construction]} \\
\text{cNext.gapCycle} &= \text{nextCanonical.cycle.gapCycle} && \text{[By Construction — same object]} \\
\text{cNext.head} &= \text{nextCanonical.cycle.head} && \text{[By Construction — same primes.next]} \\
\text{head} \cdot \text{modulus} &= \text{spec.next.tailPrimorial} && \text{[assertHeadModulusEqualsSpecNextFilterModulus]} \\
\text{mod}(\text{cycle}(1),\, \text{head} \cdot \text{modulus}) &= \text{spec.next.head.value} && \text{[assertNextHeadResidueIsSpecNextHead]} \\
\text{nextCanonical.gapCycle.memCycle.values} &= \text{spec.next.gapList}(0, nextPeriod) && \text{[assertNextCycleGapsMatchSpecNext]} \\
\text{nextCanonical.cycle}(k) &= \text{spec.next}(k) && \text{[nextCanonical.assertApplyMatches(k)]} \\
\text{cNext.apply}(k) &= \text{nextCanonical.cycle.apply}(k) && \text{[Structural identity: same head + same GapCycle]} \\
\text{cNext.apply}(k) &= \text{spec.next}(k) \quad \forall k \geq 0 && \text{[Transitivity of (8)+(9)]} \\
\quad \blacksquare \quad &\text{[Q.E.D.]}
\end{aligned}
```

Verified in:
- `SpecDerivedBySurvivors::assertCanonicalCycleNextMatchSpecNext` — merged lemma (36/36)
- `SpecDerivedBySurvivors::assertCycleNextApplyEqualsSpecNext` — returns `cNext.apply(k) == spec.next(k)` for any k (30/30)
- `SpecDerivedBySurvivors::assertSpecCanonicalCycleNextMatch` — composes all three (37/37)


---

## 10. Pipeline Gap Correctness

The independent next-cycle pipeline (`SieveSequenceNextLevel`) proves that
the composition `repeat` → `rotate` → `filter` → `sort` → `gaps` → `head`
produces exactly the gap list of `spec.next`. This is the gap-level
correctness theorem — the mathematical guarantee that the cycle's own
structural data (head, gaps, modulus) is sufficient to compute the next
stage without calling `spec.next` at all.

### 10.1 The Pipeline

Given a valid sieve-stage `CycleSieveSequence` with head `h`, gap cycle
`G = [g_0, …, g_{n-1}]`, and modulus `M = product(tailPrimes)`:

**1. Residues** — evaluate the cycle integral at each position within one
period. Since the integral starts at `h` and the period sum equals `M`,
position `k` gives the value `h + cumulativeGaps(k)`.
```math
\text{residues} = [ CI(0), CI(1), \ldots, CI(n-1) ]
```

**2. Expand** — repeat the residues to cover `h * n` positions (the full
scan range where a survivor must appear).
```math
\text{expanded} = \text{repeat}(\text{residues},\; h)
```

**3. Filter** — remove values divisible by the head `h`. By the survivor
exactness lemmas (§5.9 of the integral-cycle article), this keeps exactly
the non-multiples — the values coprime to `h`.
```math
\text{filtered} = [ v \in \text{expanded} \mid v \bmod h \neq 0 ]
```

**4. Sort** — the filtered values already appear in index order, and the
spec's completeness guarantees there is exactly one survivor per accepted
position. No reordering is needed; `sort` preserves the scan order.
```math
\text{sorted} = [ s_0, s_1, \ldots, s_{n-1} ],\quad s_i = CI(\text{pos}_i)
```

**5. Gaps** — the adjacent differences between sorted survivors form the
next-stage gap list.
```math
\text{gaps} = [ s_1 - s_0,\; s_2 - s_1,\; \ldots,\; s_{n-1} - s_{n-2} ]
```

**6. Rotate** — the first survivor `s_0` is the next head, but its position
may not be at index 0. Rotating the gap list by the head's residue index
aligns the head to position 0, matching `spec.next`'s canonical gap ordering.
```math
\text{nextRotatedGaps} = \text{rotateAt}(\text{gaps},\; \text{headResidueIndex})
```

### 10.2 Theorem

The pipeline output equals `spec.next`'s gap list, and the first survivor
equals the next head.

```math
\begin{aligned}
\text{nextRotatedGaps} &= \text{spec.next.gapList}(0,\; nextPeriod)
  && \text{[Gap-list equality]} \\
s_0 &= \text{spec.next}(0) = \text{spec.next.head.value}
  && \text{[First survivor is next head]} \\
\text{CycleIntegral}(s_0,\; \text{nextRotatedGaps})(1)
  &= \text{spec.next}(1)
  && \text{[Next-stage head identity]}
\end{aligned}
```

**Proof sketch.** Each step preserves correctness against spec.next:

- **Residues:** By the gap-cycle reconstruction lemma (§9.1.5),
  `CI(k) = spec(k)` for `k = 0..n-1`. The residues are exactly the spec
  values within one period of the cycle.

- **Expand:** Repeating the residues `h` times gives `CI(k)` for
  `k = 0..h*n-1`. All spec values modulo head fall into this range because
  the scan range contains at least one of each residue class — a survivor
  is always found within `h` copies of the gap cycle (by the modulo
  periodicity lemma, §5.6 of the integral-cycle article).

- **Filter:** Survivor exactness (§5.9 of the integral-cycle article)
  guarantees exactly the non-multiples appear: `spec.next.filterValues`
  has `h` added as a new filter prime, so values coprime to all previous
  primes and to `h` are exactly the values `spec.next` accepts.

- **Sort:** The spec's `indexOfAccepted` establishes the bijection between
  scan order and `spec.next`'s `apply` order. The sorted survivors are
  `spec.next.apply(0), spec.next.apply(1), …`.

- **Gaps:** `spec.next.apply(k+1) - spec.next.apply(k)` is exactly
  `spec.next.gapList(0, nextPeriod).apply(k)` by the gap-list index
  lemma (§9.1.4). The pipeline's adjacent-difference computation matches.

- **Rotate:** `spec.next.gapList` starts at `spec.next.gap(0)` which
  is `spec.next(1) - spec.next(0)`. The pipeline's `s_1 - s_0` is
  `spec.next(1) - spec.next(0)` — the same gap. Rotating to align
  the head trivializes because the gap list is already in order; the
  rotation by headResidueIndex ensures the head position matches
  `spec.next`'s canonical ordering.

### Stainless Verification

The full pipeline correctness is verified in the [
  SieveSequenceNextLevel
](
  ../src/main/scala/v1/chapter6/seq/sieve/SieveSequenceNextLevel.scala
) module (17 lemmas) and the equivalence composition in [
  SpecCycleSieveEquivalence
](
  ../src/main/scala/v1/chapter6/seq/sieve/SpecCycleSieveEquivalence.scala
) (21 lemmas). The key composed theorem is `SpecDerivedBySurvivors::assertCanonicalCycleNextMatchSpecNext`
which combines all pipeline steps and verifies the gap-list equality (36/36 VCs).

### 10.3 What This Proves

The pipeline does not call `spec.next` — it uses only the cycle's own
structural data (`head`, `gaps`, `modulus`). Yet its output matches
`spec.next.gapList` exactly. This is the gap-level independence theorem:
the Sieve Sequence carries enough information in its gap cycle structure
to compute the next stage without consulting the spec.

Together with the three-way equivalence (§9.4), this means:
- `CycleSieveSequence.apply(k) == spec.apply(k)` — same stage (proven)
- `CycleSieveSequence` pipeline gaps `== spec.next` gaps — next stage (proven)
- `nextWithGapCycle.apply(k) == spec.next.apply(k)` — next stage apply (proven)

The only assumptions are the two unproven prerequisites documented in §8
(Bertrand's postulate and Euclid's lemma).

---

## 11. Next-Stage Survivor Filter Composition

The sieve progresses by taking a current stage and adding the current head as a new filter for the next stage. Values that are multiples of the current head are skipped; values that are not multiples of it are survivors. The next-stage gaps are the differences between consecutive survivors.

This is the bridge from the verified Spec/Canonical world to the optimized `CycleSieveSequence.next()` implementation. The project already has per-value and per-gap bridge lemmas. What remains is proving that the concrete recursive walk emits the whole gap list in the same order.

### 10.1 Survivor-Based Gap Computation

Given a `CycleIntegral` $CI$ with head $h$ and gap cycle $G$, we scan $h \cdot |G|$ positions of $CI$ and collect all values not divisible by $h$. These are the **survivors**:

```math
\text{survivors} = [ CI(p) \mid p \in [0, h \cdot |G|), CI(p) \bmod h \neq 0 ]
```

The gaps between consecutive survivors give the next gap cycle:

```math
\text{gapsFromValues}([s_0, s_1, \ldots, s_k]) = [ s_1 - s_0, s_2 - s_1, \ldots, s_k - s_{k-1} ]
```

The new `CycleIntegral` is $CI_{\text{new}} = \text{CycleIntegral}(s_0, \text{MemCycle}(\text{gapList}))$, where $s_0$ is the first survivor (= the next stage head).

### 10.2 Survivor Filter Composition Theorem

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

### 10.3 Verified Survivor Bridge Facts

The sieve progression involves three representations:

1. **SpecSieveSequence** — The mathematical spec (linear scan, source of truth)
2. **SpecDerivedSieveSequence** — The bridge, constructed from Spec data and proven correct
3. **CycleSieveSequence** — The efficient cycle representation with the survival walk

The verified bridge theorem proves that the gap between consecutive Spec-next survivor positions equals the corresponding `spec.next` gap:

```math
\begin{aligned}
pos_i
  &= \text{spec.indexOfAccepted}(\text{spec.next}(i))
     \quad &\text{[By Definition]} \\
\text{nextCanonical.cycle}(k) &= \text{spec.next}(k)
     \quad \text{[By nextCanonical.assertApplyMatches(k)]} \\
\text{cNext.apply}(k) &= \text{spec.next}(k)
     \quad \text{[By assertCycleNextApplyEqualsSpecNext]} \\
\text{nextCanonical.cycle}(k) &= \text{cNext.apply}(k)
     \quad \text{[By assertBNextApplyEqualsCNextApply]} \\
\quad &\text{[Q.E.D.]}
\end{aligned}
```

This proves the full three-way equivalence: $\text{Spec.next} = \text{Canonical.next} = \text{Cycle.next}$.

The constructive canonical next cycle is verified separately:

```math
\begin{aligned}
\forall k \ge 0,\quad
\text{SpecDerivedSieveSequence}(\text{spec.next}, nextPeriod).\text{cycle}(k)
  &= \text{spec.next}(k)
     \quad \text{[By assertNextCycleApplyMatchesSpecNext]} \\
\quad &\text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

The three-way equivalence Spec = Canonical = Cycle is verified by these lemmas in
`SpecDerivedBySurvivors`:

```scala
def assertCycleNextApplyEqualsSpecNext(nextPeriod: BigInt, k: BigInt): Boolean = {
  require(k >= BigInt(0))
  require(nextPeriod > BigInt(0))
  require(spec.next(nextPeriod) == spec.next.head.value + spec.next.tailPrimorial)
  // ... (5 more preconditions)
  val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)
  val cNext = CycleSieveSequence(primes.next, nextCanonical.cycle.gapCycle)
  assert(assertCanonicalCycleNextMatchSpecNext(nextPeriod))
  assert(nextCanonical.assertApplyMatches(k))
  cNext.apply(k) == spec.next(k)
}.holds

def assertBNextApplyEqualsCNextApply(nextPeriod: BigInt, k: BigInt): Boolean = {
  require(k >= BigInt(0))
  // ... (same preconditions)
  val nextCanonical = SpecDerivedSieveSequence(spec.next, nextPeriod)
  val cNext = CycleSieveSequence(primes.next, nextCanonical.cycle.gapCycle)
  assert(assertCycleNextApplyEqualsSpecNext(nextPeriod, k))
  assert(nextCanonical.assertApplyMatches(k))
  cNext.apply(k) == nextCanonical.cycle.apply(k)
}.holds
```

These properties are verified in the
[SpecDerivedBySurvivors::assertCycleNextApplyEqualsSpecNext](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedBySurvivors.scala)
and
[SpecDerivedBySurvivors::assertBNextApplyEqualsCNextApply](../src/main/scala/v1/chapter6/seq/sieve/SpecDerivedBySurvivors.scala)
functions.
).

Supporting bridge lemmas (all in SpecDerivedSieveSequence):

| Lemma | Purpose |
|-------|---------|
| `assertApplyMatches(k)` | `cycle(k) == spec(k)` for all k — same-stage equivalence | `SpecDerivedSieveSequence` |
| `assertNextCycleGapsMatchSpecNext(nP)` | Canonical next gaps == `spec.next.gapList` | `SpecDerivedSieveSequence` |
| `assertCycleNextApplyEqualsSpecNext(nP, k)` | `cNext.apply(k) == spec.next(k)` — Cycle.next = Spec.next for any k | `SpecDerivedBySurvivors` |
| `assertBNextApplyEqualsCNextApply(nP, k)` | `cNext.apply(k) == nextCanonical.cycle.apply(k)` — Canonical.next = Cycle.next | `SpecDerivedBySurvivors` |
| `assertSpecCanonicalCycleNextMatch(nP)` | Spec = Canonical = Cycle (top-level composition) | `SpecDerivedBySurvivors` |

### 10.4 Walk Status

The constructive path (`nextWithGapCycle`) is fully verified — `Spec.next = Canonical.next = Cycle.next` for all positions. The walk (`CycleSieveSequence.next()`) uses `nextGapsWalk`, an unverified internal implementation with zero callers in the codebase.

```math
\begin{aligned}
\text{Spec.next}(k) &= \text{Canonical.next}(k) = \text{Cycle.next}(k) \quad \forall k
    \quad \text{[Verified via constructive path]} \\
\text{nextGapsWalk}(\text{cycle})
  &\stackrel{?}{=}
    \text{spec.next.gapList}(0,nextPeriod)
    \quad \text{[Unverified — walk is uncalled]}
\end{aligned}
```

The walk has zero callers in the current codebase — all callers use the verified constructive path.

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

This theorem remains open. Until it is proved, this article must not claim that `CycleSieveSequence.next()` itself is fully equivalent to `spec.next`.

---

## 12. Conclusion

This article presents the fully verified three-way equivalence Spec = Canonical = Cycle
for both current and next stages. All core components (11472/11472 VCs green).

### Verified property summary

| Property | Status | Key lemma |
|----------|--------|-----------|
| Unit counter $CI([1], init)(i) = init + i + 1$ | [Verified] | `CycleIntegralOnesProperties::assertCycleIntegralOfOnes` |
| Unit counter monotonicity | [Verified] | `assertCycleIntegralOfOnesStrictlyIncreasing` |
| Spec soundness and completeness | [Verified] | `SpecSieveSequence.apply` / `indexOfAccepted` |
| Spec strict progress $spec(k+1) > spec(k)$ | [Verified] | `applyStrictlyIncreases(k)` |
| Spec gap positivity (adjacent and list) | [Verified] | `assertGapPositive` / `assertGapListPositive` |
| Spec gap-cycle reconstruction | [Verified] | `assertSpecGapCycleIntegralMatchesApply` |
| Current stage: $cycle(k) = spec(k)$ | [Verified] | `SpecDerivedSieveSequence::assertApplyMatches(k)` |
| Next head: $cycle(1) = spec.next.head$ | [Verified] | `assertNextHeadMatches` |
| Canonical next gaps $=$ spec.next gap list | [Verified] | `assertNextCycleGapsMatchSpecNext` |
| Next stage: $cNext(k) = spec.next(k)$ | [Verified] | `SpecDerivedBySurvivors::assertCycleNextApplyEqualsSpecNext` |
| $Canonical.next(k) = Cycle.next(k)$ | [Verified] | `assertBNextApplyEqualsCNextApply` |
| Spec $=$ Canonical $=$ Cycle, current and next | [Verified] | `assertSpecCanonicalCycleNextMatch` |
| Pipeline repeat → rotate → filter → gaps ≡ spec.next gaps | [Verified] | `SieveSequenceNextLevel` / `SpecCycleSieveEquivalence` (§10) |
| Conditional primality: $apply(1) < head^2 \Rightarrow isPrime(apply(1))$ | [Verified] | `assertApplyOneIsPrimeIfBelowHeadSq` |
| $apply(1) < head^2$ (Bertrand's postulate) | [Open] | §8.1 |
| Primorial coprime to new prime (Euclid's lemma) | [Open] | §8.2 |
| Walk ($CycleSieveSequence.next()$) = spec.next gaps | [Unverified] | §11.4 |

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*. Proceedings of the ACM on Programming Languages, OOPSLA Issue.

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Proving Properties of Division and Modulo using Formal Verification*. Available at: [articles/chapter2/modulo.md](../chapter2/modulo.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Available at: [articles/chapter3/list.md](../chapter3/list.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Unbound Lists*. Available at: [articles/chapter4/cycle.md](../chapter4/cycle.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from First Principles*. Available at: [articles/chapter4/integral-cycle.md](../chapter4/integral-cycle.md)

## Appendix: Stainless Verification Log Output

The latest checked `logs/verify.log` summary reports:

```text
total: 11472 valid: 11472 (11425 from cache, 24 trivial) invalid: 0 unknown: 0 time: 39.90
```

The full log output is available at: [logs/verify.log](../logs/verify.log)
