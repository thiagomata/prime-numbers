# Formal Verification of Sieve Foundation Properties from First Principles

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<div align="justify">
<p style="text-align: justify">
This article establishes the foundational lemmas for the sieve sequence algorithm,
proving that CycleIntegral with unit cycle produces natural numbers and that filtering
out multiples of a prime preserves all primes. These properties decompose the complex
sieve algorithm into simpler, verifiable components.
We formally define and verify five key properties using the Stainless verification system:
the unit cycle generates consecutive integers, strict monotonicity holds for the unit cycle,
distinct primes are coprime, filtering by one prime preserves other primes, and the
filtered list contains all original primes.
All properties are expressed and proved within a minimal framework using only
elementary arithmetic, recursion, and pure Scala code.
This work bridges the gap between the sieve algorithm and its formal verification,
offering a self-contained, verifiable approach to prime sieving correctness.
</p>
</div>

## 1. Introduction

The Sieve of Eratosthenes generates prime numbers by iteratively filtering
a sequence of natural numbers. At each step, we remove all multiples of the
current smallest element (which is prime). While the algorithm is elegant and
efficient, proving its correctness requires establishing that:

1. The candidate generation mechanism produces all natural numbers
2. The filtering mechanism preserves all primes

In this article, we formalize these two properties using
[Scala Stainless](https://epfl-lara.github.io/stainless/intro.html) [[1]](#ref1),
a verification framework for pure Scala programs. Our approach follows the
zero-prior-knowledge methodology established in earlier articles:
modular arithmetic [[2]](#ref2), lists [[3]](#ref3), cycles [[4]](#ref4),
and cycle integrals [[5]](#ref5) are all defined from scratch and verified independently.

The result is a machine-checked proof of the sieve's foundational properties — 4837 verification conditions
all valid — that serves as a foundation for the complete sieve correctness proof.

## 2. Preliminaries

We reuse several basic operations and their verified properties from companion articles:

- **Modular Arithmetic** [[2]](#ref2): Division, modulo, quotient invariance, mod idempotence
- **Lists** [[3]](#ref3): Size, append, sum, slicing, tail shift
- **Cycles** [[4]](#ref4): Unbounded repeating sequences
- **Cycle Integrals** [[5]](#ref5): Cumulative sums of cycles
- **Prime Utilities** (defined in the project): Primality testing, filtering

These articles also defined and verified their properties using the same zero-prior-knowledge
methodology, and are treated here as foundational primitives.

### 2.1 Key Definitions

Let $L = [l_0, l_1, \dots, l_{n-1}] \in \mathbb{N}^n$ be a non-empty list.

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

## 3. Proof Strategy

The sieve's correctness requires establishing two foundational properties:

1. **Candidate Generation**: The unit cycle `[1]` generates consecutive natural numbers
2. **Prime Preservation**: Filtering by a prime preserves all other primes

### 3.1 Property 1: Unit Cycle Generates Natural Numbers

The first property establishes that a cycle integral with unit cycle produces
consecutive integers:

```math
\text{CycleIntegral}(\text{MemCycle}([1]), init)_i = init + i + 1
```

**Intuition:** Each step adds exactly 1, so we get consecutive integers starting from `init + 1`.

**Why This Matters:** The sieve uses `nextCandidates` to generate all natural numbers from 2 onward. This lemma proves that the cycle integral mechanism correctly implements this counter.

#### Mathematical Proof

**Base Case** ($i = 0$):
```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_0 &= \text{cycle}(0) + init \\
&= 1 + init \\
&= init + 0 + 1 \quad \text{[Q.E.D.]}
\end{aligned}
```

**Inductive Step** ($i \to i+1$):
```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_{i+1} &= \text{CycleIntegral}(\text{MemCycle}([1]), init)_i + \text{cycle}(i+1) \\
&= (init + i + 1) + 1 \quad \text{[By Induction Hypothesis]} \\
&= init + (i+1) + 1 \quad \text{[Q.E.D.]}
\end{aligned}
```

#### Stainless Verification

The mathematical proof is formalized in the following Scala code:

```scala
def assertCycleIntegralOfOnes(init: BigInt, pos: BigInt): Boolean = {
  require(pos >= 0)
  require(init >= 0)
  val cycle = MemCycle(stainless.collection.List(BigInt(1)))
  val ci = CycleIntegral(init, cycle)
  decreases(pos)
  if (pos == 0) {
    // Base case: CI(0) = cycle(0) + init = 1 + init
    ci(0) == init + BigInt(1)
  } else {
    // Inductive step: CI(pos) = CI(pos-1) + cycle(pos) = CI(pos-1) + 1
    assert(assertCycleIntegralOfOnes(init, pos - 1))
    ci(pos) == init + pos + BigInt(1)
  }
}.holds
```

This property is verified in the [
  CycleIntegralOnesProperties::assertCycleIntegralOfOnes
](
  ../src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala
).

### 3.2 Property 2: Strict Monotonicity

The second property establishes that the unit cycle is strictly increasing:

```math
b > a \implies \text{CycleIntegral}(\text{MemCycle}([1]), init)_b > \text{CycleIntegral}(\text{MemCycle}([1]), init)_a
```

**Intuition:** If you start later, you end up with a larger number.

**Why This Matters:** This ensures that larger candidate numbers come after smaller ones, which is essential for the sieving process.

#### Mathematical Proof

```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_b - \text{CycleIntegral}(\text{MemCycle}([1]), init)_a &= (init + b + 1) - (init + a + 1) \quad \text{[By Property 1]} \\
&= b - a \\
&> 0 \quad \text{[Since } b > a \text{]} \\
\therefore \text{CycleIntegral}(\text{MemCycle}([1]), init)_b &> \text{CycleIntegral}(\text{MemCycle}([1]), init)_a \quad \text{[Q.E.D.]}
\end{aligned}
```

#### Stainless Verification

```scala
def assertCycleIntegralOfOnesStrictlyIncreasing(init: BigInt, a: BigInt, b: BigInt): Boolean = {
  require(a >= 0)
  require(b > a)
  require(init >= 0)
  val cycle = MemCycle(stainless.collection.List(BigInt(1)))
  val ci = CycleIntegral(init, cycle)
  assert(assertCycleIntegralOfOnes(init, a))
  assert(assertCycleIntegralOfOnes(init, b))
  ci(b) > ci(a)
}.holds
```

This property is verified in the [
  CycleIntegralOnesProperties::assertCycleIntegralOfOnesStrictlyIncreasing
](
  ../src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala
).

### 3.3 Property 3: Distinct Primes Are Coprime

The third property establishes that if $q$ and $p$ are distinct primes, then $p$ does not divide $q$:

```math
\text{isPrime}(q) \land \text{isPrime}(p) \land q \neq p \implies q \bmod p \neq 0
```

**Intuition:** Two different primes share no common factors other than 1.

**Key Insight:** This required a helper lemma because Stainless's SMT solver couldn't automatically connect the abstract `noDivisorInRange` property to concrete prime relationships.

#### Mathematical Proof

**Helper Lemma: noDivisorInRangeImpliesModNonZero**

```math
\forall p, q \in [2, n).\ \text{isPrime}(q) \land p \neq q \implies q \bmod p \neq 0
```

This helper is proved by induction on $n$, establishing the property for all pairs up to $n$.

**Case Analysis:**

**Case 1** ($q > p$):
```math
\begin{aligned}
\text{isPrime}(q) &\implies \text{noDivisorInRange}(q, 2, q) \\
p \in [2, q) &\implies \text{noDivisorInRangeImpliesModNonZero}(q, 2, q, p) \\
&\implies q \bmod p \neq 0 \quad \text{[Q.E.D.]}
\end{aligned}
```

**Case 2** ($q < p$):
```math
\begin{aligned}
q < p &\implies \text{ModSmallDividend.modSmallDividend}(q, p) \\
&\implies q \bmod p = q \\
\text{isPrime}(q) &\implies q > 1 \\
&\implies q \bmod p = q \neq 0 \quad \text{[Q.E.D.]}
\end{aligned}
```

#### Stainless Verification

```scala
def assertPrimeNotDivisibleByDistinctPrime(q: BigInt, p: BigInt): Boolean = {
  require(q >= 2)
  require(p >= 2)
  require(Prime.isPrime(q))
  require(Prime.isPrime(p))
  require(q != p)
  if (q > p) {
    // Case 1: q > p
    // isPrime(q) means noDivisorInRange(q, 2, q)
    // p is in [2, q) since p >= 2 (from require) and p < q (from q > p)
    // By helper lemma: mod(q, p) ≠ 0
    assert(noDivisorInRangeImpliesModNonZero(q, 2, q, p))
    Calc.mod(q, p) != BigInt(0)
  } else {
    // Case 2: q < p
    // mod(q, p) = q when q < p
    // isPrime(q) means q > 1
    // Therefore mod(q, p) = q ≠ 0
    assert(ModSmallDividend.modSmallDividend(q, p))
    Calc.mod(q, p) != BigInt(0)
  }
}.holds
```

This property is verified in the [
  FilterPreservesPrimesProperties::assertPrimeNotDivisibleByDistinctPrime
](
  ../src/main/scala/v1/prime/properties/FilterPreservesPrimesProperties.scala
).

### 3.4 Property 4: Filtering Preserves Other Primes

The fourth property establishes that when filtering a list by a prime $p$, any prime $q \neq p$ is preserved:

```math
\text{isPrime}(q) \land q \neq \text{filterPrime} \implies q \bmod \text{filterPrime} \neq 0
```

**Intuition:** Primes don't divide each other unless they're equal.

**Why This Matters:** This is the core of the sieve: we remove multiples of small primes but keep all primes themselves.

#### Mathematical Proof

This follows directly from Property 3:
```math
\begin{aligned}
\text{isPrime}(q) \land \text{isPrime}(\text{filterPrime}) \land q \neq \text{filterPrime} &\implies q \bmod \text{filterPrime} \neq 0 \quad \text{[By Property 3]}
\end{aligned}
```

#### Stainless Verification

```scala
def assertFilterPreservesAllPrimes(q: BigInt, filterPrime: BigInt): Boolean = {
  require(q >= 2)
  require(filterPrime >= 2)
  require(Prime.isPrime(q))
  require(Prime.isPrime(filterPrime))
  require(q != filterPrime)
  // Direct application of Lemma 3
  assert(assertPrimeNotDivisibleByDistinctPrime(q, filterPrime))
  Calc.mod(q, filterPrime) != BigInt(0)
}.holds
```

This property is verified in the [
  FilterPreservesPrimesProperties::assertFilterPreservesAllPrimes
](
  ../src/main/scala/v1/prime/properties/FilterPreservesPrimesProperties.scala
).

### 3.5 Property 5: Filtered List Contains All Primes

The fifth property establishes that if a prime $q$ is in the original list and $q \neq \text{filterPrime}$, then $q$ is in the filtered list:

```math
q \in \text{originalPrimes} \land \text{isPrime}(q) \land q \neq \text{filterPrime} \implies q \in \text{filteredPrimes}
```

**Intuition:** The filter only removes non-primes and multiples of the filter prime. All other primes survive.

**Why This Matters:** This proves the sieve is sound: we never lose primes we need to keep.

#### Mathematical Proof

**Proof by Induction on List Structure:**

**Base Case** (empty list):
```math
\begin{aligned}
\text{originalPrimes} = [] &\implies q \notin \text{originalPrimes} \quad \text{[Contradiction with premise]}
\end{aligned}
```

**Inductive Step** ($\text{originalPrimes} = \text{head} :: \text{tail}$):

**Case 1** ($\text{head} = q$):
```math
\begin{aligned}
\text{head} = q &\implies \text{isPrime}(q) \land q \neq \text{filterPrime} \\
&\implies q \bmod \text{filterPrime} \neq 0 \quad \text{[By Property 4]} \\
&\implies \text{filterList keeps } q \\
&\implies q \in \text{filteredPrimes} \quad \text{[Q.E.D.]}
\end{aligned}
```

**Case 2** ($\text{head} \neq q$):
```math
\begin{aligned}
q \in \text{tail} &\implies q \in \text{filterList}(\text{tail}, \text{filterPrime}) \quad \text{[By Induction Hypothesis]} \\
&\implies q \in \text{filteredPrimes} \quad \text{[Q.E.D.]}
\end{aligned}
```

#### Stainless Verification

```scala
def assertFilteredContainsAllPrimes(
  originalPrimes: List[BigInt],
  filterPrime: BigInt,
  q: BigInt
): Boolean = {
  require(filterPrime >= 2)
  require(Prime.isPrime(filterPrime))
  require(q >= 2)
  require(Prime.isPrime(q))
  require(q != filterPrime)
  require(originalPrimes.contains(q))
  decreases(originalPrimes.size)
  if (originalPrimes.isEmpty) {
    // Contradiction: q is in empty list
    false
  } else {
    val filtered = SieveUtils.filterList(originalPrimes, filterPrime)
    if (originalPrimes.head == q) {
      // q is the head of the list
      // By Lemma 4: mod(q, filterPrime) ≠ 0
      // Therefore filterList keeps q
      assert(assertFilterPreservesAllPrimes(q, filterPrime))
      // filterList keeps head when mod(head, filterPrime) ≠ 0
      filtered.contains(q)
    } else {
      // q is in the tail, recurse
      assert(assertFilteredContainsAllPrimes(originalPrimes.tail, filterPrime, q))
      filtered.contains(q)
    }
  }
}.holds
```

This property is verified in the [
  FilterPreservesPrimesProperties::assertFilteredContainsAllPrimes
](
  ../src/main/scala/v1/prime/properties/FilterPreservesPrimesProperties.scala
).

## 4. Conclusion

This article establishes the foundational properties for the sieve sequence algorithm. The main results are:

```math
\begin{aligned}
\text{CycleIntegral}(\text{MemCycle}([1]), init)_i &= init + i + 1 \quad &\text{[Unit Cycle]} \\
b > a &\implies \text{CycleIntegral}(\text{MemCycle}([1]), init)_b > \text{CycleIntegral}(\text{MemCycle}([1]), init)_a \quad &\text{[Strict Monotonicity]} \\
\text{isPrime}(q) \land \text{isPrime}(p) \land q \neq p &\implies q \bmod p \neq 0 \quad &\text{[Distinct Primes Coprime]} \\
\text{isPrime}(q) \land q \neq \text{filterPrime} &\implies q \bmod \text{filterPrime} \neq 0 \quad &\text{[Filter Preserves Primes]} \\
q \in \text{originalPrimes} \land \text{isPrime}(q) \land q \neq \text{filterPrime} &\implies q \in \text{filteredPrimes} \quad &\text{[Filtered Contains All Primes]}
\end{aligned}
```

Together, these properties show that the sieve's candidate generation and filtering mechanisms are correct. The verified definitions provide a reusable foundation for reasoning about prime sieving using finite list structures and machine-checked Scala code.

## 5. Future Work

Future work may include:
- Connecting these abstract proofs to the complete `SieveSequenceV2` verification
- Extending to handle edge cases (e.g., empty lists, single elements)
- Proving the full sieve algorithm correctness by composing these lemmas
- Applications to prime number distribution analysis

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2025). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2025). *Proving Properties of Division and Modulo using Formal Verification*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2025). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2025). *Using Formal Verification to Prove Properties of Unbound Lists*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2025). *Formal Verification of Cycle Integral Properties from First Principles*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/integral-cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/integral-cycle.md)