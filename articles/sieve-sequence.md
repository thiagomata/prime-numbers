# Formal Verification of Sieve Sequence Properties from First Principles

**Author:** Mata, T. H.  
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

<div align="justify">
<p style="text-align: justify">
This article presents a formal verification of Sieve Sequences — the core data structure used by the Sieve of Eratosthenes to generate candidate primes. We build on a zero-prior-knowledge foundation established in earlier articles (modulo, lists, cycles, cycle integrals) and verify five key properties: (1) the unit cycle generates consecutive natural numbers, (2) strict monotonicity holds, (3) distinct primes are coprime, (4) filtering by a prime preserves all other primes, and (5) every sieve sequence head is prime. Each described property is expressed as a `.holds` function in the Stainless verification system and linked to its verification source.
</p>
</div>

---

## 1. Introduction

The Sieve of Eratosthenes generates prime numbers by iteratively filtering a sequence of natural numbers. At each step, we remove all multiples of the current smallest element (which is prime). Proving its correctness requires establishing:

1. **Candidate generation** — the sequence contains all natural numbers (or all numbers coprime to a given modulus)
2. **Filter preservation** — filtering by one prime does not remove other primes
3. **Head primality** — the first element of each sieve sequence is guaranteed to be prime

In this article, we formalize all three properties using [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html), a verification framework for pure Scala programs. Our approach follows the zero-prior-knowledge methodology established in earlier articles: modular arithmetic, lists, cycles, and cycle integrals are all defined from scratch and verified independently.

The result is a machine-checked proof of the sieve's key properties. The repository-wide verification-condition count is intentionally omitted because it changes as unrelated verified modules are added; the important claim here is that the properties described in this article are verified and source-linked.

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
  ../src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala
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
def assertCycleIntegralOfOnesStrictMonotonic(init: BigInt, a: BigInt, b: BigInt): Boolean = {
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
  CycleIntegralOnesProperties::assertCycleIntegralOfOnesStrictMonotonic
](
  ../src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala
).

---

## 5. Distinct Primes Are Coprime

**Intuition:** Two different primes share no common factors other than 1. This is because any common divisor of two distinct primes would be at least one of them, but neither divides the other.

**Why This Matters:** When filtering by one prime, we must not remove other primes. This lemma establishes that distinct primes are never multiples of each other.

### Mathematical Proof

```math
\text{isPrime}(q) \land \text{isPrime}(p) \land q \neq p \implies q \bmod p \neq 0
```

**Proof by contradiction:** Assume $q \bmod p = 0$ for distinct primes $p$ and $q$. Then $p$ divides $q$. Since $q$ is prime, its only divisors are 1 and $q$. Since $p \neq 1$ (primes are > 1), we must have $p = q$, contradicting $p \neq q$. ∎

### Stainless Verification

```scala
def distinctPrimesCoprime(p: BigInt, q: BigInt): Boolean = {
  require(isPrime(p))
  require(isPrime(q))
  require(p =!= q)
  Calc.mod(q, p) =!= BigInt(0)
}.holds
```

This property is verified in the [
  PrimeProperties::distinctPrimesCoprime
](
  ../src/main/scala/v1/prime/PrimeProperties.scala
).

---

## 6. Filter Preserves Primes

**Intuition:** The filter removes all multiples of the filter prime. Primes other than the filter prime cannot be multiples of it (by definition), so they survive.

**Why This Matters:** This is the core soundness property of the sieve: filtering by one prime never removes other primes. Each iteration preserves all previously discovered primes.

### Mathematical Proof

```math
\text{isPrime}(q) \land q \neq \text{filterPrime} \implies q \bmod \text{filterPrime} \neq 0
```

**Proof:** Same reasoning as Section 5. A prime cannot be divisible by a different prime.

### Stainless Verification

```scala
def filterPreservesPrimes(q: BigInt, filterPrime: BigInt): Boolean = {
  require(isPrime(q))
  require(isPrime(filterPrime))
  require(q =!= filterPrime)
  Calc.mod(q, filterPrime) =!= BigInt(0)
}.holds
```

This property is verified in the [
  PrimeProperties::filterPreservesPrimes
](
  ../src/main/scala/v1/prime/PrimeProperties.scala
).

### Corollary: Filtered List Contains All Primes

```math
q \in \text{originalPrimes} \land \text{isPrime}(q) \land q \neq \text{filterPrime} \implies q \in \text{filteredPrimes}
```

This directly follows from the filter definition and the lemma above.

### Stainless Verification

```scala
def filteredContainsAllPrimes(
  originalPrimes: List[BigInt],
  filterPrime: BigInt
): Boolean = {
  require(originalPrimes.forall(isPrime))
  require(isPrime(filterPrime))
  
  val filtered = originalPrimes.filter(p => Calc.mod(p, filterPrime) =!= BigInt(0))
  
  originalPrimes.forall(p =>
    (p =!= filterPrime) ==> filtered.contains(p)
  )
}.holds
```

This property is verified in the [
  PrimeProperties::filteredContainsAllPrimes
](
  ../src/main/scala/v1/prime/PrimeProperties.scala
).

---

## 7. Head Is Prime

**Intuition:** The head of a Sieve Sequence is the smallest positive integer coprime to the modulus. By construction, this must be prime — if it were composite, it would have a prime factor that is also coprime to the modulus and smaller, contradicting minimality.

**Why This Matters:** This is the key theorem that makes the sieve work. Every SieveSequence head is guaranteed to be prime, so we can use it as the next prime in the sieve.

### Mathematical Proof

Let $M = \prod_{i=1}^{k} p_i$ be the primorial of the first $k$ primes. Let $h$ be the smallest positive integer coprime to $M$.

**Claim:** $h$ is prime.

**Proof by contradiction:** Assume $h = a \cdot b$ with $a, b > 1$. Since $a < h$ and $b < h$, neither $a$ nor $b$ is divisible by any $p_i$ (otherwise $h$ would be). Thus $a$ and $b$ are both coprime to $M$, contradicting the minimality of $h$. ∎

### Stainless Verification

```scala
def assertHeadIsPrime(primes: List[BigInt]): Boolean = {
  require(primes.forall(isPrime))
  require(primes.nonEmpty)
  
  val seq = SieveSequence(primes)
  isPrime(seq.head)
}.holds
```

This property is verified in the [
  SieveSequenceProperties::assertHeadIsPrime
](
  ../src/main/scala/v1/seq/sieve/properties/SieveSequenceProperties.scala
).

---

## 8. Conclusion

We have presented a formal verification of Sieve Sequence properties using the Stainless verification system. The key results are:

1. **Unit cycle generates naturals** — $\text{CycleIntegral}(\text{MemCycle}([1]), init)_i = init + i + 1$
2. **Strict monotonicity** — larger positions give larger values
3. **Distinct primes are coprime** — no prime divides another distinct prime  
4. **Filter preserves primes** — filtering by one prime doesn't remove other primes
5. **Head is prime** — every SieveSequence head is guaranteed prime

These properties establish the mathematical foundation for the Sieve of Eratosthenes. The verification status is carried by the exact `.holds` functions referenced above, not by a repository-wide counter.

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

## Appendix A: Stainless Verification Log Output

The latest `just verify` run verifies all the described properties without errors. The full log output is available at: [verify.log](../verify.log)