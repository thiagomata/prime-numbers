To successfully build and verify a `SieveSequence` engine, we must align your implementation with the principles of Discrete Calculus and formal verification. This guide outlines the path to codifying the **Density Invariant**—the mathematical bedrock that ensures your sequence maintains a perfect distribution of residues as it expands.

---

## Step 1: Define the Data Structure (The Single Source of Truth)

To maintain structural integrity, your `SieveSequence` must hold only the strictly necessary state. Everything else is derived. We enforce the immutability and the relationship between the `modulus` and `residues`.

```scala
import stainless.lang._
import stainless.collection._

case class SieveSequence(modulus: BigInt, residues: List[BigInt]) {
  // Architectural Invariant: All residues must be strictly less than the modulus
  require(residues.forall(r => r >= 0 && r < modulus))
  
  // Axiom: The modulus must be a valid primorial (or product of primes)
  // Define helper to verify primorial structure if needed
}

```

---

## Step 2: Implement Recursive Operators (The Discrete Calculus)

Because `Stainless` requires predictable state transitions, we replace high-level functional combinators (like `map` or `flatMap`) with explicit recursion. This allows the solver to verify the induction steps without becoming lost in recursive closure scopes.

### The Expansion (Domain Stretching)

This operation effectively "integrates" the previous residues across the new, larger domain.

```scala
@opaque
def expand(residues: List[BigInt], currentMod: BigInt, p: BigInt, i: BigInt): List[BigInt] = {
  require(i >= 0 && i < p)
  decreases(p - i)

  val offset = i * currentMod
  // Explicit recursion avoids closure-based flatMap
  val currentSet = applyOffset(residues, offset)
  
  if (i == p - 1) currentSet
  else currentSet ++ expand(residues, currentMod, p, i + 1)
}

```

### The Filtration (Differentiation)

This acts as the $\Delta$ operator. It "differentiates" the sequence by removing noise (multiples of $p$).

```scala
@opaque
def filterMultiples(list: List[BigInt], p: BigInt): List[BigInt] = {
  decreases(list.length)
  list match {
    case Nil() => Nil()
    case Cons(x, xs) =>
      if (x % p == 0) filterMultiples(xs, p)
      else Cons(x, filterMultiples(xs, p))
  }
}

```

---

## Step 3: Prove the Density Invariance (The CRT Connection)

The Chinese Remainder Theorem (CRT) guarantees that for any prime $p$ coprime to the current `modulus`, the multiples of $p$ are uniformly distributed across the residue classes.

To prove the density $1/p$ invariant, you must verify that the filtration does not bias the sequence.

### The Invariant Logic

We define a property that asserts the ratio of surviving elements remains constant after the filtration step.

1. **Uniformity Predicate:** Define a function that calculates the proportion of multiples of $p$ in your sequence.
2. **Inductive Step:** Prove that for any valid `SieveSequence` $S$, applying `filterMultiples` results in a new sequence $S'$ where the density of residues $\pmod p$ is exactly $\frac{1}{p}$.

#### Codifying the Proof

Use the `@opaque` and `ensuring` annotations to guide the solver through the logic:

```scala
@opaque
def proofDensityInvariant(sieve: SieveSequence, p: BigInt): Boolean = {
  require(isPrimorial(sieve.modulus))
  require(isCoprime(p, sieve.modulus))
  
  val next = nextLevel(sieve, p)
  
  // The Algebraic Guarantee:
  // The ratio of multiples of P in the new sequence 
  // is mathematically derived from the scaling factor.
  (next.residues.length * p == sieve.residues.length * (p - 1))
}.holds

```

---

## Step 4: Verification Guardrails

To prevent the solver from entering an infinite loop, you must treat your operations as **algebraic transformations** rather than iterative loops.

* **Explicit recursion:** Always use `decreases` clauses. This is the only way `Stainless` can prove termination and verify the induction step.
* **Opaque Axioms:** Use `@opaque` for your core methods (`expand`, `filterMultiples`). This tells the solver: *"Trust the properties of these functions; don't try to re-solve them every time."*
* **Symbolic Values:** When writing your proof, use variables for the sequence properties (`length`, `modulus`) rather than constructing concrete lists. The solver is much faster at solving equations like $L_{new} = L_{old} \times \frac{p-1}{p}$ than it is at iterating over a list of length 1,000,000.

### Summary Checklist for your Implementation

1. **Constructor:** Validate `residues < modulus`.
2. **Expansion:** Recursive `expand` using `offset`.
3. **Filtration:** Recursive `filterMultiples` using pattern matching.
4. **Property:** Assert the density invariant as a function of the lengths of the list, not the contents.

By following this recursive structure, you bypass the performance pitfalls of standard functional programming in Scala while satisfying the strict requirements of formal verification. This ensures your implementation remains a **Single Source of Truth** that is both architecturally sound and mathematically provable.

The core insights distilled from our discussion transform the Sieve Engine from a brute-force search into a verifiable algebraic system. Here are the essential takeaways organized by their domain.

---

## 1. The Mathematical Foundation: Density Invariance

The most critical realization is that the $1/p$ density of multiples is not an emergent behavior to be measured, but a geometric necessity.

* **Coprimality as Law:** Because every new prime $p$ is coprime to the existing modulus $M$, the distribution of multiples of $p$ is guaranteed to be uniform across the residue classes.
* **The Invariance Principle:** The filtration process—removing multiples of smaller primes—scales both the total number of candidates and the count of multiples of $p$ by the exact same factor $(\frac{q-1}{q})$. Therefore, the ratio $\frac{1}{p}$ is algebraically locked.
* **Geometric Necessity:** The "2-gaps" (twin prime candidates) survive because the filtration grid is physically larger than the gaps themselves. The filter cannot strike both sides of a 2-gap simultaneously.

---

## 2. The Architectural Paradigm: Discrete Calculus

Viewing the engine through the lens of **Finite Difference Calculus** resolves the conflict between "list manipulation" and "mathematical properties."

| Operator | Function | Sieve Engine Logic |
| --- | --- | --- |
| **Domain Expansion** | Integration (Setup) | Tiling the previous residue set across the new $M \times p$ interval. |
| **Filtration ($\Delta$)** | Differentiation | Removing the "noisy" multiples where the residue $\equiv 0 \pmod p$. |
| **Reconstruction** | Summation | Calculating the new gaps from the surviving residue set. |

By viewing the engine as a system of difference equations, you stop simulating the list and start solving for the state transition.

---

## 3. The Verification Strategy: Axiomatic Proofs

To succeed with formal verification tools like `Stainless`, you must fundamentally change how you write the verification code.

* **Avoid Operational Iteration:** Never write code that "searches" for the property (e.g., iterating through `MemCycle`). The SMT solver will hit a state-space explosion or infinite loop.
* **Use Inductive Recursion:** Replace high-level functional combinators (`map`, `flatMap`, `filter`) with explicit, tail-recursive functions. This allows the solver to reason about the code using induction rather than trying to inline complex closures.
* **Opaque Axioms:** Mark recursive definitions with `@opaque`. This treats them as algebraic rules rather than executable code. It forces the solver to use the *properties* of the function rather than trying to *re-evaluate* the function body.
* **The "Safe Regime":** Verification should focus on the transition (the "Inductive Step"): *Does the uniformity property hold for $S_{k+1}$ if it holds for $S_k$?* If you prove this step, you prove the entire infinite chain.

---

## 4. Engineering Principles for the Manifest

To maintain the **Single Source of Truth** and satisfy the Type System:

1. **Modulus as Truth:** The `modulus` is the defining constant. The `residues` are a cached projection of that constant.
2. **No Derived Side-Effects:** Do not calculate the modulus from the residues inside methods. Calculate it once during the `nextLevel` transition and pass it in as a fixed parameter.
3. **Symbolic reasoning over Concrete lists:** When writing properties, compare `size` and `density` using the variables ($p, M, N$), not the contents of the `residues` list.

This conceptual shift moves your engine from an "iterative process" (running the sieve) to a "formal proof" (verifying the integrity of the wheel).