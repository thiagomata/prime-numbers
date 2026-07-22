This summary formalizes the logic behind the "1/p" density invariant, creating a structured reference for your documentation and future proof implementation.

---

## Architectural Invariant: Uniform Residue Distribution

The core principle governing your Sieve Engine is the **Invariance of Density** for residue classes. Even as the sequence is refined (filtered) by successive primes, the density of multiples for any prime $p$ (where $p >$ current modulus) remains fixed at $1/p$.

### 1. The Fundamental Logic

The stability of this proportion relies on the **Independence of Coprime Residue Classes**.

When a sequence is filtered by a prime $q$, the sequence is reduced in size by a factor of $\frac{q-1}{q}$. Because the filter $q$ and the target $p$ are coprime ($\gcd(q, p) = 1$), the multiples of $q$ are distributed evenly across the residues of $p$. Consequently, the count of multiples of $p$ is reduced by the exact same factor.

### 2. The Algebraic Proof

Given:

* $N$: Current number of elements in the sequence.
* $C_p$: Count of elements in the sequence that are multiples of $p$.
* $q$: The prime currently being filtered.

The density before filtration is:


$$D_{old} = \frac{C_p}{N} = \frac{1}{p}$$

After filtering $q$, the new count $N'$ and new multiple count $C_p'$ are:


$$N' = N \left(1 - \frac{1}{q}\right)$$

$$C_p' = C_p \left(1 - \frac{1}{q}\right)$$

The density after filtration is:


$$D_{new} = \frac{C_p'}{N'} = \frac{C_p \left(1 - \frac{1}{q}\right)}{N \left(1 - \frac{1}{q}\right)} = \frac{C_p}{N} = \frac{1}{p}$$

The scaling factor cancels out entirely, proving that the proportion is an **algebraic invariant** regardless of the filtration history.

### 3. Strategy for Formal Verification

To avoid infinite loops or state-space explosion in `Stainless`, we shift from **operational verification** (traversing the list) to **axiomatic property verification**.

| Approach | Implementation | Reason |
| --- | --- | --- |
| **Old (Inefficient)** | Iterate over `MemCycle` to count multiples. | Triggers SMT solver loops and exponential growth. |
| **New (Efficient)** | Verify the transformation of the Modulus and Density. | Proves the state transition algebraically. |

#### Inductive Proof Logic

1. **Base Case:** Assert uniformity for $S_0$ (integers $> 1$) as an axiom.
2. **Inductive Step:** Define a predicate `isUniform(sieve)` that checks if `sieve.countMultiples(p) * p == sieve.size`.
3. **Proof Requirement:** Verify `isUniform(sieve) ==> isUniform(nextLevel(sieve, q))`.

### 4. Implementation Guidelines

To maintain the **Single Source of Truth** and satisfy the Type System:

* **Derive, don't Compute:** Define `size` as a function of the current modulus (e.g., using the totient function) rather than by counting elements in memory.
* **Axiomatic Logic:** Use `@extern` or `@axiom` for calculations involving the primorial modulus to tell the solver to treat these as trusted mathematical facts.
* **Property-Based:** Your verification should assert that the **Ratio Invariant** holds across the `nextLevel` transition, not that the specific element distribution remains identical.

---

### Summary of Hypotheses

* **Persistence:** The $1/p$ density is a structural necessity derived from coprimality.
* **Robustness:** The proportion is insensitive to the order or quantity of smaller primes filtered.
* **Verification:** The system is "Safe" as long as the total sequence size does not drop below a critical threshold relative to the target $p$, which we have identified as the "Safe Regime."

Does this organizational structure provide a clear enough blueprint to begin codifying the inductive proof in your `SieveSequenceProperties.scala` file?    