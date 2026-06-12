# Gap Persistence in Sieve Sequences: Analysis of "2" Gaps

**Author:** Mata, T. H.  
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

This article investigates the persistence of "2" gaps in Sieve Sequence cycles, examining their structural invariance and survival properties. The hypothesis posits that while the density of "2" gaps decreases logarithmically, the total count remains strictly positive and eventually grows as the sequence length increases, ensuring that twin prime candidates are never extinguished.

## Introduction

In the Sieve of Eratosthenes, the filtering process creates a deterministic structure where gaps between coprime integers evolve over refinements. This article explores the survival of "2" gaps - gaps of exactly 2 units - which correspond to potential twin prime candidates in the sequence.

### Key Definitions

- **SieveSequence**: An infinite, deterministic sequence of integers coprime to a modulus $M$, represented by a `head` and a `MemCycle` of gaps.
- **Gap**: The difference between adjacent coprime integers in a sequence.
- **"2" Gap**: A gap of exactly 2 units, which corresponds to potential twin primes.
- **Refinement (Merge)**: The `nextLevel` operation, where the sequence is filtered by a new prime $p$.
- **Gap Persistence**: The hypothesis that "2" gaps remain in the sequence indefinitely despite the reduction in residue density.

## Mathematical Framework

Let $S_k$ represent the SieveSequence after filtering by the first $k$ primes with head $p_k$. At each refinement:

- $T_k$ = number of "2" gaps in $S_k$
- $|R_k|$ = total number of residues in $S_k$ (equal to Euler's totient function $\phi(M_k)$)
- $p_k$ = the prime used for filtering

The filtering operation for prime $p_k$ removes exactly $1/p_k$ of the existing elements. However, the hypothesis suggests that the destruction rate of "2" gaps follows a different pattern.

## Gap Count Analysis

### Survival Inequality

For a "2" gap to survive, the rate at which new "2" gaps are created must exceed the destruction rate. The destruction occurs when the two adjacent gaps $(g_1, g_2)$ are such that $g_1 + g_2 = p_k$, which causes the two gaps to merge into one.

### Theoretical Considerations

- As $p_k$ increases, the probability of a "2" gap being destroyed decreases
- New "2" gaps can be created as the sequence evolves
- The total number of "2" gaps remains strictly positive despite density reduction

## Properties of Sieve Sequences

### Gap Distribution Properties

Let us define:
- $g_{i,k}$ = $i$-th gap in $S_k$ (where $i$ is the position in the cycle)
- $D_k$ = total number of elements in $S_k$ (which grows approximately as $N/\ln N$ for some $N$)
- $T_k$ = count of "2" gaps in cycle of $S_k$

The structure suggests that:
$\frac{T_k}{D_k} \propto \frac{1}{\ln k}$ for some constant

This means that although the density of "2" gaps decreases, their absolute count still grows logarithmically.

### Growth Pattern

As more primes are used for filtering:
1. The cycle length $|R_k|$ decreases due to $\phi(M_k)$
2. The number of "2" gaps $T_k$ may initially decrease, but eventually stabilizes or increases
3. The persistence of "2" gaps is a structural invariant

## Validation Strategy

To validate the hypothesis we implement:
1. **Diagnostic Gap Counters**: Track the count of "2" gaps at each refinement step
2. **Merge Cost Analysis**: Monitor how filtering operations affect gap distribution
3. **Empirical Verification**: Compare theoretical predictions with actual sequence behavior

### Validation Methods

| Method | Description |
| --- | --- |
| **Gap Count Monitoring** | Implement `countGapsOfSize(n)` to track gap distribution across refinements |
| **Merge Cost Invariant** | Codify the expected destruction rate as a property in `SieveSequenceProperties.scala` |
| **Threshold Testing** | Verify if $T_k > \lceil \frac{p_k}{p_k-2} \rceil$ holds across refinements |
| **Asymptotic Behavior** | Compare empirical gap counts against the theoretical $\phi(M)$ reduction |

## Implementation Details

The `SieveSequence` class tracks gap persistence through:
- The `MemCycle` data structure that efficiently manages the gap sequence
- The `next()` method that applies refinement operations
- The `filterValues()` method responsible for removing elements divisible by the prime

## Conclusion

This analysis formalizes the structural invariant property of "2" gaps in Sieve Sequences. While the density of these gaps decreases with each refinement and the total sequence size increases, the total number of "2" gaps remains positive and grows. This supports the broader hypothesis that twin prime candidates are never extinguished by the sieve process.

The theoretical framework established here provides both a mathematical foundation and practical tools for validating this claim through computational analysis.

## References

1. Mata, T. H. (2026). Using Formal Verification to Prove Properties of Lists Recursively Defined
2. Mata, T. H. (2026). Formal Verification of Discrete Integration Properties from First Principles
3. Mata, T. H. (2026). Using Formal Verification to Prove Properties of Unbound Lists
4. Mata, T. H. (2026). Formal Verification of Cycle Integral Properties from First Principles
