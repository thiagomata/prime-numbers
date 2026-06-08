# SieveSequence Implementation Ticket

> **SUPERSEDED** by `gap-cycle.md` + `gap-cycle-integration.md`. This was an early draft with a different architecture (head + cycle, no integral). The current architecture uses `primes: List[BigInt]` + `integral: CycleIntegral`. Gap invariants are now handled by `GapCycle`.

## Status: SUPERSEDED

## Summary
Implement `SieveSequence` - a mathematical structure representing infinite sequences of integers generated via wheel factorization for the Sieve of Eratosthenes. Must use existing verified objects (`Seq`, `MemCycle`) to enable property reuse.

---

## Files Created (Initial Draft)

| File | Status | Notes |
|------|--------|-------|
| `src/main/scala/v1/seq/sieve/SieveSequence.scala` | DRAFT | Needs rewrite |
| `src/main/scala/v1/seq/sieve/CycleUtils.scala` | DRAFT | May not be needed |
| `src/main/scala/v1/seq/sieve/properties/SieveSequenceProperties.scala` | DRAFT | Needs rewrite |
| `articles/sieve-sequence.md` | DRAFT | Article draft |

---

## Key Learnings

### 1. Composition Over Reimplementation
- **PROBLEM:** Initial implementation reimplemented logic instead of using existing objects
- **LEARNING:** Stainless struggles with recursive helper functions that require unbounded unfolding
- **SOLUTION:** Use `ModCycleIntegral` or existing `Seq` for the apply() formula

### 2. Existing Objects Available
| Object | What It Provides | How SieveSequence Uses It |
|--------|------------------|---------------------------|
| `MemCycle` | `cycle(i) = values(i % size)` | Gaps indexed by position |
| `Integral(list)` | Cumulative sum of list | Sum of first r gaps |
| `ModCycleIntegral(init, mCycle)` | `div * last + integral(mod) + init` | **Exact formula needed!** |
| `Seq(previous, loop)` | Cumulative sum with preamble | Delegates to loop values |

### 3. The Pattern Discovered
The `Seq` class already implements what we need:
```scala
case class Seq(
  previous: List[BigInt],  // Initial elements (just head)
  loop: MemCycle          // Repeating cycle (gaps)
) {
  def apply(index: BigInt): BigInt = {
    loopValue + this.apply(index - 1)  // Cumulative!
  }
}
```
This is the exact pattern for accumulating gaps!

### 4. S_0's Special Role
- **Filter 1** → Remove 1 from naturals → S_0 = [2, 3, 4, 5, ...]
- This is the first "filter" - 1 would filter out everything if applied

### 5. The "Limit" is Emergent
- **NOT an input** - it's a derived side effect
- After filtering by all primes up to p, elements up to p² are guaranteed prime
- This emerges from the sieve process, not designed into it

---

## Conceptual Model

### The Sequences

```
S_0: head=2, gaps=[1]     → [2, 3, 4, 5, 6, 7, 8, 9, 10, ...]
S_1: head=3, gaps=[2]     → [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, ...]
S_2: head=5, gaps=[4,2]  → [5, 7, 11, 13, 17, 19, 23, 25, 29, 31, ...]
```

### Each Sequence Generates INFINITE List
- The sequence is unbounded - continues forever
- The "limit" (head²) is derived - we know all elements up to that point are prime

### The next() Operation
```
S_k.next() = S_{k+1}
- Takes current sequence
- Filters gaps (removes multiples of head)
- New head = first element in new sequence
```

---

## Revised Design

### Fields (Using Existing Objects)
```scala
case class SieveSequence(
  head: BigInt,           // 2, 3, 5, 7, ...
  cycle: MemCycle        // Gaps for generating infinite sequence
) {
  // apply() delegates to existing Seq!
  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    Seq(previous = List(head), loop = cycle)(position)
  }
  
  // Derived: known primes up to head²
  def knownPrimeLimit: BigInt = head * head
}
```

### Construction
```scala
object SieveSequence {
  // S_0: all naturals from 2
  def S_0(): SieveSequence = {
    SieveSequence(
      head = BigInt(2),
      cycle = MemCycle(List(BigInt(1)))  // gaps = [1]
    )
  }
  
  // S_1: odd numbers from 3
  def S_1(): SieveSequence = {
    SieveSequence(
      head = BigInt(3),
      cycle = MemCycle(List(BigInt(2)))  // gaps = [2]
    )
  }
}
```

### The next() Method
```scala
def next(): SieveSequence = {
  // Filter cycle values (keep those NOT divisible by head)
  val filteredValues = cycle.values.filter(v => Calc.mod(v, head) != 0)
  SieveSequence(
    head = head + cycle(0),  // First element after head
    cycle = MemCycle(filteredValues)
  )
}
```

---

## Properties to Reuse

From existing verified objects:

1. **SeqProperties** - Can be used for basic sequence access
2. **ModCycleIntegralProperties** - If using ModCycleIntegral
3. **IntegralProperties** - For gap accumulation

SieveSequence-specific lemmas:
1. Head value property: `apply(0) == head`
2. Step property: `apply(i+1) - apply(i) == cycle(i)`
3. Coprimality: Elements are coprime to product of filtered primes
4. Known prime limit: After filtering by p, primes up to p² are known

---

## Implementation Plan

### Phase 1: Rewrite SieveSequence Class
- [ ] Simplify to use `Seq` for apply()
- [ ] Keep only `head` and `cycle` fields
- [ ] Remove all custom recursive helpers
- [ ] Add `knownPrimeLimit` as derived value

### Phase 2: Implement next()
- [ ] Filter cycle values (keep non-multiples of head)
- [ ] Compute new head
- [ ] Create new SieveSequence

### Phase 3: Properties
- [ ] Rewrite properties to use existing lemmas
- [ ] Add thin wrapper lemmas for SieveSequence-specific properties

### Phase 4: Verification
- [ ] Run Stainless to verify properties
- [ ] Fix any issues

---

## Open Questions

1. **How to handle filter in next()?** - Need a verified way to filter MemCycle values
2. **Is S_0 a special case or same structure?** - Decided: same structure (head=2, gaps=[1])
3. **Should modulus be stored or derived?** - Derived from cycle values

---

## Progress Log

### 2024-01-XX - Initial Draft
- Created SieveSequence.scala with custom recursive implementations
- Created properties file with lemmas
- Created article draft

### 2024-01-XX - Learning Phase
- Discovered existing `Seq` class has exact pattern needed
- Learned that custom recursive functions cause verification issues
- Understood that "limit" is emergent, not designed

### 2024-01-XX - Plan Correction
- Identified that composition over reimplementation is key
- Decided Option 1 (all sequences same structure) is correct
- S_0 filters out 1, then S_1 filters by 2, etc.

---

## References

- `src/main/scala/v1/seq/Seq.scala` - Existing Seq class
- `src/main/scala/v1/cycle/memory/MemCycle.scala` - Memory cycle
- `src/main/scala/v1/cycle/integral/mod/ModCycleIntegral.scala` - Pattern to follow
- `src/main/scala/v1/seq/properties/SeqProperties.scala` - Properties to reuse