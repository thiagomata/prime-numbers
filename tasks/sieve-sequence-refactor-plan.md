# SieveSequence Refactoring Plan

## Guidelines
1. Don't do too many changes at the same time. Add one thing, test it.
2. Whatever can be asserted first (`import verification.Helper.assert`) do it.
3. Unit tests are your friend - use unit tests before Stainless verification.
4. When possible use invariants. Check ModDiv how invariants can be helpful.
5. If we can make it simpler, let's make it simpler.
6. Build the object thinking about the invariants first.
7. Use `@opaque`/`@extern` as last resort only.
8. Keep this ticket updated as you work on it — add insights, concerns, and failed attempts.

## Goals

| Goal | Description | Invariant |
|------|-------------|-----------|
| **Middle-term** | Prove 1/p uniformity invariant | `countMultiples(p) * p == size` for any p > head |
| **Long-term** | Prove "2" gap survival (twin prime candidates) | `T_k > 2 * (R_k / head)` |

---

## Architectural Design

### Why Add `primes` Field
By making the filtering history explicit, invariants become structural properties rather than things to verify. The modulus equals `product(primes)` and the size equals `φ(modulus)`.

### New Structure (Option A)
```scala
case class SieveSequence(
  head: BigInt,           // Current prime (e.g., 5 after filtering 2, 3)
  primes: List[BigInt],   // Primes already filtered: [2, 3]
  cycle: MemCycle          // Gaps (differences between consecutive elements)
) {
  require(head > 0)
  require(primes.forall(p => p > 0))
  require(cycle.size > 0)
  require(cycle.values.forall(_ > 0))
  
  // Derived values — these are the key invariants
  def modulus: BigInt = primes.foldLeft(BigInt(1))(_ * _)  // product of primes
  def size: BigInt = totient(modulus)                       // φ(modulus)
}
```

**Note:** Option A keeps `head` separate from `primes` (primes = previous only). 
If this becomes problematic, we can switch to Option B where `primes` includes `head`.

### Naming Convention
| Term | Meaning | Example (S_2) |
|------|---------|---------------|
| `head` | First element (prime) | 5 |
| `primes` | Primes already filtered (filtering history) | [2, 3] |
| `cycle` / `gaps` | Differences between consecutive elements | [4, 2] |
| `modulus` | product of `primes` | 6 |
| `size` | number of residues = φ(modulus) | 2 |

---

## Key Invariants (Design Goals)

### Invariant 1: Size from Modulus (Structural)
```scala
size == totient(modulus)
// φ(2*3) = φ(6) = 2
```

### Invariant 2: Sum of Gaps = Modulus (Structural)
```scala
sum(gaps) == modulus
// gaps [4, 2] → sum = 6 = modulus
```

### Invariant 3: Uniformity (Middle-term Goal to Prove)
```scala
// For any prime p > head: countMultiples(p) * p == size
// This is structurally true because size = φ(modulus) and gcd(p, modulus) = 1
// From Chinese Remainder Theorem: multiples distribute uniformly
```

### Invariant 4: "2" Gap Survival (Long-term Goal to Prove)
```scala
// T_k = count of "2" gaps in cycle
// R_k = size (total elements)
// Max destruction by prime head = 2 * (R_k / head)
// Survival guaranteed if: T_k > 2 * (R_k / head)
```

---

## Discrete Calculus Mental Model

The `next()` operation follows the expand → filter → reconstitute pattern, 
which maps cleanly to discrete calculus operations:

| Step | Operation | Calculus Equivalent | Sieve Action |
|------|-----------|-------------------|--------------|
| 1 | Expand | Domain Extension (∫ setup) | Tile residues p times with offsets [r + i*mod] |
| 2 | Filter | Δ (Differentiation) | Remove multiples where residue ≡ 0 (mod p) |
| 3 | Reconstitute | ∫ (Integration) | Calculate gaps from sorted filtered residues |

This model from `talk.md` helps understand why invariants are preserved:
- The "area" under the residue curve remains invariant
- The filter is a linear operator
- The reconstruction (sum of gaps) recovers the modulus

---

## The Correct `next()` Algorithm

From the conversation: the old code filters cycle values directly (wrong).

### Old Code (INCORRECT)
```scala
def next(): SieveSequence = {
  val newHead = head + cycle(0)
  val filteredCycle = filterCycle(cycle, head)  // Filters steps, NOT integral!
  SieveSequence(head = newHead, cycle = filteredCycle)
}
```

### New Algorithm (CORRECT)
```
1. Expand residues p times with offsets:
   For each residue r, create [r, r+mod, r+2*mod, ..., r+(p-1)*mod]
   
2. Filter out multiples of p:
   Keep only values where value % p != 0
   
3. Reconstitute gaps:
   Sort filtered residues, calculate differences between consecutive elements
   Include wrap-around: (modulus * p - last) + first
   
4. Return new sequence:
   SieveSequence(head + cycle(0), head :: primes, MemCycle(newGaps))
```

---

## Implementation Phases

### Phase 1: Add `primes` Field and Derived Values

**Goal:** Make invariants structural by storing filtering history.

**Changes to SieveSequence:**
```scala
case class SieveSequence(
  head: BigInt,
  primes: List[BigInt],   // NEW: filtering history
  cycle: MemCycle
) {
  // Derived values
  def modulus: BigInt = primes.foldLeft(BigInt(1))(_ * _)
  // def size: BigInt = totient(modulus)  // TODO: implement or use external property
  
  require(primes.forall(p => p > 0))
  require(modulus > 0)
}
```

**Unit Tests:**
| Test | Expected |
|------|----------|
| S_0().primes | `[]` |
| S_1().primes | `[2]` |
| S_2().primes | `[2, 3]` |
| S_1().modulus | `2` |
| S_2().modulus | `6` |

**Assertions:**
```scala
assert(S_0().primes.isEmpty)
assert(S_1().primes == List(2))
assert(S_2().primes == List(2, 3))
assert(S_1().modulus == 2)
assert(S_2().modulus == 6)
assert(S_2().cycle.values == List(4, 2))
```

---

### Phase 2: Implement Correct `next()` Algorithm

**Goal:** Replace the broken filtering with expand → filter → reconstitute.

**Implementation:**
```scala
def next(): SieveSequence = {
  val newHead = head + cycle(0)
  
  // Step 1: Expand — tile residues p times
  val expanded = expandValues(modulus, head)
  
  // Step 2: Filter — remove multiples of head
  val filtered = filterMultiples(expanded, head)
  
  // Step 3: Reconstitute — calculate gaps
  val newGaps = calculateGaps(expandValues, head * modulus)
  
  // Step 4: Return
  SieveSequence(
    head = newHead,
    primes = head :: primes,
    cycle = MemCycle(newGaps)
  )
}
```

**Unit Tests:**
| Test | Expected |
|------|----------|
| S_0().next().head | 3 |
| S_0().next().primes | [2] |
| S_0().next().cycle.values | [2] |
| S_1().next().head | 5 |
| S_1().next().primes | [3, 2] |
| S_1().next().cycle.values | [4, 2] |

**Key Assertions:**
```scala
val nextSeq = next()
assert(nextSeq.primes == head :: primes)    // History maintained
assert(nextSeq.head > head)                 // Head increases
assert(nextSeq.modulus == head * modulus)   // Modulus grows
```

---

### Phase 3: Implement Helper Functions

**Goal:** Build well-tested helper functions for the expand/filter/reconstitute operations.

#### 3a: `deriveSteps(values)` — Calculate gaps from a list

```scala
def deriveSteps(values: List[BigInt]): List[BigInt] = {
  require(values.size >= 2)
  decreases(values.size)
  
  if (values.size == 2) {
    List(values(1) - values(0))
  } else {
    List(values(1) - values(0)) ++ deriveSteps(values.tail)
  }
}
```

**Unit Tests:**
| Input | Expected |
|-------|----------|
| [5, 7, 11] | [2, 4] |
| [5, 7, 11, 13, 17] | [2, 4, 2, 4] |
| [2, 3] | [1] |

**Key Invariant:**
```scala
assert(ListUtils.sum(steps) + values.head == values.last)
```

#### 3b: `expandValues(mod, factor)` — Tile residues

```scala
def expandValues(mod: BigInt, factor: BigInt): List[BigInt] = {
  require(mod > 0 && factor > 0)
  // Generate residues from modulus, then tile factor times with offsets
  // Explicit recursion, NO flatMap/map
}
```

#### 3c: `filterMultiples(list, divisor)` — Filter by divisibility

```scala
def filterMultiples(list: List[BigInt], divisor: BigInt): List[BigInt] = {
  require(divisor > 0)
  decreases(list.length)
  
  list match {
    case Nil() => Nil()
    case Cons(x, xs) =>
      if (Calc.mod(x, divisor) == 0) filterMultiples(xs, divisor)
      else Cons(x, filterMultiples(xs, divisor))
  }
}
```

**Unit Tests:**
| Input | divisor | Expected |
|-------|---------|----------|
| [1, 2, 3, 4, 5, 6] | 3 | [1, 2, 4, 5] |
| [3, 6, 9] | 3 | [] |
| [1, 5] | 3 | [1, 5] |

**Key Invariant (from ModOperations.modZeroPlusC):**
```scala
// Removing multiples doesn't change the sum mod divisor:
assert(Calc.mod(ListUtils.sum(values), divisor) == Calc.mod(ListUtils.sum(filtered), divisor))
```

#### 3d: `calculateGaps(sortedResidues, modulus)` — Reconstitute

```scala
def calculateGaps(sortedResidues: List[BigInt], modulus: BigInt): List[BigInt] = {
  require(sortedResidues.nonEmpty)
  require(sortedResidues.forall(r => r >= 0 && r < modulus))
  
  // 1. Gaps between consecutive residues
  val innerGaps = deriveSteps(sortedResidues)
  
  // 2. Wrap-around gap: (modulus - last) + first
  val wrapGap = modulus - sortedResidues.last + sortedResidues.head
  
  innerGaps ++ List(wrapGap)
}
```

**Unit Tests:**
| Input | modulus | Expected |
|-------|---------|----------|
| [1, 5] | 6 | [4, 2] (wrap: (6-5)+1 = 2) |
| [1, 7, 11, 13, 17, 19, 23, 29] | 30 | [6, 4, 2, 4, 2, 4, 6, 2] |

---

### Phase 4: Prove Uniformity Invariant (Middle-term Goal)

**Goal:** Prove that any prime p > head has exactly size/p multiples in the sequence.

**Property to Prove:**
```scala
def uniformityInvariant(seq: SieveSequence, p: BigInt): Boolean = {
  require(p > seq.head)
  require(gcd(p, seq.modulus) == 1)  // Always true by construction
  
  seq.countMultiples(p) * p == seq.size
}
```

**Proof Strategy:**
1. Base case: Prove for S_0 (trivial — all integers)
2. Inductive step: Show uniformity is preserved by `next()`
   - Use: φ(M * p) = φ(M) * (p - 1)
   - Show: countMultiples scales by (p-1)/p
3. Key insight from `talk.md`: Define algebraically, not by iteration

**Stainless-Safe Pattern:**
```scala
// Define count algebraically — NO iteration
def countMultiples(p: BigInt): BigInt = {
  require(gcd(p, modulus) == 1)
  size / p  // By uniformity — this IS the definition
}

// Verify structurally: countMultiples(p) * p == size
// Follows from totient properties
```

**Verification Guardrails (from talk.md):**
- Use symbolic reasoning over concrete lists
- Compare `size` and `density` using variables, not list contents
- Verify transition (inductive step), not the infinite sequence
- Mark recursive helpers `@opaque` only if solver cannot handle them

---

### Phase 5: Prove "2" Gap Survival (Long-term Goal)

**Goal:** Prove that "2" gaps always survive in any SieveSequence.

**Insight from conversation:**
The survival of "2"s depends on the inequality:
- T_k (count of 2-gaps) > 2 * (R_k / head)
- Where max destruction = 2 * (R_k / head) because each removed element affects 2 adjacent gaps

**Property to Prove:**
```scala
def twosSurvivalInvariant(seq: SieveSequence): Boolean = {
  val T_k = countGapsOfSize(seq.cycle, 2)
  val R_k = seq.size                    // Total elements
  
  // Max destruction of "2" gaps by the filter (head):
  // At most 2 * (R_k / head) gaps destroyed
  // (each removed residue touches 2 adjacent gaps)
  
  T_k > 2 * (R_k / seq.head)
}
```

**Verification Strategy (from conversation):**
1. Track T_k and R_k at each step
2. Verify the inequality T_k > 2 * (R_k / p) holds
3. Show the surplus grows over time (diverges after p ≥ 7)
4. Key insight: The filter cannot strike both sides of a 2-gap simultaneously

**Expected Data (from conversation's survival table):**
| Prime | T_k (2-gaps) | R_k (size) | Max Destr (2*R_k/p) | Safe? |
|-------|-------------|-----------|---------------------|-------|
| 7 | 3 | 8 | 2.28 | Yes |
| 11 | 15 | 48 | 8.72 | Yes |
| 13 | 135 | 480 | 73.84 | Yes |
| 17 | 1485 | 5760 | 677.64 | Yes |

The surplus grows significantly as p increases.

---

## Summary

| Phase | Focus | Tests First | Key Invariants |
|-------|-------|-------------|----------------|
| 1 | Add `primes` field + derived values | Unit tests | `modulus = product(primes)` |
| 2 | Correct `next()` algorithm | Unit tests | `modulus *= head`, `head increases` |
| 3 | Helpers: `deriveSteps`, `filterMultiples`, `calculateGaps` | Unit tests each | `sum(gaps) + first == last` |
| 4 | Prove uniformity | Stainless properties | `countMultiples(p) * p == size` |
| 5 | Prove "2" survival | Stainless properties | `T_k > 2 * (R_k / head)` |

---

## Stainless-Safe Coding Rules (from talk.md)

1. **Avoid Operational Iteration:** Never iterate through cycles to count. The solver will loop forever.
2. **Use Inductive Recursion:** Replace `map`, `flatMap`, `filter` with explicit recursive functions with `decreases` clauses.
3. **Symbolic Reasoning:** Define properties using algebraic variables (`p, M, size`), not concrete list contents.
4. **Verify Transitions:** Prove `invariant(S_k) ==> invariant(S_{k+1})`. This covers the infinite chain.
5. **Opaque as Last Resort:** Only mark a function `@opaque` if the solver truly cannot handle it otherwise.
6. **Everything Verifiable:** All code must be verifiable by Stainless:
   - Private methods → add `.holds` invariants within the class
   - External/object methods → create properties objects with `.holds` proofs
   - Unit tests alone are NOT sufficient — Stainless verification is required

---

## Concerns & Open Questions

1. **Totient implementation:** Do we need to compute φ(modulus), or can we use it as a pure property without computing?
2. **Residues vs Gaps duality:** The current code stores gaps in `cycle`. Do we need explicit residues or keep them derived?
3. **S_0 definition:** S_0 = [2, 3, 4, ...] with head=2 and gaps=[1]. Does this need special-casing?
4. **Performance vs Proofs:** The recursive helpers might be slower at runtime. Can we have separate "verified" and "production" implementations?

---

## References

### Articles (Mathematical Foundation)
- `articles/sieve-sequence.md` — Sieve Sequence formal properties
- `articles/gap-persistence.md` — "2" gap survival analysis
- `articles/cycle.md` — Cycle definition and properties
- `articles/integral.md` — Integral definition and properties
- `articles/integral-cycle.md` — Cycle Integral definition and properties
- `articles/modulo.md` — Modulo arithmetic definition and properties

### Existing Scala Classes
- `v1/seq/sieve/SieveSequence.scala` — Main class (to refactor)
- `v1/seq/sieve/SieveGenerator.scala` — Generator (likely to merge into SieveSequence)
- `v1/seq/sieve/CycleUtils.scala` — Cycle utilities
- `v1/cycle/memory/MemCycle.scala` — Cycle storage with memoized mod checks
- `v1/cycle/integral/recursive/CycleIntegral.scala` — Integral generation over cycles
- `v1/list/ListUtils.scala` — List sum and slice operations
- `v1/div/DivMod.scala` — Division and modulo with proofs
- `v1/Calc.scala` — Arithmetic helper (mod, div)

### Key Properties to Leverage
- `CycleIntegralProperties.assertDiffEqualsCycleValue` — integral diff = cycle value
- `ModOperations.modAdd` — mod(a+c, b) == mod(mod(a,b) + mod(c,b), b)
- `ModOperations.modZeroPlusC` — removing multiples preserves sum mod
- `CycleCheckMod.allModZeroPropagate` — mod zero results propagate correctly
- `IntegralProperties.assertLastEqualsSum` — last = init + sum(list)

### Related Markdown Files
- `tasks/talk.md` — Discrete calculus approach and verification guide
- `haskell_test/sieve-seq.md` — Original sieve sequence documentation
- `tasks/seq.md` — Sequence hierarchy and wheel modulo notation

---

## Change Log

| Date | Change |
|------|--------|
| (initial) | Plan created based on conversation analysis and code review |
| Phase 1 | Added `primes` field and `modulus` derived value |
| Phase 2 | Correct `next()` algorithm implemented but verification times out |
| Reset | Stripped to barebones, add helpers one-by-one, all helpers GREEN |
| Blocker | `next()` calling ANY private method causes Stainless timeout |

## Current Status (2026-06-03)

### What's Green
- **Barebones SieveSequence** (head, primes, cycle, modulus, apply, first, knownPrimeLimit): ✅
- **Barebones + ALL private helpers** (getAt, addOffset, filterList, sortFiltered, insertSorted, isCoprime, checkCoprime, calculateGaps, pairwiseGaps, rotateAt, splitAt, nextResidueIndex, findResidueIndex, residueAt, residues, generateResidues, expandResidues, expandSingleResidue): ✅
- **All helpers INDIVIDUALLY verified** — they pass when verified in isolation (without `next()` calling them)

### What's Blocked
- **`next()` calling ANY private helper**: ❌ Timeout
- Even the simplest case like `product(List(BigInt(2)))` called from `next()` causes Stainless to timeout (~120s+)
- The bare `next()` that does NOT call any helpers (just constructs a new SieveSequence) passes

### Key Discovery: Private Methods are Inlined
Stainless **inlines private methods** when they are called from public methods in the same class. This means:
- Each private helper's recursive body is expanded into the `next()` verification condition
- Combined with the constructor's VCs (`require(primes.forall(...))`, etc.), this creates a massive VC
- Even a trivial helper like `product` triggers the blowup

### Attempts That Did NOT Work
1. **Making helpers total** (removing `require(sorted.nonEmpty)`): increased VC size, same timeout
2. **`@opaque` annotation** on heavy helpers: caused false compilation errors and didn't prevent timeout
3. **Breaking requires into separate lines**: didn't change the inlining behavior
4. **Removing `require(modulus > 0)` from `next()`**: timeout still occurs

### Path Forward
The hypothesis: **move helpers out of the class** (to companion object or external objects like `DivMod`) so Stainless doesn't inline them. Or keep `next()` body minimal and verify the helper call preconditions separately via lemmas.

## Learnings

### 2026-06-03: Private method inlining in Stainless
Stainless inlines private class methods into public method callers. This is a critical
bottleneck for verification — you CANNOT have a public method call many private helpers,
even if each helper verifies fine in isolation.

**Recommendation:** Place helper functions in companion objects or external "utils" objects.
External methods are NOT inlined the same way. Follow the `DivMod` pattern.

### 2026-06-03: Incremental verification strategy
1. Return to green first (bare minimum code, no helper calls from public methods)
2. Add helper declarations (private methods) one by one — verify they compile
3. Move complex helpers to external objects BEFORE calling them from `next()`
4. Verify after each rearrangement

### 2026-06-03: Require debugging
When a require fails ("precond. (call ... (require 1/2))"):
- Number refers to which require failed (1st, 2nd, etc.)
- Break `require(a && b)` into two separate `require(a); require(b)` for clearer messages
- Add `require` at the innermost function level before adding at caller level

### 2026-06-03: Stainless timeout debugging
If verification is timing out, it's likely a proof stuck in infinite loop.
Debug steps:
1. Comment out new verifications/proofs
2. Check if we're back to the healthy state
3. Recreate proofs one by one to find the culprit
4. Rewrite the problematic proof

Common triggers: `map`, `reduce`, `foldLeft` — these cause Stainless to expand
closures and get stuck. Replace with explicit recursive functions with `decreases` clauses.

### 2026-06-03: Compile without Stainless for fast iteration
`sbt compile` runs Stainless plugin which verifies ALL source files. To compile
quickly without verification: `sbt 'set stainlessEnabled := false' compile`

### 2026-06-03: Stainless List vs Scala List in tests
Test files use Scala types by default. `List(1)` creates `scala.collection.immutable.List[Int]`
not `stainless.collection.List[BigInt]`. Must explicitly:
- `import stainless.collection.List`
- Use `List(BigInt(1))` syntax

### 2026-06-03: Phase 2 completed (fix next() and remove S_1())
- Removed hardcoded S_1() factory - S_1 is now derived via S_0().next()
- Implemented correct next(): expand residues → filter → reconstitute gaps → rotate for head
- Must rotate gaps so gap[0] = gap from head's residue to next residue
- Must compute newHead from next residue value, NOT from rotated gap
- SieveGenerator.nextLevel() now delegates to SieveSequence.next()
- All 8 tests pass (green!)
