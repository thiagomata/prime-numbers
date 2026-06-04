# Ticket: Prove Every Requirement of Next SieveSequence in Isolation

**Created:** 2026-06-04
**Status:** Planning
**Depends on:** Phase 1-2 of `sieve-sequence-ticket.md` (SieveSequence class exists, S_0 verified, SieveSequenceNextLevel helpers exist)

---

## Working Rules (CRITICAL)

1. **Green to green.** Before making any change, verify the current state is good (compiles + Stainless passes). After any change, verify again. Stainless timeout is a failure — it means the solver is stuck in a verification loop. Never proceed with a red state.

2. **Extreme small changes.** Do the minimal change required to trigger the next verification. Do not add 3 assertions at once — add 1. Make it even simpler in the first version, then improve. If one assertion is `a && b && c`, break it into three separate `assert(a)`, `assert(b)`, `assert(c)` over multiple iterations.

3. **Stop and ask for help.** If you have tried rewriting the same assertion too many times (3+ attempts) without success, STOP. Do not keep trying variations. Ask for guidance.

4. **NEVER git revert. NEVER remove classes.** If you don't know what is happening and the current state seems very strange, ASK FOR HELP.

**Quick verify command:**
```bash
./stainless-dotty-standalone-*/stainless --fail-early=true src/main/scala/v1/seq/sieve/SieveSequence.scala src/main/scala/v1/seq/sieve/SieveUtils.scala src/main/scala/v1/seq/sieve/CycleUtils.scala src/main/scala/v1/seq/sieve/SieveSequenceNextLevel.scala src/main/scala/v1/seq/sieve/properties/SieveSequenceS0Properties.scala src/main/scala/v1/seq/sieve/properties/SieveSequenceProperties.scala
```

**Fast compile without verification:**
```bash
sbt 'set stainlessEnabled := false' compile
```

---

## Context

### What We're Building

A formally verified Sieve of Eratosthenes using Stainless. The core data structure is `SieveSequence` — an infinite sequence of integers coprime to a modulus, represented as a `head`, a list of filtered `primes`, and a `CycleIntegral` of gaps.

### What Happened So Far

1. `SieveSequence` class exists with 13 `require` clauses (invariants) — `SieveSequence.scala:14-26`
2. `S_0` (head=2, primes=[], cycle=[1]) is defined and fully verified — `SieveSequence.scala:43-49`
3. `SieveSequenceNextLevel` object has helper functions for computing the next level:
   - `newHead(seq)` — `seq.apply(1)`, the second element
   - `newPrimes(seq)` — `seq.head :: seq.primes`
   - `survives`, `candidate`, `expansionBlockSize`, etc.
   - Verified assertions: `assertBlockSizePositive`, `assertNewHeadLarger`, `assertFirstCandidateSurvives`, `assertRangeOrdered`, `assertNewPrimesValid`
4. `SieveUtils.scala` contains expand/filter/reconstitute helpers (residues, expandResidues, filterList, calculateGaps, etc.) — all 17+ helpers verify in isolation
5. **Critical blocker**: `next()` calling any private helper causes Stainless timeout (~120s+) because Stainless **inlines private methods** into the caller's verification condition. Combined with the constructor's `require` VCs, this creates massive VCs that cannot be solved.
6. **Just fixed**: Added `assertAllLessThanTransitive` lemma in `CycleUtils.scala` to prove that `allLessThan(list, bound) && bound <= bound2` implies `allLessThan(list, bound2)`. Used this in `assertNewPrimesValid` to prove `allLessThan(head :: old_primes, newHead)`.

### Why This Ticket Exists

The approach of writing `next()` as a monolithic method that calls helpers doesn't work because of the inlining timeout. Instead, we need to:

1. **Prove each `require` of the next sequence in isolation** — as separate `.holds` lemmas
2. **Compose them** into the `next()` method using `assert()` calls on pre-verified lemmas

Since Stainless trusts `.holds` results without re-verifying the lemma body, the composed `next()` stays compact and verifiable.

---

## Goal

For any valid `seq: SieveSequence`, prove that the candidate next sequence:

```scala
nextSeq = SieveSequence(
  head      = seq.apply(BigInt(1)),      // = seq.head + seq.cycle(0)
  primes    = seq.head :: seq.primes,
  integral  = CycleIntegral(newHead, newCycle)
)
```

satisfies **all 13 `require` clauses** of the `SieveSequence` constructor.

Each requirement gets its own lemma. The `next()` method then calls each lemma via `assert(...)` and returns the new sequence.

---

## Architecture: What Is a "Next Sequence"?

### The Expand → Filter → Reconstitute Pipeline

From `tasks/sieve-sequence-refactor-plan.md` and `tasks/talk.md`, the correct `next()` algorithm is:

```
1. EXPAND: Tile the current residues p times with offsets:
   For each residue r, create [r, r+M, r+2M, ..., r+(p-1)M]
   Produces size × p values in [0, M×p)

2. FILTER: Remove multiples of p:
   Keep values where value % p != 0
   Removes exactly size values (1/p of expanded set)
   Leaves size × (p - 1) values

3. RECONSTITUTE: Calculate gaps from filtered residues:
   Sort the filtered values
   Compute differences between consecutive sorted values
   Include wrap-around: (M×p - last) + first
   Sum of gaps = M×p
```

This maps to discrete calculus:
| Step | Operation | Equivalent |
|------|-----------|------------|
| Expand | Domain Extension | ∫ setup |
| Filter | Δ Differentiation | Remove noise |
| Reconstitute | ∫ Integration | Recover gaps |

### The `SieveUtils` Helpers (Already Implemented)

All these exist in `SieveUtils.scala` and verify in isolation:

- `residues(modulus, primes)` — generates valid residues modulo M
- `expandResidues(residues, mod, p)` — tiles residues p times
- `filterList(list, divisor)` — removes elements where `% != 0`
- `sortFiltered(list)` — insertion sort (for Stainless compatibility)
- `calculateGaps(sorted, modulus)` — pairwise gaps + wrap-around
- `isCoprime(value, primes)` — checks `value % p != 0` for all p
- `product(list)` — product of all elements
- `rotateAt(list, index)` — rotate list to start at given index

### The Process for `newCycle`

```scala
val M = seq.modulus                    // product(seq.primes)
val p = seq.head                       // the prime we're filtering by
val currentResidues = residues(M, seq.primes)
val expanded = expandResidues(currentResidues, M, p)
val filtered = filterList(expanded, p)
val sorted = sortFiltered(filtered)
val gaps = calculateGaps(sorted, M * p)

// Rotate gaps so gap[0] = gap between head's new residue and next residue
val headResidueIdx = nextResidueIndex(sorted, 0, newHead % (M * p))
val newGaps = rotateAt(gaps, headResidueIdx)
```

**Key insight from the plan**: The gaps must be rotated so `gap[0]` corresponds to the step from `newHead` to the next element. Without rotation, `gap[0]` would start at residue 0, not at head's position.

---

## The 13 Requirements: Full Breakdown

### Current `SieveSequence` requires (lines 14-26)

```scala
require(head > 0)                                              // R1
require(head >= BigInt(2))                                     // R2
require(integral.cycle.size > 0)                               // R3
require(integral.initialValue == head)                         // R4
require(CycleUtils.checkPositiveOrZero(integral.cycle.values)) // R5
require(SieveUtils.checkAllPositive(primes))                   // R6
require(SieveUtils.assertProductEqualOrBiggerThanElements(primes)) // R7
require(v1.seq.sieve.CycleUtils.allLessThan(primes, head))     // R8
require(SieveUtils.isCoprime(head, primes))                    // R9
require(integral.cycle.sum() == SieveUtils.product(primes))    // R10
require(integral.cycle(BigInt(0)) < head)                      // R11
require(integral.cycle.values.head > BigInt(0))                // R12
require(SieveUtils.isCoprime(head + SieveUtils.product(primes), primes)) // R13
```

Now for the next sequence, substitute:
- `head` → `newHead = seq.apply(1) = seq.head + seq.integral.cycle(0)`
- `primes` → `newPrimes = seq.head :: seq.primes`
- `integral` → `newIntegral = CycleIntegral(newHead, newCycle)` where `newCycle` is the new MemCycle

---

### R1: `newHead > 0` ✅ TRIVIAL

**What we know from `seq`:**
- `seq.head > 0` (R1 for current seq)
- `seq.integral.cycle.values.head > 0` (R12 for current seq), so `cycle(0) > 0`

**Proof:**
`newHead = seq.head + cycle(0) > 0 + 0 = 0`

**Dependencies:** `assertNewHeadLarger` (already .holds)
**Priority:** Trivial, combine with R2
**Lemma:** `assertNewHeadPositive(seq)` 

---

### R2: `newHead >= 2` 🟡 SIMPLE

**What we know:**
- `seq.head >= 2` (R2)
- `cycle(0) > 0` (R12)

**Proof:**
`newHead = seq.head + cycle(0) >= 2 + 1 = 3 >= 2`

**Dependencies:** `assertNewHeadLarger`
**Priority:** Simple, combine with R1
**Lemma:** `assertNewHeadAtLeastTwo(seq)` or merge with R1

---

### R3: `newCycle.size > 0` 🟡 NEEDS CONSTRUCTION

**What we need to prove:** The new cycle (computed from expand → filter → reconstitute) is non-empty.

**Hyphothesis / Reasoning:**
The expansion produces `|R_old| × p` values (where `|R_old|` is the number of residues in the old sequence). After filtering, `|R_old|` values are removed (those where `value % p == 0`). Since `|R_old| >= 1` (the old cycle is non-empty by R3), and `p >= 2` (by R2), the filtered set has at least `1 × (2 - 1) = 1` values, so `newCycle.size >= 1 > 0`.

**Actually simpler:** The old cycle has at least 1 value (gap). The expansion produces at least `1 × p >= 2` values. At most 1 value is removed (since `|R_old| = 1` only happens at S_0 where residues = [0]). After filtering, at least `2 - 1 = 1` values remain.

But this is only obvious for S_0 → S_1. For general S_k → S_{k+1}, we need:
- `old_residues.count = old_cycle.size >= gap_count`
- Actually: number of residues = number of gaps = size of cycle
- So `size_old >= 1` (from R3)
- After expansion: `size_old × p` values
- After filtering: `size_old × (p - 1)` values (removing exactly `1/p` of the values)
- This equals `size_old × (p - 1) >= 1 × (2 - 1) = 1`

**Warning:** This argument assumes filtering removes exactly `size_old` values (= exactly 1/p of the total). This relies on the CRT uniform distribution property, which is the **middle-term goal** (Phase 4 of the plan). For the immediate requirement, we might need a weaker bound or prove the general case from the structure.

**Dependencies:** The expand → filter → reconstitute pipeline. This lemma must come after the new cycle construction is defined.
**Lemma:** `assertNewCycleNonEmpty(seq)`

---

### R4: `newIntegral.initialValue == newHead` ✅ BY CONSTRUCTION

We set `initialValue = newHead` when constructing `CycleIntegral(newHead, newCycle)`. No proof needed — this is a value assignment.

However, for Stainless to see this in `next()`, we need `next()` to explicitly construct it:
```scala
val newIntegral = CycleIntegral(newHead, newCycle)
assert(newIntegral.initialValue == newHead)
```

**Priority:** Immediate (trivial)
**Lemma:** None needed

---

### R5: `checkPositiveOrZero(newCycle.values)` 🟡 NEEDS GAP POSITIVITY PROOF

**What it means:** All gap values in the new cycle must be >= 0.

**Hyphothesis / Reasoning:**
The gaps come from `calculateGaps(sorted, M*p)`, which computes differences between consecutive sorted residues. Since the residues are sorted (by `sortFiltered`), each gap = `residue[i+1] - residue[i] >= 0`. The wrap-around gap = `(M*p - last) + first`. Since `last < M*p` and `first >= 0`, this is also > 0.

**Potential issues:**
- `sortFiltered` correctness — is it a true sort? (Yes, insertion sort verified in isolation)
- Duplicate residues? Should not happen since all residues in [0, M*p) are unique (different mod classes)
- Wrap-around: `(M*p - last) + first` > 0 because `last < M*p` (all residues < modulus) and `first > 0` (since 0 is filtered out when 0 is a multiple of p... wait, not necessarily).

Actually, wait. The first residue could be 0 if 0 is coprime to all primes... but 0 % p = 0 for any p, so 0 is never coprime to any prime. So residue 0 is never in the filtered set. Thus first > 0 and `(M*p - last) + first > 0`.

Actually, we need to consider: is 0 in the residues list? Let me check. `residues(modulus, primes)` generates residues in [0, modulus) that are coprime to primes. Since 0 % p = 0 for any p, 0 is NOT coprime to any non-empty list of primes. So for S_1 onward, 0 is not a residue. For S_0 (primes = []), all numbers in [0, 2) are residues: [0, 1]. But for S_0 → S_1 transition, we filter by 2, removing 0, so 0 is still excluded from the new cycle.

So all gaps are strictly positive (> 0), which is stronger than `checkPositiveOrZero` (>= 0).

**Dependencies:** `calculateGaps` correctness, `sortFiltered` correctness, `filterList` correctness
**Lemma:** `assertNewGapsNonNegative(seq)` or `assertNewGapsPositive(seq)`

---

### R6: `checkAllPositive(newPrimes)` ✅ TRIVIAL

**What we know:**
- `seq.head >= 2 > 0` (R1, R2)
- All `seq.primes` are positive (R6 for current seq)

**Proof:** All elements of `seq.head :: seq.primes` are > 0.

**Dependencies:** None
**Priority:** Trivial
**Lemma:** `assertNewPrimesPositive(seq)` — so simple it might be inline

---

### R7: `assertProductEqualOrBiggerThanElements(newPrimes)` 🟡 NEEDS PRODUCT LEMMA

**This lemma requires `checkAllBiggerThanOne(primes)` as its own require.**

**What we need to prove:** For `newPrimes = seq.head :: seq.primes`:
- `product(newPrimes) >= 1`
- `product(newPrimes) >= seq.head`
- `product(newPrimes) >= each element in seq.primes`

**What we know:**
- `assertProductEqualOrBiggerThanElements(seq.primes)` holds (R7 for current)
- This means `oldProduct >= each_old_prime` and `oldProduct >= 1`
- `seq.head > 1` (>= 2, so > 1)
- `newProduct = seq.head × oldProduct`

**Proof sketch:**
Since `oldProduct >= 1` and `seq.head > 1`:
- `newProduct = seq.head × oldProduct >= seq.head` (since `oldProduct >= 1`)
- `newProduct >= oldProduct >= each_old_prime` (by transitivity)
- `newProduct >= 1` (since both factors >= 1)

**Need:**
1. Show `checkAllBiggerThanOne(newPrimes)` — i.e., `seq.head > 1` (true since >= 2) and all old primes > 1 (from R7's own require chain)
2. Use `assertValueNeverDecreases(seq.head, oldProduct)` to show `seq.head × oldProduct >= seq.head`

**Dependencies:** `assertValueNeverDecreases`, `assertProductEqualOrBiggerThanElements` on old seq
**Lemma:** `assertNewProductEqualOrBiggerThanElements(seq)`

---

### R8: `allLessThan(newPrimes, newHead)` ✅ DONE

**What it proves:** Every prime in `seq.head :: seq.primes` is strictly less than `newHead`.

**Proof:**
- `seq.head < newHead` — from `assertNewHeadLarger` (already .holds)
- `allLessThan(seq.primes, seq.head)` — from R8 on current seq
- Transitivity: since each prime < seq.head < newHead, each prime < newHead
- The `assertAllLessThanTransitive` lemma (just added to `CycleUtils.scala`) bridges this

**Status:** Already verified via `assertNewPrimesValid` in `SieveSequenceNextLevel.scala:74-84`. ✓

---

### R9: `isCoprime(newHead, newPrimes)` 🔴 HARD — CENTRAL BLOCKER

**What it proves:** `newHead` is not divisible by any prime in `newPrimes`.

`newPrimes = seq.head :: seq.primes`, so we must prove:
1. `newHead % seq.head != 0` — i.e., `newHead` is not a multiple of `seq.head`
2. `isCoprime(newHead, seq.primes)` — `newHead` is not a multiple of any old prime

**Part 1:** Already proved by `assertFirstCandidateSurvives(seq)` which shows `Calc.mod(seq(1), seq.head) != 0`.

**Part 2: The hard part.** We need `newHead % p != 0` for all `p` in `seq.primes`.

`newHead = seq.head + seq.cycle(0)`

**What we know:**
- `SieveUtils.isCoprime(seq.head, seq.primes)` — R9 for current seq
- `SieveUtils.isCoprime(seq.head + product(seq.primes), seq.primes)` — R13 for current seq
- But neither directly tells us about `seq.head + cycle(0)`

**Why it should be true:**
The sequence S_k generates exactly the integers coprime to `M = product(primes)`. By construction, every element `seq.apply(i)` for any i >= 0 should be coprime to all primes in `seq.primes`. In particular, `newHead = seq.apply(1)` is the second element, so it should be coprime.

**The problem:** This "every element is coprime" property is NOT currently an invariant of `SieveSequence`. We have R9 (head is coprime) and R13 (head + M is coprime), but not a general lemma for all positions.

**How to prove it:**
We need to show that for any prime p in `seq.primes`, and any position i >= 0:
`seq.apply(i) % p != 0`

From the definition of `apply`:
- `seq.apply(0) = head` — coprime by R9
- `seq.apply(1) = seq.integral(0) = cycle(0) + head`
- `seq.apply(n) = seq.integral(n-1)`

We know the `integral.cycle.sum() == product(primes)` (R10). So the cycle sum is M, which is divisible by every p in primes.

But that alone doesn't prove each individual element is coprime. We need the stronger property: the residues modulo M are exactly the numbers coprime to M.

**Approaches:**

**A) Add residues as an explicit field.** This makes coprimality structural. The `SieveSequence` would have:
```scala
case class SieveSequence(
  head: BigInt,
  primes: List[BigInt],
  residues: List[BigInt],  // NEW: residues mod M that are coprime to M
  integral: CycleIntegral
)
```
Then R9 would be: `residues.forall(r => isCoprime(r, primes))` and the `apply` function would be `head + integral * M + residue`.

**B) Prove a general coprimality lemma.** That `∀i ≥ 0, isCoprime(seq.apply(i), seq.primes)`. This would require:
- Knowing the structure of the integral (gaps from residues)
- Proving by induction on position using the cycle sum = M property
- This essentially re-derives the residue structure from the gaps

**C) Prove just what we need.** Instead of proving for all i, prove specifically for `i = 1` (newHead). This might be easier:
- `newHead = head + cycle(0)`
- `head` is coprime to primes
- `cycle(0) < head` (R11)
- Need to show `head + cycle(0) ≡ something (mod p)` that is ≠ 0

But this is equivalent to showing `cycle(0) % p != -head % p`, which doesn't help without knowing the residue structure.

**Recommendation:** Approach A (add residues field) is the most principled. The article `sieve-sequence.md` already describes the SieveSequence in terms of residues. The current code derives residues from the modulus (via `SieveUtils.residues`), but storing them makes the invariant structural.

**Dependencies:** Expand → filter → reconstitute pipeline OR residues field
**Lemma:** `assertNewHeadCoprime(seq)` — depends on how we solve this

---

### R10: `newCycle.sum() == product(newPrimes)` 🔴 HARD — CENTRAL INVARIANT

**What it proves:** The sum of all gaps in the new cycle equals the new modulus.

`newProduct = product(newPrimes) = product(seq.head :: seq.primes) = seq.head × product(seq.primes) = p × M`

Where `p = seq.head` and `M = product(seq.primes)`.

So we need: `sum(newCycle) == p × M`

**Why it should be true:**
The expand → filter → reconstitute pipeline preserves the sum:
1. Expansion: Each of p tiles sums to M (the modulus). Total sum before filtering = `p × M`.
2. Filtration: Removing values changes the sorted order, but the gaps between remaining values still tile [0, p×M) exactly once. The gaps + wrap-around sum to p×M.
3. This is essentially: "the residues modulo p×M are exactly the numbers in [0, p×M) coprime to p and to all primes in seq.primes."

**Proof strategy:**

The filtered residues partition [0, p×M) into intervals. The gaps are the lengths of these intervals. Since the intervals exactly cover [0, p×M), the sum of gap lengths = p×M.

More formally:
- Let `R' = [r_0, r_1, ..., r_{k-1}]` be the filtered, sorted residues (0 < r_0 < r_1 < ... < r_{k-1} < p×M)
- Gaps: `g_i = r_{i+1} - r_i` for `0 <= i < k-1`, and `g_{k-1} = (p×M) - r_{k-1} + r_0`
- Sum of gaps: `(r_1 - r_0) + (r_2 - r_1) + ... + (r_{k-1} - r_{k-2}) + ((p×M) - r_{k-1} + r_0)`
- This telescopes to: `p×M`

This is a telescoping sum — always true regardless of the values of r_i, as long as they're sorted and in [0, p×M).

**What we need to prove:**
1. `calculateGaps(sorted, p*M)` produces gaps whose sum equals `p*M`
2. The filtered residues are all in [0, p×M) and sorted

**Existing code that does this:** `SieveUtils.calculateGaps` already exists and verifies in isolation. We need a lemma about its sum-preserving property.

**Sub-lemma needed:** `assertCalculateGapsSum(sorted, modulus)`:
```scala
sum(calculateGaps(sorted, modulus)) == modulus
```
Given `sorted` is non-empty, sorted ascending, and all values in [0, modulus).

**Dependencies:** `calculateGaps` sum lemma, `sortFiltered` correctness, `expandResidues` produces values in range
**Lemma:** `assertNewCycleSumEqualsProduct(seq)`
**Sub-lemma:** `assertCalculateGapsSum(sorted, modulus)` — telescoping proof

---

### R11: `newCycle(0) < newHead` 🟡 NEEDS FIRST GAP BOUND

**What it proves:** The first gap in the new cycle is strictly less than the new head.

`newCycle(0)` = first gap = difference between first and second filtered residue (after rotation to start at newHead's position).

After rotation, the first gap is the distance from `newHead` to the next element in the filtered sequence. Since the next element is at least `newHead + 1` (gaps are positive), and the new cycle wraps at `p×M`, the first gap must be at least 1 and at most... well, it could be large.

But we need it to be `< newHead`. Why is this true?

**Reasoning:**
In the old sequence, `cycle(0) < head` (R11 for current seq). After filtering by p = head, the gaps between surviving elements can change. But the first gap in the new sequence is determined by the distance from `newHead` to the next surviving element.

Actually, wait. After filtering, some elements are removed. The gaps may grow. For example, in S_0 → S_1:
- S_0: head=2, cycle=[1]. Here cycle(0)=1 < 2. ✓
- S_1: head=3, cycle=[2]. Here cycle(0)=2 < 3. ✓

For S_1 → S_2:
- S_1: head=3, cycle=[2]. Here cycle(0)=2 < 3. ✓
- S_2: head=5, cycle=[4,2]. Here cycle(0)=4 < 5. ✓

For S_2 → S_3:
- S_2: head=5, cycle=[4,2]. Here cycle(0)=4 < 5. ✓
- S_3: head=7, cycle=[6,4,2,4,2,4,6,2]. Here cycle(0)=6 < 7. ✓

This seems to always hold numerically. The first gap is always the distance to the next candidate, which should be < the head.

**Why it holds:**
The initial residues include residue 0? No — residue 0 is never coprime (0 mod anything = 0).

Actually, let me think about it differently. The old cycle produces: head, head+gap[0], head+gap[0]+gap[1], ...

After filtering, we keep only those where `(head + accumulated_gaps) % p != 0`. The new head is `head + gap[0]`. The first gap of the new cycle is the distance from `newHead` to the next surviving element.

We know that within a block of size p (the old head), there is exactly one multiple of p. The old cycle has `cycle(0) < head`. After expansion to size `p × M`, and filtering, the first gap between surviving residues should be < head... but I'm not 100% sure of the general proof.

**Hypothesis:** This might actually be a property that follows from the construction rather than an invariant that needs separate proof. We should verify it empirically first (write unit tests for S_0→S_1, S_1→S_2, S_2→S_3) and then attempt to prove it generally.

**Dependencies:** Expand → filter → reconstitute pipeline, rotation logic
**Lemma:** `assertNewFirstGapLessThanHead(seq)`

---

### R12: `newCycle.values.head > 0` 🟡 SAME AS R5

Same as R5 — all gaps are positive. The first gap specifically is > 0 because it represents a non-zero distance. Follows from R5.

**Dependencies:** Same as R5
**Lemma:** Can share with R5

---

### R13: `isCoprime(newHead + product(newPrimes), newPrimes)` 🟡 MODULAR ARITHMETIC

**What it proves:** `newHead + M_new` is coprime to all primes in `newPrimes`.

Where `M_new = product(newPrimes) = p × M`.

**Reasoning:**
For any prime q in `newPrimes = p :: old_primes`:
- `(newHead + p×M) % q = (newHead % q + (p×M) % q) % q`
- Since `q` divides `p×M` (because q is either p or a factor of M), `(p×M) % q = 0`
- So `(newHead + M_new) % q = newHead % q`
- If `newHead % q != 0` (from R9), then `(newHead + M_new) % q != 0`

So R13 follows directly from R9 plus the fact that `M_new` is a multiple of every prime in `newPrimes`.

**Proof sketch:**
```scala
def assertNewHeadPlusProductCoprime(seq: SieveSequence): Boolean = {
  assert(assertNewHeadCoprime(seq))  // R9 for next seq
  // For each q in newPrimes:
  //   M_new % q == 0 (by definition of product)
  //   (newHead + M_new) % q == newHead % q != 0
  SieveUtils.isCoprime(newHead + product(newPrimes), newPrimes)
}.holds
```

We need a lemma: `assertMultipleIsZeroMod(divisor, multiple)`:
```scala
// If d divides m, then m % d == 0
// But we have m = product(list) and d is in the list, so d | m
(prod % d) == 0
```

**Dependencies:** R9 (assertNewHeadCoprime), lemma about product being multiple of its factors
**Lemma:** `assertNewHeadPlusProductCoprime(seq)`

---

## Dependency Graph

```
                              ┌─────────────────────────┐
                              │  Expand → Filter →       │
                              │  Reconstitute Pipeline   │
                              │  (SieveUtils helpers)    │
                              └──────────┬──────────────┘
                                         │
              ┌──────────────────────────┼──────────────────────┐
              │                          │                      │
              ▼                          ▼                      ▼
   ┌─────────────────────┐  ┌─────────────────────┐  ┌─────────────────────┐
   │ assertNewCycleNonEmpty│  │ assertNewGapsPositive│  │ assertCalculateGaps │
   │ (R3)                 │  │ (R5, R12)           │  │ Sum (R10 helper)    │
   └─────────────────────┘  └─────────────────────┘  └──────────┬──────────┘
                                                              │
                                         ┌────────────────────┘
                                         ▼
                              ┌─────────────────────┐
                              │ assertNewCycleSum   │
                              │ EqualsProduct (R10) │
                              └──────────┬──────────┘
                                         │
              ┌──────────────────────────┼──────────────────────┐
              │                          │                      │
              ▼                          ▼                      ▼
   ┌─────────────────────┐  ┌─────────────────────┐  ┌─────────────────────┐
   │ assertNewHeadCoprime │  │ assertNewFirstGap   │  │ assertNewHeadPlus    │
   │ (R9)                 │  │ LessThanHead (R11)  │  │ ProductCoprime (R13) │
   └──────────┬──────────┘  └─────────────────────┘  └─────────────────────┘
              │                                                    ▲
              └────────────────────────────────────────────────────┘

Trivial (no deps):  R1, R2, R6, R7, R8 (done)
By construction:    R4
Depends on pipeline: R3, R5, R9, R10, R11, R12, R13
```

---

## Execution Order (Recommended)

### Step 0: Pre-existing (already done)
- [x] `assertNewHeadLarger` — newHead > head
- [x] `assertFirstCandidateSurvives` — first candidate not multiple of head
- [x] `assertRangeOrdered` — expansion range valid
- [x] `assertBlockSizePositive` — block size > 0
- [x] `assertNewPrimesValid` — includes R8 (allLessThan)
- [x] `assertAllLessThanTransitive` lemma in CycleUtils

### Step 1: Trivial requirements (no pipeline needed)
- [x] `assertNewHeadAtLeastTwo` — R1 + R2 (newHead >= 2, hence > 0)
- [x] `assertNewPrimesPositive` — R6
- [x] `assertNewPrimesAllBiggerThanOne` — helper for R7 (proves newPrimes all > 1)
- [x] `assertNewProductEqualOrBiggerThanElements` — R7

### Step 2: Pipeline construction (define the new cycle)
- [ ] Define `nextCycle(seq): MemCycle` — the expand → filter → reconstitute pipeline
  - This is the core of `next()` and the main technical work
  - Uses `SieveUtils.residues`, `expandResidues`, `filterList`, `sortFiltered`, `calculateGaps`, `rotateAt`
  - Should be a method in `SieveSequenceNextLevel` or `SieveUtils`
  - **Must avoid the inlining trap** — keep helpers external, use `assert()` calls
- [ ] Unit test: `nextCycle(S_0) == MemCycle(List(2))` (S_0 → S_1)
- [ ] Unit test: `nextCycle(S_1) == MemCycle(List(4, 2))` (S_1 → S_2)

### Step 3: Pipeline-dependent requirements
- [ ] `assertNewCycleNonEmpty` — R3
  - Proof: expansion size = size_old × p, after filter = size_old × (p-1) >= 1 × 1 = 1
- [ ] `assertNewGapsPositive` — R5, R12
  - Proof: gaps from sorted, unique residues are strictly positive
  - Sub-lemma: gaps are positive when computed from sorted unique values
- [ ] `assertCalculateGapsSum` — helper for R10
  - Proof: telescoping sum of sorted residues + wrap-around = modulus
  - Key sub-lemma: `sum(calculateGaps(sorted, M)) == M` for sorted residues in [0, M)
- [ ] `assertNewCycleSumEqualsProduct` — R10
  - Depends on `assertCalculateGapsSum`
  - The new modulus = p × M, the gaps sum to this
- [ ] `assertNewFirstGapLessThanHead` — R11
  - May require residue structure to prove

### Step 4: Coprimality requirements (hardest)
- [ ] `assertNewHeadCoprime` — R9
  - This is the central challenge
  - Option A: Add residues field to SieveSequence
  - Option B: Prove general coprimality lemma for all sequence elements
  - Option C: Prove just for newHead specifically
- [ ] `assertNewHeadPlusProductCoprime` — R13
  - Depends on R9
  - Sub-lemma: `assertFactorOfProduct(list, x)` — if x is in list, product(list) % x == 0

### Step 5: Compose into `next()`
- [ ] Implement `next()` in `SieveSequence` calling all lemmas via `assert()`
- [ ] Verify `next()` passes Stainless without timeout
- [ ] Unit test: `S_0().next().head == 3`
- [ ] Unit test: `S_0().next().primes == List(2)`
- [ ] Unit test: `S_0().next().cycle.values == List(2)`
- [ ] Unit test: `S_0().next().next().head == 5`

---

## Lessons Learned (Carried Forward)

### From `summary-2026-06-02.md`:
1. **Avoid `forall` over `BigInt`** — causes unbounded unfolding, timeouts
2. **Use `assert()` chains** to build lemmas incrementally
3. **Recursion with `decreases(list.size)`** over `BigInt`
4. **Reuse already-proved properties** — don't re-prove
5. **Avoid `forall` over infinite domains**

### From `sieve-sequence-refactor-plan.md`:
6. **Stainless inlines private methods** — NEVER call private helpers from public methods that have VCs. Use external objects or companion object methods.
7. **Test before Stainless** — unit tests first, verification second
8. **Compile without verification for fast iteration**: `sbt 'set stainlessEnabled := false' compile`
9. **`@opaque` as last resort** — only if solver truly cannot handle otherwise
10. **Verify transitions, not infinite sequences** — prove `invariant(S_k) ==> invariant(next(S_k))`
11. **Symbolic reasoning over concrete lists** — compare variables (p, M, size), not list contents
12. **Break `require(a && b)`** into separate requires for clearer error messages
13. **`sbt compile` runs Stainless which verifies ALL source files** — use `sbt 'set stainlessEnabled := false' compile` to skip

### From this ticket:
14. **Compose lemmas, don't inline** — proven `.holds` lemmas can be called via `assert()` in `next()` without re-verification. This is the key to avoiding timeouts.
15. **Prove each require in isolation** — one lemma per requirement, then compose

---

## Verification Strategy

### Per Lemma
1. Write the lemma as a `.holds` function in the appropriate properties object
2. Add `require` clauses for all premises from `seq: SieveSequence`
3. Use `assert()` to reference other lemmas rather than re-proving
4. Verify with Stainless

### Per Requirement
1. Create a function `assertReqN(seq: SieveSequence): Boolean` that asserts the requirement holds for the next sequence derived from `seq`
2. This function may call helper lemmas (pipeline construction, coprimality, etc.)
3. If a requirement depends on the new cycle (R3, R5, R10, R11, R12), the function must construct or reference the new cycle

### For `next()` (Step 5)
```scala
def next(): SieveSequence = {
  // Compute new components
  val newHead = this.apply(BigInt(1))
  val newPrimes = this.head :: this.primes
  val newCycle = SieveSequenceNextLevel.nextCycle(this)
  val newIntegral = CycleIntegral(newHead, newCycle)

  // Assert ALL requirements via pre-verified lemmas
  assert(assertNewHeadPositive(this))
  assert(assertNewHeadAtLeastTwo(this))
  assert(assertNewCycleNonEmpty(this))
  assert(newIntegral.initialValue == newHead)
  assert(assertNewGapsPositive(this))
  assert(assertNewPrimesPositive(this))
  assert(assertNewProductEqualOrBiggerThanElements(this))
  assert(assertNewPrimesValid(this))          // R8
  assert(assertNewHeadCoprime(this))          // R9
  assert(assertNewCycleSumEqualsProduct(this)) // R10
  assert(assertNewFirstGapLessThanHead(this)) // R11
  // R12 covered by assertNewGapsPositive
  assert(assertNewHeadPlusProductCoprime(this)) // R13

  SieveSequence(newHead, newPrimes, newIntegral)
}
```

Each `assert(...)` call uses a pre-verified `.holds` lemma. Stainless trusts the result without re-verifying the lemma body, keeping the VC small.

---

## Open Questions & Hypotheses

### Q1: Residues field — do we add it?
The article `sieve-sequence.md` describes `SieveSequence` with residues. The current code computes residues on-the-fly via `SieveUtils.residues(modulus, primes)`. Adding residues as a field would:
- **Pro:** Make coprimality (R9) structural — `residues.forall(r => isCoprime(r, primes))`
- **Pro:** Simplify R11 and R10 proofs
- **Con:** Another field to maintain, another require to prove for next level
- **Hypothesis:** Worth it. The invariant "every element is coprime to primes" is the core property of the sieve and should be explicit.

### Q2: Is R11 (first gap < head) always true?
Empirically it holds for S_0→S_1→S_2→S_3. The first gap in the new sequence is `newCycle(0) = gap from newHead to next surviving candidate`. In the old sequence, `cycle(0) < head`. After filtering by p=head, some intermediate candidates are removed, which could potentially make the first gap larger. But within any block of p consecutive elements, exactly one is removed (the multiple of p). The first block starts at head, so the first removed element is at head + k×p for some k... Actually wait.

In the old sequence, the elements are: head, head+gap[0], head+gap[0]+gap[1], ...
The new head is head+gap[0]. The next candidate after newHead is head+gap[0]+gap[1] (if not filtered).
The filtering removes elements where `element % p == 0`. The first such element could be anywhere.
The first gap of the new sequence is the distance from newHead to the next surviving element.

Since within any block of size p in the old sequence, exactly one element has residue 0 mod p (by uniform distribution), and the old gaps are < head (R11 ensures cycle(0) < head but doesn't guarantee all gaps < head)... hmm, but for the first gap specifically, we know `cycle(0) < head` (R11 for current seq).

After filtering, if the first few elements are all survivors, the first gap stays small. But if element(s) after newHead are removed, gaps merge and could grow. However, since the removed density is 1/p and gaps are approximately M/|R| on average, the merged gap could still be < head.

**Hypothesis:** This is provable from the structure but may require the residues. Worth testing empirically first.

### Q3: Can we avoid the full pipeline for some requirements?
Some requirements (R1, R2, R6, R7, R8, R13) don't depend on the new cycle at all. They can be proved immediately without implementing the pipeline.

R9 might be provable without the full pipeline if we add a residues field or prove the general coprimality property.

R3, R5, R10, R11, R12 depend on the new cycle and cannot be proved until the pipeline is defined.

### Q4: How to handle the "newCycle" MemCycle constructor requires?
`MemCycle.apply(values)` requires `values.nonEmpty` and `checkPositiveOrZero(values)`. We need to prove both for the new gaps. These correspond to R3 and R5. If we prove R3 and R5 first, the MemCycle constructor passes.

### Q5: Does the `nextCycle` function itself cause timeout?
The `nextCycle` function will call multiple `SieveUtils` helpers (external object methods). External methods are NOT inlined the same way as private methods (per the plan's discovery). So `nextCycle` should verify without timeout. If it does time out, break it into smaller lemmas.

---

## Test Cases (to write before verification)

### S_0 → S_1
```
Input:  head=2, primes=[], cycle=[1]
Output: head=3, primes=[2], cycle=[2]
```

### S_1 → S_2
```
Input:  head=3, primes=[2], cycle=[2]
Output: head=5, primes=[3,2], cycle=[4,2]
```

### S_2 → S_3
```
Input:  head=5, primes=[3,2], cycle=[4,2]
Output: head=7, primes=[5,3,2], cycle=[6,4,2,4,2,4,6,2]
```

### Verify each transition satisfies all 13 requires
```
test("S_0(). S_0.next() satisfies all 13 requires")
test("S_0.next() satisfies all 13 requires")
test("S_0.next().next() satisfies all 13 requires")
```

---

## References

- `SieveSequence.scala` — main class with 13 requires (lines 14-26)
- `SieveSequenceNextLevel.scala` — transition helpers
- `SieveUtils.scala` — expand/filter/reconstitute utilities
- `CycleUtils.scala` — list predicates (including new `assertAllLessThanTransitive`)
- `CycleIntegral.scala` — integral over cycles
- `MemCycle.scala` — cycle storage
- `articles/sieve-sequence.md` — full formal treatment
- `tasks/sieve-sequence-refactor-plan.md` — refactoring plan with inlining discovery
- `tasks/talk.md` — discrete calculus approach
- `tickets/summary-2026-06-02.md` — learnings
- `tickets/sieve-sequence-ticket.md` — general ticket
