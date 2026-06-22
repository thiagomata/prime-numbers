# GapCycle Integration — Review Report

**Reviewed:** 2026-06-08
**Ticket:** `gap-cycle-integration.md`
**Reviewer:** opencode

---

## Overall Assessment

The ticket is well-structured, correctly identifies risks, and follows the project's one-lemma-per-verify discipline. However, there are several issues and blind spots. **The recommended path forward is a side-by-side `CycleSieveSequence` instead of mutating the existing `SieveSequence`.** See Section V for the revised plan.

---

## I. Issues Found

### 1. Phase 3 removal of `checkAllPositive` is unsound (Critical)

The ticket claims at line 74:
> `require(ListUtils.checkAllPositive(integral.cycle.values))` → `checkAllPositive` delegates to `ListBoundUtils.allGreaterThan(list, 0)` — same as GapCycle factory require

This is **wrong**. `checkAllPositive` = `allGreaterThan(list, 0)` = **strictly** positive (> 0). But GapCycle's third constructor require is `checkPositiveOrZero(values.list)` = **non-negative** (>= 0). These are **different predicates**. The GapCycle factory requires `allGreaterThan(list, 0)` to *construct*, but the case class stores `checkPositiveOrZero` as an invariant. If you remove the `checkAllPositive` require from SieveSequence, you lose the > 0 guarantee — you'd only have >= 0.

**Fix:** Either:
- (a) Add a 4th require to GapCycle: `require(ListBoundUtils.allGreaterThan(values.list, BigInt(0)))` — storing the stronger invariant directly, OR
- (b) Keep the `checkAllPositive` require on SieveSequence indefinitely, OR
- (c) Update the ticket to acknowledge that Phase 3 is blocked until GapCycle carries the `allGreaterThan` invariant internally.

### 2. Phase 1c has a proof gap (High)

`nextCycle` currently returns `MemCycle` with `require(CycleUtils.checkPositiveOrZero(gaps))`. The ticket says to wrap it in `GapCycle(nextCycle.values)` in `next()`. But `GapCycle.apply(list)` requires `allGreaterThan(list, BigInt(0))` — strictly stronger than `checkPositiveOrZero`. Since `next()` is `@extern`, this doesn't cause a compile error, but it means **the GapCycle constructed in next() has an unproven assumption** that is weaker than what GapCycle promises. This is technically fine (extern = no verification), but the ticket doesn't acknowledge this mismatch explicitly.

### 3. Phase 2 `allGreaterThan` require is still an assumption (Medium)

The ticket acknowledges this at line 114, but doesn't propose a path forward. The require `allGreaterThan(gaps, 0)` in `nextCycle` is never proved from the pipeline — it remains an axiom. This is the same problem that caused `r3-r5-r12-gaps-nonempty-positive.md` to be superseded. GapCycle doesn't solve it; it just wraps the assumption in a type.

**Suggestion:** Add a note to the ticket that this assumption blocks removing `@extern` from `next()`, and link to a future ticket for pipeline-dependent positivity proof.

---

## II. Blind Spots

### 4. GapCycle.integral vs SieveSequence.integral are different objects

GapCycle creates `integral: CycleIntegral = CycleIntegral(BigInt(0), memCycle)` with `initialValue = 0`. SieveSequence's `integral: CycleIntegral` has `initialValue = primes.head`. The linking require `integral.cycle == gapCycle.memCycle` only constrains the **cycle** field, not the integral as a whole. This is correct behavior, but the ticket doesn't explain *why* only the cycle is linked (and not the integral). A reader might wonder why GapCycle carries an integral at all if it's not the one used by SieveSequence.

**Suggestion:** Add a note explaining that GapCycle's integral serves only its own `cumulativeSum` accessor and is independent from SieveSequence's integral.

### 5. Commented-out requires in SieveSequence are not addressed

Lines 24-30 of `SieveSequence.scala` contain 6 commented-out requires (e.g., `primes.head >= 2`, `isCoprime`, `cycle.sum() == product`). The ticket doesn't mention whether GapCycle integration interacts with any of these. At minimum, the `cycle.sum() == product(primes.tail)` invariant is related to GapCycle's `sum` accessor.

### 6. Phase 2 changes the semantics of `nextCycle`

Changing `nextCycle` from `MemCycle` to `GapCycle` changes the require from `checkPositiveOrZero` to `allGreaterThan`. This is a **semantic change**, not just a type change. The ticket should explicitly note that Phase 2 strengthens the contract, not just the return type.

### 7. Missing `SieveSequenceNextLevel.next()` interaction

The `next()` method at `SieveSequence.scala:48` constructs the new sequence using `SieveSequenceNextLevel.nextCycle(this)`. The ticket mentions updating this in Phase 1c, but doesn't discuss whether `next()` itself should take/return `GapCycle` or remain agnostic.

### 8. No estimate of verify cycles

Each phase should estimate how many verify cycles are needed. Phase 1a (constructor change + linking require) could be 1-3 cycles depending on whether Stainless can handle the `MemCycle` equality. Phase 1b (S_0/S_1 factories) is likely 2 cycles. This helps with planning.

---

## III. Minor Nits

- Line 80: "check `gc.memCycle.values`" — tests should check `gc.memCycle.values` AND the linking invariant `integral.cycle.values == gc.memCycle.values`.
- Line 93: `GapCycle(List(1))` — the factory takes `List[BigInt]`, so this is `GapCycle(List(BigInt(1)))`. Cosmetic but could confuse.
- The ticket doesn't mention whether `SieveSequence.cycle` accessor (line 43: `def cycle: MemCycle = integral.cycle`) should be updated to also expose `gapCycle`.

---

## IV. Summary of Issues

| # | Issue | Severity | Fix |
|---|-------|----------|-----|
| 1 | Phase 3 removal of `checkAllPositive` is unsound (>=0 != >0) | Critical | Update GapCycle to store `allGreaterThan` invariant, or keep `checkAllPositive` require |
| 2 | Phase 1c proof gap (extern + weaker require) | High | Acknowledge explicitly in ticket |
| 3 | Phase 2 `allGreaterThan` still unproven | Medium | Add forward-looking note |
| 4 | GapCycle.integral vs SieveSequence.integral confusion | Low | Add explanatory note |
| 5 | Commented-out requires not addressed | Low | Add note or defer explicitly |
| 6 | Phase 2 is a semantic change, not just type change | Low | Clarify in ticket |
| 7 | Missing verify cycle estimates | Low | Add estimates per phase |

---

## V. Recommended Approach: Side-by-Side CycleSieveSequence

### Why side-by-side instead of mutating in place

Mutating `SieveSequence` creates a messy intermediate state where:
- Both `gapCycle` and `integral` coexist with a linking require that Stainless may struggle to equate
- Phase 1c constructs a GapCycle in `@extern next()` with an unproven `allGreaterThan` assumption (Issue #2)
- Phase 3 tries to remove requires that are strictly stronger than GapCycle's invariants (Issue #1)
- The dual-integral confusion persists (Issue #4)

A side-by-side `CycleSieveSequence` eliminates all of these by starting clean.

### How side-by-side resolves the issues

| Original Issue | How V2 Resolves It |
|---|---|
| #1 (Critical) `checkAllPositive` vs `checkPositiveOrZero` | V2 requires `allGreaterThan(gaps, 0)` from the start. No later removal of a stronger require. |
| #2 (High) Phase 1c proof gap | `nextGapCycle()` takes `allGreaterThan` as an explicit require. Assumption is visible at definition, not hidden in `@extern`. |
| #4 Dual-integral confusion | V2 derives its integral from `gapCycle.memCycle`. One integral, clear ownership. |
| #6 Semantic change disguised as type change | The `allGreaterThan` contract is explicit in `nextGapCycle`'s signature from day one. |

### Issues that persist regardless of approach

| Issue | Why it persists |
|---|---|
| #3 `allGreaterThan(gaps, 0)` still unproven | Fundamental limitation. V2 makes the assumption explicit but doesn't prove it. A future ticket is needed for pipeline-dependent positivity. |
| #5 Commented-out requires | Independent of architecture. |
| #7 Missing verify cycle estimates | Process issue, not architecture. |

### Key insight: SieveUtils is fully decoupled

`SieveUtils` operates on raw `List[BigInt]` — it never references `SieveSequence`. The pipeline functions in `SieveSequenceNextLevel` only read `seq.primes`, `seq.head`, `seq.modulus`, `seq.integral` — all of which V2 would still expose identically. This means:

- **`SieveUtils` needs zero changes**
- **Pipeline functions can be shared** — they only need `primes` and `modulus`
- Only `nextGapCycle` and `next()` need new implementations
- Since `next()` is `@extern`, Stainless never verifies its body — the old V1 code is effectively dead code for verification purposes

### Prerequisite: Strengthen GapCycle first

Before creating V2, GapCycle should be updated to store `allGreaterThan` as an internal invariant (Issue #1 fix-a). This is a 1-cycle change:

```scala
case class GapCycle private (values: MinBoundList) {
  require(values.lowerBound == BigInt(0))
  require(values.list.nonEmpty)
  require(CycleUtils.checkPositiveOrZero(values.list))
  require(ListBoundUtils.allGreaterThan(values.list, BigInt(0))) // NEW
  // ...
}
```

The `checkPositiveOrZero` require becomes redundant (implied by `allGreaterThan(list, 0)`) but keeping it is harmless and avoids a Phase 3 removal discussion.

---

## VI. Revised Ticket: CycleSieveSequence with GapCycle

### Goal

Create `CycleSieveSequence` as a side-by-side alternative to `SieveSequence` that uses `GapCycle` as a first-class field, encoding the strictly-positive gap invariant at the type level from construction onward.

### Prerequisite: Strengthen GapCycle (1 verify cycle)

Add `require(ListBoundUtils.allGreaterThan(values.list, BigInt(0)))` to `GapCycle` case class. Update `GapCycleTest` to confirm. Verify.

### Phase 1 — CycleSieveSequence skeleton (2-3 verify cycles)

Create `src/main/scala/v1/chapter6/seq/sieve/CycleSieveSequence.scala`:

```scala
case class CycleSieveSequence(
  primes: List[BigInt],
  gapCycle: GapCycle
) {
  require(primes.nonEmpty)
  require(ListUtils.checkAllPositive(primes))
  require(ListUtils.checkAllBiggerThanValue(primes, 1))
  require(SieveUtils.assertProductEqualOrBiggerThanElements(primes.tail))
  require(gapCycle.size > 0)  // implied by GapCycle but kept for clarity
  require(gapCycle.memCycle.values.head > BigInt(0))  // gap values > 0
  require(integral.initialValue == primes.head)

  val integral: CycleIntegral = CycleIntegral(primes.head, gapCycle.memCycle)

  def head: BigInt = primes.head
  def modulus: BigInt = SieveUtils.product(primes.tail)
  def cycle: MemCycle = gapCycle.memCycle

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    if (position == 0) head
    else integral(position - 1)
  }
  // ...
}
```

**Cycle 1:** Case class skeleton with requires + `integral` val. Verify.
**Cycle 2:** Add `apply`, `head`, `modulus`, `cycle` accessors. Verify.
**Cycle 3:** Add `S_0()` and `S_1()` factories. Verify.

### Phase 2 — nextGapCycle (2-3 verify cycles)

Add to `SieveSequenceNextLevel` or a new `SieveSequenceNextLevelV2`:

```scala
def nextGapCycle(seq: CycleSieveSequence): GapCycle = {
  val gaps = nextRotatedGaps(seq)  // reuses existing pipeline
  require(gaps.nonEmpty)
  require(ListBoundUtils.allGreaterThan(gaps, BigInt(0)))  // stronger: > 0, not >= 0
  GapCycle(gaps)
}
```

**Cycle 1:** `nextGapCycle` skeleton with requires. Verify.
**Cycle 2:** Add `next(): CycleSieveSequence` (marked `@extern`). Verify.
**Cycle 3:** Add factory methods `S_0V2()`, `S_1V2()`. Verify.

### Phase 3 — Verify equivalence (2-4 verify cycles)

Prove that V2 produces the same primes as V1:

```scala
def assertS0V2MatchesS0(): Boolean = {
  CycleSieveSequence.S_0V2().primes == SieveSequence.S_0().primes
}.holds

def assertS1V2MatchesS1(): Boolean = {
  CycleSieveSequence.S_1V2().primes == SieveSequence.S_1().primes
}.holds
```

**Cycle 1:** `S_0` equivalence. Verify.
**Cycle 2:** `S_1` equivalence. Verify.
**Cycle 3 (optional):** `S_0().next()` equivalence — requires `@extern` so Stainless won't verify the body, but runtime test can confirm.

### Phase 4 — Tests (1-2 verify cycles + test runs)

- `CycleSieveSequenceTest.scala`: construction, apply, next, equivalence with V1
- Run `sbt 'set stainlessEnabled := false' 'testOnly v1.seq.sieve.*'`
- Confirm all V1 tests still pass (no regressions)

### Risks

1. **GapCycle strengthening may need a bridging lemma** — `allGreaterThan(list, 0)` implies `checkPositiveOrZero(list)` is already proved (`assertAllGreaterThanImpliesCheckPositiveOrZero`). Adding the 4th require should be straightforward.
2. **Pipeline sharing** — V2 reuses `SieveSequenceNextLevel` pipeline functions which take `SieveSequence` as parameter. Either: (a) V2 exposes the same interface as V1 so pipeline functions work unchanged, or (b) create thin adapter functions. Option (a) is cleaner.
3. **Stainless case class equality** — `GapCycle` wrapping `MinBoundList` wrapping `List[BigInt]` should be equal by structure, but if Stainless struggles, fall back to comparing `.values` lists.
4. **`allGreaterThan(gaps, 0)` in `nextGapCycle` remains an assumption** — this is the same unsolved problem from `r3-r5-r12-gaps-nonempty-positive.md`. V2 makes it explicit; it doesn't solve it. A future ticket is needed.

### Validation

- `just verify` after each cycle
- Total valid count >= 4240 (current baseline)
- V1 tests unchanged and passing
- V2 tests passing
- `CycleSieveSequence.S_0V2().primes == SieveSequence.S_0().primes` (runtime check)

### Files

| File | Action |
|------|--------|
| `src/main/scala/v1/chapter4/cycle/gap/GapCycle.scala` | Modify: add `allGreaterThan` require |
| `src/main/scala/v1/chapter6/seq/sieve/CycleSieveSequence.scala` | Create: new case class |
| `src/test/scala/v1/seq/sieve/CycleSieveSequenceTest.scala` | Create: tests |
| `src/main/scala/v1/chapter6/seq/sieve/SieveSequenceNextLevel.scala` | Modify: add `nextGapCycle` (or create V2 variant) |
| `src/test/scala/v1/cycle/gap/GapCycleTest.scala` | Modify: add test for strengthened require |

No changes to `SieveUtils.scala`, `SieveSequence.scala`, or existing V1 tests.
