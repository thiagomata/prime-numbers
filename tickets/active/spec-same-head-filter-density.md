# Spec Same-Head Filter Density

**Created:** 2026-07-13
**Updated:** 2026-07-13
**Status:** In progress
**Depends on:** `next-gaps-size-closed-form.md` (active, density/counting background), `m-interval-density-and-sieve-sequence-v2.md` (active, article framing), `sieve-sequence-proof.md` (active, spec proof context)

## Related Tickets

- `tickets/active/next-gaps-size-closed-form.md` — prior closed-form `|G'| = |G| * (h - 1)` ticket. It correctly identifies density as the hard step, but its route goes through `nextResidues -> nextExpanded -> nextFiltered` and then tries to connect to gaps. This ticket deliberately restarts from `SpecSieveSequence` so helpers remain attached to the end theorem.
- `tickets/active/m-interval-density-and-sieve-sequence-v2.md` — article/proof framing for the `h * M` expanded interval. Useful warning: the one-over-head count is exact over the expanded interval of length `h * M`, not over a single current interval of length `M`.
- `tickets/active/sieve-sequence-proof.md` — spec sequence proof work. Reuse its lessons about builder order, list sizes before `.apply`, and avoiding opaque recursive-builder equality.
- `tickets/trash/superseded/independent-next-cycle.md` — superseded but important trap log. Do not revive its bespoke cycle/survivor proof universe. Only mine it for warnings, especially the false `nextSeq.head.value == head.value` contract shape.
- `LEARNINGS.md` sections 18.6 and 18.8 — critical warnings about confusing `nextSeq.head.value` with `nextSeq.filterValues.head`, and about precondition migrations needing all callees/callers/dependents together.

## Goal

Prove the size/count transition from the spec sequence first, without using the cycle pipeline as the primary proof object.

The intended end-game theorem is:

```text
current period size = period
same-head extended-filter period size = period * (head - 1)
```

where the same-head extended-filter sequence has the same starting head as `seq`, but adds the current head as a new front filter:

```text
old filters:       seq.filterValues
extended filters:  seq.head.value :: seq.filterValues
```

This ticket explicitly postpones the real `seq.next` head change and any rotation/cycle proof. The first objective is only the filter-count theorem:

```text
Adding the current head as a filter removes exactly 1/head of the values
accepted over the expanded interval [head, head + head * M).
```

## Current State

- `SpecSieveSequence` is the source of truth: it scans all consecutive integers and emits those satisfying `accepts`.
- `accepts(value)` is a gate over ordinary integer candidates, not the definition of the candidate universe.
- Existing private same-head lemmas in `SpecSieveSequence` already express the desired filter relationship for a same-head extended-filter sequence:
  - `assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple`
  - `assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple`
  - `assertRejectedByNextWhenNewHeadMultiple`
- Those lemmas currently require `nextSeq.head.value == head.value`. That is appropriate for a same-head extended-filter proxy, but wrong for actual `seq.next`.
- Actual `seq.next` has:

```text
seq.next.head.value        = next prime
seq.next.filterValues.head = seq.head.value
```

- Chapter 2 has raw interval density lemmas:
  - `ConsecutiveIntegers.countModZeroEqualsM`
  - `ConsecutiveIntegers.densityForDivisor`
  - `ConsecutiveIntegers.densityPreservedAfterFiltering`
  - `ConsecutiveIntegers.densityForPrimeList`
- The missing proof is not repeated-list size. It is the counted filtering theorem that survives prior filters and removes exactly one-over-head from the expanded candidate interval.

## Expected State

At completion of this ticket, there should be a verified spec-level theorem or a clearly documented blocker.

Preferred verified theorem shape:

```scala
def assertSameHeadExtendedFilterPeriodSize(
  period: BigInt,
  extendedPeriod: BigInt
): Boolean = {
  require(period > 0)
  require(apply(period) == head.value + tailPrimorial)
  // same-head extended filter sequence/proxy requirements here
  // expanded interval length is head.value * tailPrimorial
  extendedPeriod == period * (head.value - BigInt(1))
}.holds
```

The exact signature may change, but it must keep the spec object in view:

- `SpecSieveSequence`
- `head.value`
- `tailPrimorial`
- current `period`
- same-head extended filter
- no cycle rotation
- no sorted pipeline

If the theorem cannot be verified, the ticket should end with the precise missing lemma and a green working tree.

## Tracks

### Track A: Same-Head Filter Equivalence

**Status:** RECOMMENDED FIRST TRACK

Work only with a same-head extended-filter proxy. Do not use actual `seq.next` yet.

Desired statement:

```text
extended.accepts(v)
iff
seq.accepts(v) && Calc.mod(v, seq.head.value) != 0
```

Required facts:

```text
extended.head.value == seq.head.value
extended.filterValues.head == seq.head.value
extended.filterValues.tail == seq.filterValues
```

Existing private lemmas already prove most of this in old-shape form. The work may be to expose a narrow public wrapper or define a cleaner same-head proxy theorem.

**Do not migrate those private lemmas to actual `seq.next` in this track.** That repeats the 2026-07-03 partial-migration failure.

### Track B: Spec-Level Density Count

**Status:** MAIN HARD TRACK

Prove the count over ordinary integer candidates, not over cycle residues and not over sorted pipeline lists.

Correct interval:

```text
[head, head + head * tailPrimorial)
```

Incorrect interval:

```text
[head, head + tailPrimorial)
```

The theorem must count values accepted by old filters, then values accepted by old filters plus the current head:

```text
oldAcceptedCount      = period * head
extendedAcceptedCount = period * (head - 1)
removedCount          = period
```

Recommended proof strategy:

1. Use `SpecSieveSequence` periodicity to connect one current period to `tailPrimorial`:

```text
apply(period) == head.value + tailPrimorial
```

2. Use lower-level interval/density lemmas only as dependencies of the spec theorem.
3. Prefer a theorem about filter predicates over consecutive integer intervals:

```text
count(v in [head, head + head*M) where accepts_old(v)) = period * head
count(v in [head, head + head*M) where accepts_old(v) && mod(v, head) != 0)
  = period * (head - 1)
```

4. Only after the predicate count is verified, connect it to the generated index/period through `indexOfAccepted` / `apply`.

#### Track B1: Residue/Permutation Count

**Status:** AVAILABLE BUT NOT SELECTED

This route proves that, for each current survivor residue, the `head` lifted
copies hit every residue class modulo `head` exactly once. It is mathematically
clean but repeats the residual/CRT style that previously produced hard bridges.

Use only if Track B2 fails with a clear blocker.

#### Track B2: Recursive Density Preservation Over Previous Primes

**Status:** SELECTED NEXT ROUTE

This route avoids starting from products/residue permutations. Instead, prove
that the already-established one-prime density law remains true after filtering
by every prime seen so far.

Use `AllPrimesSoFarList` as the intended domain anchor, even if the first helper
is conditional over a raw `List[BigInt]`. The eventual consumer is
`SpecSieveSequence.primes`, and `AllPrimesSoFarList` provides the exact structural
facts the final proof needs:

- no repeated prime values;
- no missing earlier primes;
- descending stage order with current `head` and previous primes in `tail`;
- direct match to `SpecSieveSequence.filterValues`.

Do not let the proof drift into a generic-list theorem that cannot be connected
back to `seq.primes` without another narrator bridge.

Target statement, in prose:

```text
Fix a tracked prime h and a list of distinct previous primes P.
Across a complete interval large enough for the filters in P and h,
after removing multiples of every p in P, the remaining values still
contain h-multiples at density exactly 1 / h.
```

This is intentionally phrased over the previous-prime list, not over an opaque
product-only object, so the later bridge back to `SpecSieveSequence.filterValues`
is direct.

Recommended proof shape:

1. Base case: no previous filters. The existing consecutive-integer density
   theorem gives the `1 / h` count.
2. Step case: assume `h`-multiple density is preserved after filtering by
   `tail(P)`. Show that additionally filtering by `P.head` preserves that same
   `1 / h` density, using the two-prime density preservation theorem as the
   local step.
3. Keep the theorem conditional on the needed distinct-prime facts at first.
   Do not derive all `AllPrimesSoFarList` structure in the same lemma.
4. Once the conditional wrapper is green, add a thin `AllPrimesSoFarList` or
   `SpecSieveSequence` wrapper that discharges those conditions from the real
   stage object.

Expected link to the spec theorem:

```text
P = seq.filterValues
h = seq.head.value
```

Once Track B2 is verified, the same-head filter-size proof should consume it
directly instead of introducing a disconnected product/residue theorem.

## Draft Lemma Plan

**Status:** First wrapper and primorial-divisibility bridge implemented. Treat
`assertDensityForAllPrimesSoFarConditional` and
`assertPrimeValuesDividePrimorial` as verified; the remaining code in this
section is still draft.

### Proposed Location

Create a Chapter 5 object, because the proof receives `AllPrimesSoFarList`:

```text
src/main/scala/v1/chapter5/prime/properties/AllPrimesSoFarDensity.scala
```

Rationale:

- Chapter 2 owns raw integer density lemmas.
- Chapter 5 owns `Prime`, `AllPrimesSoFarList`, `PrimeUtils.primeValues`, and
  prime-list structural facts.
- Chapter 6 should later consume a stage-shaped theorem, not unwrap
  `AllPrimesSoFarList` itself.

### Planned Lemmas

1. `assertDensityForAllPrimesSoFarConditional`
   - Receives `AllPrimesSoFarList`.
   - Assumes the two raw-list preconditions required by
     `ConsecutiveIntegers.densityForPrimeList`.
   - Calls the already verified Chapter 2 density lemma.
   - Purpose: prove the wrapper shape before trying to discharge structure.

2. `assertPrimeValuesNoMultiplesInAllPrimesSoFar`
   - Receives `AllPrimesSoFarList`.
   - Proves `ConsecutiveIntegers.noMultiplesInList(values)` for
     `values = PrimeUtils.primeValues(primes.list.list)`.
   - Purpose: discharge the "distinct / no repeated divisibility" precondition
     from the real prime-list object, not from a generic list.
   - Reuse points:
     - `AllPrimesSoFarList.allPrimesSoFar(primes.list)` is already a constructor invariant.
     - `SortedPrimeList.isDescending(primes.list.list)` is already a constructor invariant.
     - `SortedPrimeList.assertTailDescending` and `AllPrimesSoFarList.tail` already preserve
       the structure for recursion.
     - Since the list is descending, every tail prime value is smaller than the
       current head value; use this directly rather than proving "no duplicates"
       from scratch.

3. `assertPrimeValuesDividePrimorial`
   - Receives `AllPrimesSoFarList`.
   - Proves `ConsecutiveIntegers.allPrimesDivideM(values, M)` where
     `M = PrimeUtils.primorial(primes.list.list)`.
   - Purpose: discharge the "each prime divides the full product" precondition
     from the real prime-list object.
   - Reuse points:
     - `PrimeUtils.primorialUnfold` exposes `primorial(p :: ps) == p.value * primorial(ps)`.
     - `PrimeUtils.primorialPositive` proves the product is positive.
     - `PrimeProperties.primorialPlusOneTailLoop` contains the exact local pattern
       for proving `mod(previousPrimorial * p * tailPrimorial, p) == 0`; it is
       private, so either expose a tiny public divisibility helper or re-use the
       same one-step arithmetic locally. Do not invent a new product theory.

4. `assertDensityForAllPrimesSoFar`
   - Receives `AllPrimesSoFarList`.
   - Calls lemmas 2 and 3, then lemma 1.
   - Purpose: final Chapter 5 wrapper showing the already-proved prime density
     theorem works for the exact prime-list structure used by `SpecSieveSequence`.

5. `assertCurrentHeadDensityAfterTailFilters`
   - Later, still Chapter 5 or as a thin Chapter 6 wrapper.
   - Receives `AllPrimesSoFarList` and specializes the density result to:

```text
tracked prime = primes.head.value
previous filters = primes.list.tail.list
```

   - Purpose: bridge from "density for all primes so far" to the same-head
     spec-size theorem. Do not attempt this until lemma 4 is green.

### Draft Code

```scala
package v1.chapter5.prime.properties

import stainless.lang.*
import stainless.collection.List
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.ConsecutiveIntegers
import v1.chapter3.list.properties.ListProduct
import v1.chapter5.prime.{AllPrimesSoFarList, PrimeUtils}

object AllPrimesSoFarDensity {

  /**
   * DRAFT -- not yet verified.
   *
   * First wrapper only: prove that the Chapter 2 density theorem can be called
   * with the exact values extracted from AllPrimesSoFarList.
   */
  def assertDensityForAllPrimesSoFarConditional(
    primes: AllPrimesSoFarList,
    start: BigInt,
    blocks: BigInt
  ): Boolean = {
    require(start >= BigInt(0))
    require(blocks >= BigInt(1))

    val primeList = primes.list.list
    val values = PrimeUtils.primeValues(primeList)
    val modulus = PrimeUtils.primorial(primeList)

    require(modulus > BigInt(0))
    require(ConsecutiveIntegers.noMultiplesInList(values))
    require(ConsecutiveIntegers.allPrimesDivideM(values, modulus))

    assert(PrimeUtils.primorialPositive(primeList))
    assert(ConsecutiveIntegers.densityForPrimeList(start, values, modulus, blocks))

    true
  }.holds

  /**
   * DRAFT -- not yet verified.
   *
   * Discharge ConsecutiveIntegers.noMultiplesInList from AllPrimesSoFarList.
   * This should use descending order, primality, and existing coprimality
   * helpers; do not reimplement a duplicate prime-list predicate.
   */
  def assertPrimeValuesNoMultiplesInAllPrimesSoFar(
    primes: AllPrimesSoFarList
  ): Boolean = {
    val primeList = primes.list.list
    val values = PrimeUtils.primeValues(primeList)

    // Draft proof direction:
    // - Do NOT prove distinctness from scratch.
    // - Use primes.list's SortedPrimeList invariant:
    //     SortedPrimeList.isDescending(primeList)
    //   so every tail value is strictly smaller than primeList.head.value.
    // - Recurse through AllPrimesSoFarList.tail / SortedPrimeList.assertTailDescending
    //   so the tail keeps the same structure.
    // - For the current head against each smaller tail value, use the small-dividend
    //   fact (`tailValue < headValue`) rather than Euclid.
    // - If ConsecutiveIntegers.noMultiplesInList's `%`-based surface becomes hard
    //   to feed from `Calc.mod`, stop and create/ask for a Calc.mod-shaped
    //   companion in Chapter 2 instead of forcing an ad hoc bridge here.

    ConsecutiveIntegers.noMultiplesInList(values)
  }.holds

  /**
   * DRAFT -- not yet verified.
   *
   * Discharge ConsecutiveIntegers.allPrimesDivideM for the primorial of the
   * exact AllPrimesSoFarList values.
   */
  def assertPrimeValuesDividePrimorial(
    primes: AllPrimesSoFarList
  ): Boolean = {
    val primeList = primes.list.list
    val values = PrimeUtils.primeValues(primeList)
    val modulus = PrimeUtils.primorial(primeList)

    assert(PrimeUtils.primorialPositive(primeList))
    assert(PrimeUtils.primeValues(primeList).size == primeList.size)

    // Draft proof direction:
    // - Do NOT invent a new product theory.
    // - Base: empty list, allPrimesDivideM is true.
    // - Step:
    //   PrimeUtils.primorialUnfold(primeList) gives
    //     modulus == head.value * PrimeUtils.primorial(primeList.tail)
    //   so head.value divides modulus by the same local arithmetic pattern used
    //   in PrimeProperties.primorialPlusOneTailLoop:
    //     AdditionAndMultiplication.ATimesBSameMod(BigInt(0), head.value, tailPrimorial)
    // - Tail divisibility should come from the recursive call on the tail's
    //   primorial, then a one-step "if x divides tailProduct, x divides
    //   head.value * tailProduct" bridge.
    // - If that bridge already exists, use it. If not, add only that tiny
    //   Chapter 5/Chapter 2 helper, then return here.

    ConsecutiveIntegers.allPrimesDivideM(values, modulus)
  }.holds

  /**
   * DRAFT -- not yet verified.
   *
   * Final Chapter 5 wrapper for the already-proved density theorem.
   * This is the first useful result for Chapter 6 to consume later.
   */
  def assertDensityForAllPrimesSoFar(
    primes: AllPrimesSoFarList,
    start: BigInt,
    blocks: BigInt
  ): Boolean = {
    require(start >= BigInt(0))
    require(blocks >= BigInt(1))

    val primeList = primes.list.list
    val values = PrimeUtils.primeValues(primeList)
    val modulus = PrimeUtils.primorial(primeList)

    assert(assertPrimeValuesNoMultiplesInAllPrimesSoFar(primes))
    assert(assertPrimeValuesDividePrimorial(primes))
    assert(ConsecutiveIntegers.noMultiplesInList(values))
    assert(ConsecutiveIntegers.allPrimesDivideM(values, modulus))
    assert(assertDensityForAllPrimesSoFarConditional(primes, start, blocks))

    true
  }.holds

  /**
   * DRAFT -- not yet verified.
   *
   * Later specialization for the spec theorem. Do not attempt until
   * assertDensityForAllPrimesSoFar is green.
   */
  def assertCurrentHeadDensityAfterTailFilters(
    primes: AllPrimesSoFarList,
    start: BigInt,
    blocks: BigInt
  ): Boolean = {
    require(!primes.isEmpty)
    require(start >= BigInt(0))
    require(blocks >= BigInt(1))

    val head = primes.head.value
    val tailPrimes = primes.list.tail.list
    val tailValues = PrimeUtils.primeValues(tailPrimes)
    val tailModulus = PrimeUtils.primorial(tailPrimes)

    // TODO:
    // 1. Apply the all-primes-so-far density theorem to head :: tail.
    // 2. Relate the tracked head density to filtering by tailValues.
    // 3. Expose the exact statement needed by SpecSieveSequence:
    //
    //    Over [start, start + head * tailModulus),
    //    the head-multiple density among values surviving tailValues is 1 / head.

    true
  }.holds
}
```

### Track C: Real `seq.next` Head Change

**Status:** DEFERRED UNTIL TRACKS A AND B ARE GREEN

Actual `seq.next` changes the starting head to the next prime. Keep this separate from the filter-count theorem.

The future statement should be:

```text
same-head extended-filter stream
rotated/rebased at its first survivor
equals real seq.next
```

Do not try this while the same-head count is still open.

### Track D: Cycle/Rotation Connection

**Status:** DEFERRED LAST

Current implementation check:

- `CycleSieveSequence.next()` does not call the visible
  `nextExpanded -> nextFiltered -> nextSorted -> nextGaps -> nextRotatedGaps`
  chain. It calls `SieveSequenceNextLevel.nextGapsWalk(this)` and then
  `nextWithGapCycle`.
- `nextGapsWalk` uses `steps = seq.head * seq.gapCycle.size`, starts from
  `newHead = seq.apply(1)`, and walks the expanded current sequence while
  skipping values where `Calc.mod(current, seq.head) == 0`.
- `nextFromWindow` is the clearest executable shape for the desired order:
  it builds `currentWindow(integral, head * gapCycle.size)`, filters by
  `Calc.mod(v, head) != 0`, turns survivors into gaps, and then calls
  `nextWithGapCycle`.
- The named helper pipeline still exists and is explicitly:
  `nextExpanded -> nextFiltered -> nextSorted -> nextGaps -> nextRotatedGaps`.
  So the standard helper surface is expand/filter first and rotate last, but
  the active `next()` path bakes the walk/rebase shape in earlier and does not
  expose rotation as a direct call.

Only after the spec same-head and real-next bridges are verified should anyone connect this to:

```text
seq.gaps -> repeat -> filter/merge -> rotate
```

Do not use `nextSorted`, `nextFiltered`, or `nextRotatedGaps` as a shortcut unless the spec count theorem is already green and the exact bridge is load-bearing. Avoid creating detached lemmas that require a narrator.

Important future fact for this track:

```text
multiply -> filter -> rotate
multiply -> rotate -> filter
rotate -> multiply -> filter
```

should generate the same final filtered/rotated result, provided multiplication/expansion happens before filtering. The forbidden order is:

```text
filter -> multiply
```

because filtering before multiplication can remove the unique element whose later copy is supposed to witness the one-over-head removal count.

## Assumptions

- The current stage has a valid period:

```text
period > 0
apply(period) == head.value + tailPrimorial
```

- The expanded interval for the count is:

```text
head.value * tailPrimorial
```

- `SpecSieveSequence.apply` scans consecutive integers; `accepts` is a predicate over that integer domain.
- The current head is prime and is not one of the tail filters.
- Any use of lower-level density lemmas must be visibly consumed by the spec theorem.
- `AllPrimesSoFarList` is the canonical source of previous-prime structure for
  the final proof. Generic list assumptions are acceptable only as an intermediate
  step if a later wrapper consumes them from `seq.primes`.

## Traps To Avoid

1. **Do not forget the multiply by head.**

The one-over-head count is over:

```text
[head, head + head * M)
```

not over:

```text
[head, head + M)
```

2. **Do not treat `seq.apply` values as the candidate universe.**

`SpecSieveSequence` scans all consecutive integers. `apply` returns accepted values. The count theorem should start from integer intervals and filter predicates, then connect to `apply`.

3. **Do not confuse actual next head with front filter.**

For actual `seq.next`:

```text
seq.next.head.value != seq.head.value
seq.next.filterValues.head == seq.head.value
```

4. **Do not repeat the partial precondition migration.**

Changing a `require` from:

```scala
nextSeq.head.value == head.value
```

to:

```scala
nextSeq.filterValues.head == head.value
```

requires migrating callee, all callers, and all dependents together. Do not do that as a side quest in this ticket.

5. **Do not route through sorting.**

There is no sorting in the intended track:

```text
spec integer interval -> old filter -> add head filter -> same-head period size
```

Sorting belongs to the cycle pipeline, not the spec-only count proof.

6. **Do not filter before expansion/multiplication.**

The later cycle route may commute rotation with filtering:

```text
multiply -> filter -> rotate
multiply -> rotate -> filter
rotate -> multiply -> filter
```

but it must not commute filtering ahead of multiplication. The proof needs the expanded copies so exactly one copy per old position can be removed by the new head filter.

7. **Do not create duplicate proof surfaces.**

If a lower-level density lemma is added, the spec theorem must call it directly. Otherwise it is another detached proof object and should not be counted as progress.

8. **Do not overclaim in articles.**

Until the spec theorem verifies, `articles/chapter6/sieve-sequence-v2.md` must keep the closed-form size statement marked as pending/draft.

## Critic Gate: Ticket No-Go Items

For this ticket, the Critic must explicitly check the proposed code change
against the no-go list below. The Critic should return `CONCERNS` if the action
violates any no-go item, even if the change looks locally valid.

Worker proposals for this ticket must include:

```text
Track: A | B2 | C | D
Load-bearing path: <which later theorem/wrapper consumes this lemma>
No-go check: <one sentence explaining why the proposal avoids the no-go list>
```

If a proposal has no track, no named consumer, or no no-go check, the Critic
must return `CONCERNS`.

### No-Go Items

1. **No cycle/pipeline targets before Track B2 is green.**

Do not edit or add proof code in:

```text
CycleSieveSequence
SieveSequenceNextLevel
SpecDerivedSieveSequence
SpecDerivedBySurvivors
SpecCycleSieveEquivalence
```

and do not introduce new proof obligations involving:

```text
nextSorted
nextFiltered
nextRotatedGaps
```

until the Chapter 5 / spec-facing density wrapper is verified.

2. **No generic-list-only endpoint.**

A raw `List[BigInt]` helper is allowed only if the proposal names the
`AllPrimesSoFarList` or `SpecSieveSequence` wrapper that will consume it.
Generic density proofs without a stage-facing consumer are off-track.

3. **No residual/permutation route unless Track B2 is blocked.**

Do not switch to the residue/permutation/CRT lift proof until Track B2 has a
documented blocker in the Learning Log.

4. **No wrong interval.**

Any count theorem for the one-over-head removal must use the expanded interval:

```text
[head, head + head * M)
```

not:

```text
[head, head + M)
```

5. **No `seq.next.head` / `seq.next.filterValues.head` confusion.**

Actual `seq.next` has:

```text
seq.next.head.value        = next prime
seq.next.filterValues.head = seq.head.value
```

Any proposal that treats those as the same must be rejected.

6. **No partial precondition migration.**

Do not change a `require` from:

```scala
nextSeq.head.value == head.value
```

to:

```scala
nextSeq.filterValues.head == head.value
```

unless the proposal lists every callee, direct caller, and downstream dependent
that must migrate in the same green-to-green change. This ticket should not need
that migration during Tracks A or B2.

7. **No filtering before expansion/multiplication.**

Allowed future cycle orders:

```text
multiply -> filter -> rotate
multiply -> rotate -> filter
rotate -> multiply -> filter
```

Forbidden:

```text
filter -> multiply
```

8. **No article upgrade before proof.**

Do not change `articles/chapter6/sieve-sequence-v2.md` from pending/draft to
verified for the closed-form size theorem until a verified Stainless lemma
exists and is cited.

9. **No duplicate proof surface.**

If an existing lemma or invariant already states the needed fact, the proposal
must reuse or expose it. Do not re-prove `AllPrimesSoFarList`, descending-order,
prime-values, or primorial facts under a new predicate name.

## Risks

- The existing Chapter 2 density lemmas may count raw divisibility but not old-filter survivors. If so, an induction over the previous-prime filter list may be required.
- Proving density preservation across a prime list may need Euclid/Bezout support. Check current `EuclidLemma` and related done tickets before adding anything.
- `SpecSieveSequence` has large VCs and cross-instance calls can time out. Keep wrappers small and avoid cross-instance calls unless they are the only fact in the lemma.
- A same-head proxy may not exist as a concrete object. If constructing one is hard because of `AllPrimesSoFarList` invariants, state the proof in terms of explicit filter lists first, then wrap it back into `SpecSieveSequence`.
- A generic `List[BigInt]` density lemma can become another disconnected proof
  surface. Keep the planned `AllPrimesSoFarList` / `SpecSieveSequence` wrapper
  in the same track and do not count the generic lemma as the final result.

## Validation

Markdown-only changes do not require Stainless verification.

Before any future code change:

1. Check `logs/verify.log` with:

```text
grep "total:" logs/verify.log
```

2. Do not rerun `just verify` if the log already answers the baseline question.
3. If a code change is made, follow AGENTS.md:
   - one assertion/require/lemma per change;
   - verify after each code change;
   - timeout is failure;
   - stop after three failed attempts.
4. After adding any verified lemma, update `OBJECTS.md`.
5. After a completed proof, update the article with all three representations and honest framing.

## START HERE

1. Read this ticket and `LEARNINGS.md` sections 18.6 and 18.8.
2. Read the bodies of these `SpecSieveSequence` lemmas:
   - `assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple`
   - `assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple`
   - `assertRejectedByNextWhenNewHeadMultiple`
   - `assertNextValueAcceptedByThis`
3. Decide whether Track A needs a public same-head wrapper or only a new theorem over explicit filter lists.
4. Search Chapter 2 and Chapter 5 for existing density/Euclid lemmas before writing anything:
   - `ConsecutiveIntegers.countModZeroEqualsM`
   - `ConsecutiveIntegers.densityPreservedAfterFiltering`
   - `ConsecutiveIntegers.densityForPrimeList`
   - `EuclidLemma`
   - `BezoutUtils`
5. Inspect `AllPrimesSoFarList` and `PrimeUtils.primeValues` before choosing the
   first helper signature. The route may start with a conditional raw-list lemma,
   but it must already name how `seq.primes.list.tail.list` will discharge those
   conditions.
6. Continue Track B2 from the verified conditional wrapper:
   `AllPrimesSoFarDensity.assertDensityForAllPrimesSoFarConditional`.
7. Next code micro-goal should discharge exactly one structural precondition
   needed by that wrapper from `AllPrimesSoFarList`, preferably starting with
   the smallest reusable fact. Do not jump to the full spec-size theorem yet.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-13 | Ticket created after user rejected detached cycle/pipeline proof directions. The right proof starts from `SpecSieveSequence`, keeps the same-head filter-count theorem separate, and defers real head change plus rotation. | Start with Track A, then Track B. |
| 2026-07-13 | User selected the simple count route over the residual/permutation route: prove that one-prime density remains true after filtering by all primes so far, keeping the later link to `SpecSieveSequence.filterValues` direct. | Start Track B2 before B1. |
| 2026-07-13 | Read-only check found `ConsecutiveIntegers.densityPreservedAfterFiltering` already proves the two-prime local step, and `BezoutUtils.assertPrimeProductNotDivisible` now provides the Euclid contrapositive needed for distinct-prime product non-divisibility. Current `logs/verify.log` is red (`23 valid, 1 unknown`), so no Scala proof change can start under green-to-green. | First future code step: after green baseline is restored, add only a conditional list-recursive density-preservation wrapper over previous primes. |
| 2026-07-13 | User emphasized that the proof should stay anchored to `AllPrimesSoFarList`, not only arbitrary lists: it guarantees no repeated prime values, no missing earlier primes, and direct correspondence with the `SpecSieveSequence` object that must consume the theorem. | Keep an `AllPrimesSoFarList` / `SpecSieveSequence` wrapper in scope for Track B2. |
| 2026-07-13 | Added a ticket-specific Critic gate: every Worker proposal must name its track, load-bearing consumer, and no-go check. The Critic must reject proposals that violate the ticket no-go list, even if the local lemma seems plausible. | Future implementation must pass the no-go gate before editing. |
| 2026-07-13 | Added and focused-verified `AllPrimesSoFarDensity.assertDensityForAllPrimesSoFarConditional`: a conditional Chapter 5 bridge from `AllPrimesSoFarList` to `ConsecutiveIntegers.densityForPrimeList`. It does not discharge `noMultiplesInList` or `allPrimesDivideM`; those remain the next structural obligations. | Next Track B2 step: prove one structural precondition from `AllPrimesSoFarList`, then verify before adding the other. |
| 2026-07-13 | Full Stainless verification after the new wrapper is green: `13171 valid, 0 invalid, 0 unknown`. `just test` still reports the existing two `MainTest` CLI help-text failures also present in older `logs/test.log`; do not treat those as a density-proof regression. | Continue proof work from the green Stainless baseline; keep the unrelated test drift out of this ticket unless the user explicitly redirects. |
| 2026-07-13 | Failed micro-attempt: direct `assertPrimeValuesDividePrimorial` using `ListProductDiv.allElementsDivideProduct(values)` did not prove `ConsecutiveIntegers.allPrimesDivideM(values, primorial)`. Focused verify ended with `1 valid, 2 unknown/cancelled`, stuck on the `%`-shaped `allPrimesDivideM` bridge. The failed lemma was reverted and the surviving wrapper re-verified green (`7 valid, 0 unknown`). | Do not repeat the direct product-divisibility bridge. Next attempt should either add a tiny Chapter 2 `Calc.mod`-shaped companion for `allPrimesDivideM`, or prove the required density through a predicate whose surface already uses `Calc.mod`. |
| 2026-07-13 | Verified `ModNativeCompatibility.percentEqualsCalcMod`: for `a >= 0` and `b > 0`, native `a % b` equals `Calc.mod(a,b)`, using `ModIdempotence.modUnique` over the native quotient/remainder witness and the `Calc`/`DivMod.solve` witness. Focused verification passed (`28 valid`, `0 unknown`). | This can bridge legacy `%` predicates when arguments are known nonnegative/positive. Use it as a narrow compatibility lemma, not as permission to add new `%`-based APIs broadly. |
| 2026-07-13 | Verified `AllPrimesSoFarDensity.assertPrimeValuesDividePrimorial`. The key fix was not a new constructor lemma: `ConsecutiveIntegers.allPrimesDivideM` needs `values.head > 1`, while product helpers still need `allGreaterThan(values, 0)`. The recursive helper therefore carries both bounds, both supplied by `PrimeUtils.primeValues`. Focused verifies passed for the helper (`41 valid, 0 unknown`) and public lemma (`43 valid, 0 unknown`); full `just verify` passed (`13298 valid, 0 unknown`). | Next structural obligation is `noMultiplesInList(values)` from the same `AllPrimesSoFarList` domain. Preserve the dual-bound lesson when adding recursive helpers: carry the exact domain fact and the helper preconditions explicitly. |
| 2026-07-13 | Off-track attempt reverted: a private `assertProductNotDivisibleByPrime(head, values)` helper tried to prove `mod(product(values), head) != 0` using `BezoutUtils.assertPrimeProductNotDivisible`. Focused verify timed out at the Bezout precondition (`45 valid, 1 unknown`, 300s). This is the B1/residue/CRT support lane, not selected Track B2, and repeats the known product-nondivisibility timeout family. The helper/import were removed and `assertDensityForAllPrimesSoFar` re-verified green (`9 valid, 0 unknown`). | Do not continue through product/residue nondivisibility for this ticket unless Track B2 fails with a clear blocker and the user explicitly switches tracks. The next B2 micro-goal is a conditional list-recursive density-preservation wrapper whose step calls `ConsecutiveIntegers.densityPreservedAfterFiltering`, with an `AllPrimesSoFarList` wrapper only after the conditional shape is green. |
| 2026-07-13 | Verified the selected Track B2 bridge. `assertHeadDensityPreservedAfterPreviousFiltersConditional` recursively applies `ConsecutiveIntegers.densityPreservedAfterFiltering` across the previous filters and proves the closed-form block scaling equality; focused verify passed (`25 valid, 0 unknown`). `assertHeadDensityPreservedAfterAllPreviousFilters` wraps that bridge in `AllPrimesSoFarList`, discharging positivity and `< head` facts from the sorted prime object; focused verify passed (`21 valid, 0 unknown`). Full `just verify` is green (`13472 valid, 0 invalid, 0 unknown`). | This is not yet the final `seq.next.size` theorem. Next micro-goal should connect this verified density-preservation bridge to the actual spec-side accepted-value/count surface over `[head, head + head * M)`, without switching back to product/residue nondivisibility or expanded-residue permutation arguments. |
| 2026-07-14 | Built and verified the spec-side count surface. `SpecSieveSequence.assertGeneratedPrefixCount` proves `countAcceptedBetween(head, apply(k)) == k`; `assertExpandedOldAcceptedCount` proves the old accepted count over `[head, head + head * tailPrimorial)` is `period * head`; `assertSameHeadExtendedFilterCountFromRemovedCount` proves the same-head survivor size formula from the exact removed-count premise. Full `just verify` passed (`13652 valid, 0 invalid, 0 unknown`). | Remaining core theorem is now precise: prove `countAcceptedHeadMultiplesBetween(head, head + head * tailPrimorial) == period` from the B2 density route. Do not replace it with a narrator bridge; the theorem must connect to the concrete recursive count surface or it has not solved the size problem. |
