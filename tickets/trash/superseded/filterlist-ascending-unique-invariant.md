# filterList Ascending + Unique Invariant

**Created:** 2026-07-12
**Status:** SUPERSEDED — do not pursue as the size-proof route
**Owner:** proof follow-up for the size-composition bridge
**Related:** `tickets/active/m-interval-density-and-sieve-sequence-v2.md`

> **NOTE (2026-07-12):** This ticket explored proving the size bridge via
> `nextSorted.size == nextFiltered.size`, requiring an ascending-preservation
> invariant on `filterList`. That route was a wrong turn — it forces the proof
> through the implementation's list machinery (`sortFiltered`, deduplication,
> ascending preservation) instead of the spec's acceptance predicate. The
> correct route is documented in `m-interval-density-and-sieve-sequence-v2.md`
> (MAJOR RE-FRAMING entry): compose the verified filter-nesting bridge
> (`seq2.accepts(v) ⟺ seq1.accepts(v) ∧ mod(v,h)≠0`) with the density kernel
> at the SPEC level. This ticket is retained only for the `filterList`
> duplication cleanup (two textually-identical definitions in ch5/ch6),
> which is a separate hygiene issue, not a size-proof dependency.

## Goal

Attach two structural postconditions to `SieveUtils.filterList`, capturing the
fact that filtering only *removes* elements — it never reorders, duplicates, or
creates values:

```text
isAscending(list)        ==> isAscending(filterList(list, divisor))
noDuplicates(list)       ==> noDuplicates(filterList(list, divisor))
```

These invariants make the size-composition bridge
`nextSorted.list.size == nextFiltered.size` tractable: an ascending,
duplicate-free input passes through `filterList` still ascending and still
duplicate-free, so `SortedList.sortFiltered` (whose only dedup branch is
`x == list.head`) is a no-op on it.

## Motivation

The density theorem
`assertNextFilteredSizeGreaterThanResiduesByDensity` proves
`nextFiltered.size == residues.size * (head - 1)` conditionally. To compose
this with the existing `assertNextGapsSize` (`nextGaps.size == nextSorted.size`)
into a final `nextGaps.size == residues.size * (head - 1)`, we need
`nextSorted.list.size == nextFiltered.size`.

That equality holds because the sieve survivor values are ascending and unique
by construction, filtering only removes elements, and `sortFiltered` is a no-op
on an already-sorted duplicate-free list. But none of those structural facts is
currently available at `filterList`'s call sites — they would have to be
re-derived inside each consumer VC (the pattern that times out per LEARNINGS
18.4).

## Current State

- Baseline is green: `13164 valid, 0 invalid, 0 unknown`.
- `SortedList.assertSortFilteredNonEmpty` is verified (sort of nonempty is nonempty).
- `SieveUtils.filterList` (line 261) has NO `.ensuring` postcondition today.
- `CoprimeUtils.filterList` (ch5, line 42) is a **textually identical duplicate**
  of `SieveUtils.filterList`. Stainless treats them as different functions
  (LEARNINGS 5.3). Any invariant added to one does not apply to the other.
- There is NO existing `noDuplicates` predicate anywhere in the codebase.
- `SortedList.insertSorted` (ch3, line 60) is the sort used by
  `SortedList.fromUnsorted` → `sortFiltered`. Its dedup branch is
  `else if (x == list.head) list`.
- Private membership lemmas `assertFilterListContainsIf` /
  `assertFilterListContainsOnlyIf` in `SpecCycleSieveEquivalence` prove
  set-style containment but NOT order/subsequence preservation.

## Expected State

1. A canonical `noDuplicates` predicate exists (location TBD — likely
   `ListBoundUtils` or `ListUtils` in ch3, since both `isAscending` and
   `allGreaterThan` live there).
2. `SieveUtils.filterList` carries `.ensuring` with both preservation clauses.
3. `CoprimeUtils.filterList` either delegates to `SieveUtils.filterList` or
   carries the same postcondition (decision needed — see Risks).
4. A downstream lemma proves
   `isAscending(list) && noDuplicates(list) ==> sortFiltered(list).size == list.size`.
5. The sequence-level wrapper
   `nextSorted(seq).list.size == nextFiltered(seq).size` composes the above.
6. Final composition:
   `nextGaps(seq).size == nextResidues(seq).size * (seq.head - 1)`.

## Risks

### R1: High blast radius (25 call sites)

`filterList` has ~25 call sites across ch5/ch6. Adding `.ensuring` clauses is
backwards-compatible for *callers* (postconditions only add obligations at the
definition, not the call site), BUT:
- If Stainless re-verifies `filterList`'s body against the new postcondition
  and the proof is non-trivial, the body VC may time out.
- Any *other* `.ensuring`/`.holds` lemma that constructs `filterList(...)` and
  relies on its old contract shape could surface new VCs.

Mitigation: add ONE postcondition at a time, verify between each.

### R2: Duplicate filterList functions — RESOLVED (decision: ch3 canonical)

`CoprimeUtils.filterList` (ch5) and `SieveUtils.filterList` (ch6) are identical
but distinct to Stainless. Per LEARNINGS 5.3, the same invariant proved in two
places is itself the problem — Stainless cannot bridge the two surfaces.

**Decision (2026-07-12):** Extract a canonical `BigInt`-specialized (NOT
generic) `filterList` into ch3. Both `CoprimeUtils.filterList` and
`SieveUtils.filterList` become one-line delegators. The ascending-preservation
postcondition attaches to the single ch3 definition only.

Generics are explicitly avoided: the canonical function stays
`filterList(list: List[BigInt], divisor: BigInt)` because a generic
`filter[T](list, pred)` would force the ascending-preservation proof to reason
about an arbitrary higher-order predicate, which Stainless handles poorly.

### R3: noDuplicates predicate — RESOLVED (unnecessary)

`noDuplicates(list)` is recursive: `list.isEmpty || (!list.tail.contains(list.head) && noDuplicates(list.tail))`.
This is O(n²) and may be expensive inside inductive proofs. Alternative: define
it via `isAscending` (a strictly ascending list is automatically duplicate-free),
avoiding a new predicate entirely:

```text
isAscending(list) ==> isAscending(filterList(list, divisor))   [ascending preserved]
```

combined with the existing fact that `sortFiltered` of a strictly-ascending list
has the same size (no dedup branch hit). This collapses R3 into R1 — only ONE
postcondition needed, not two.

**Hypothesis to validate:** because `isAscending` is *strict* (uses `<`, see
`SortedList.isAscending` at line 35: `list.tail.isEmpty || (list.head < ...)`),
strict-ascending ⟹ duplicate-free. So the single `isAscending`-preservation
postcondition may suffice for the size-equality bridge, and the separate
`noDuplicates` predicate can be avoided.

## Plan

### Phase 1: Validate the strict-ascending sufficiency hypothesis — DONE

`SortedList.isAscending` (line 35) is STRICT: `list.head >= list.tail.head => false`.
So strict-ascending ⟹ duplicate-free. Therefore a SINGLE ascending-preservation
postcondition suffices — no separate `noDuplicates` predicate needed.

### Phase 2: Add canonical filterList to ch3

Create `ListBoundUtils.filterList` (BigInt-specialized, NOT generic) with the
ascending-preservation postcondition. This is the single canonical definition.

```scala
def filterList(list: List[BigInt], divisor: BigInt): List[BigInt] = {
  require(divisor > 0)
  decreases(list.size)
  if (list.isEmpty) List.empty
  else {
    val rest = filterList(list.tail, divisor)
    if (Calc.mod(list.head, divisor) != BigInt(0)) list.head :: rest
    else rest
  }
}.ensuring(res => !SortedList.isAscending(list) || SortedList.isAscending(res))
```

Note: ch3 already contains `SortedList` (which has `isAscending`), so no
cross-chapter import is needed for the postcondition. Verify in isolation.

### Phase 3: Delegate CoprimeUtils.filterList to ch3

Replace `CoprimeUtils.filterList` (ch5) body with a one-line delegator:
```scala
def filterList(list: List[BigInt], divisor: BigInt): List[BigInt] =
  ListBoundUtils.filterList(list, divisor)
```
Keep the same signature so all ch5 callers (`FilterPreservesPrimesProperties`)
work unchanged. Verify ch5 still green.

### Phase 4: Delegate SieveUtils.filterList to ch3

Replace `SieveUtils.filterList` (ch6) body with a one-line delegator:
```scala
def filterList(list: List[BigInt], divisor: BigInt): List[BigInt] =
  ListBoundUtils.filterList(list, divisor)
```
All ch6 callers unchanged. Verify full tree green.

ONLY after Phase 4 is green is the duplication resolved and the invariant
available everywhere through one canonical definition.

### Phase 5: Prove sortFiltered size-equality for ascending input

In `SortedList`:
```scala
def assertSortFilteredSizeWhenAscending(list: List[BigInt]): Boolean = {
  require(SortedList.isAscending(list))
  sortFiltered(list).size == list.size
}.holds
```
Uses: strict-ascending ⟹ duplicate-free, so `insertSorted`'s dedup branch
(`x == list.head`) never fires when inserting `list.head` into
`sortFiltered(list.tail)` (since `list.head` > all tail elements).

### Phase 6: Compose to sequence level

```scala
def assertNextSortedSizeEqualsFiltered(seq): Boolean = {
  ... // nextSorted(seq).list.size == nextFiltered(seq).size
}.holds

def assertNextGapsSizeByDensity(seq): Boolean = {
  ... // nextGaps(seq).size == nextResidues(seq).size * (seq.head - 1)
}.holds
```

## Stop Conditions

- If `ListBoundUtils.filterList` body VC times out against the postcondition,
  revert and try Phase 5's direct size-equality lemma instead (without the
  invariant).
- If delegating `CoprimeUtils.filterList` or `SieveUtils.filterList` breaks
  existing proofs (callers that unfolded the old body), STOP — that means a
  caller depended on the body shape, which needs a bridge lemma, not a forced
  delegation. Record which caller broke.
- If `assertSortFilteredSizeWhenAscending` needs more than 3 attempts, stop and
  record the missing lemma rather than retrying variations.

## Validation

1. Start from green (`grep "total:" logs/verify.log`).
2. One phase per change. Verify between each.
3. Focused verify first, then full `just verify`.
4. Update OBJECTS.md after each green verification.
5. Update `m-interval-density-and-sieve-sequence-v2.md` with the composed
   final theorem once Phase 4 is green.

## START HERE

1. Read `SortedList.isAscending` (line 35) to confirm strictness.
2. Read `SortedList.insertSorted` (line 60) dedup branch.
3. Decide: single ascending-preservation postcondition (preferred) vs two
   postconditions (ascending + noDuplicates).
4. If single: proceed to Phase 2. If two: define `noDuplicates` in ch3 first.

## Progress Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-12 | Created ticket. Confirmed `SortedList.isAscending` is STRICT (`list.head >= list.tail.head => false`), so strict-ascending ⟹ duplicate-free for free. This means the "unique" preservation postcondition may be unnecessary — a single ascending-preservation postcondition suffices for the size-equality bridge. | Decide single vs double postcondition before touching filterList. |
| 2026-07-12 | User flagged the core issue: `CoprimeUtils.filterList` (ch5) and `SieveUtils.filterList` (ch6) are textually identical duplicates. Having the same invariant proved in two places is itself the problem (LEARNINGS 5.3) — Stainless cannot connect the two surfaces, so any bridging proof gets stuck. The real fix is delegation: one canonical definition, both surfaces delegate to it. Attempted adding `.ensuring` to `SieveUtils.filterList` alone; verify was cancelled and the change reverted to baseline because it would have created the asymmetric duplicated-proof surface the user warned against. | Do NOT add the postcondition to only one filterList. Resolve the duplication first (R2), then attach the invariant to the single canonical definition. |
| 2026-07-12 | Decision: ch3 canonical, BigInt-only (not generic). User concerned about Stainless + generics, confirmed filterList stays `List[BigInt] + divisor` specialized. Plan rewritten as Phases 2-6: add canonical to `ListBoundUtils` (ch3), delegate both ch5/ch6 to it, then size-equality lemma, then compose. | Proceed with Phase 2. |
| 2026-07-12 | Phase 2 attempted: added canonical `filterList` to `ListBoundUtils` with `.ensuring(!isAscending(list) || isAscending(res))`. Focused verify: 23/24 valid, **1 timeout (300s)** on the postcondition VC for the `head :: rest` branch (line 223). Root cause: proving `isAscending(list.head :: rest)` needs the fact `rest.head >= list.tail.head > list.head` when rest is nonempty — i.e. "filter output is a subsequence preserving order" — which is exactly the structural fact not yet available and that the postcondition was meant to establish. The postcondition-on-producer approach (LEARNINGS 18.4) works when the proof is simple; here the proof needs a subsequence lemma that doesn't exist yet. Reverted `ListBoundUtils` to baseline (removed function + import). | The direct size-equality lemma (Phase 5) has the SAME core difficulty — both need "filter preserves ascending order." The real missing lemma is: `isAscending(list) && isAscending(filterList(list,d)) holds`, proven by induction with an explicit "rest is subsequence of tail" helper. Next session should target THAT lemma first (in ch3, standalone, not as a postcondition), then both the postcondition and size-equality become easy. |
