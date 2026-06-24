# Canonical Next Strategy (Leg 3 of the Spec/Canonical/Cycle EPIC)

**Status:** Active
**Created:** 2026-06-24
**Owner:** `CanonicalCycleSieve` (`src/main/scala/v1/chapter6/seq/sieve/CanonicalCycleSieve.scala`)

## EPIC Context (do not duplicate per-ticket)

A three-way connection between three sieve representations:

| Leg | Statement | Status |
|---|---|---|
| 1 | Spec is correct | ✅ Done (`SpecSieveSequence` linear scan) |
| 2 | Canonical ≡ Spec, current stage | ✅ Done (`CanonicalCycleSieve.assertApplyMatches(k)`: `cycle(k) == spec(k)`) |
| **3** | **The cycle strategy (merge / rotate / new-head) is correct, certified via Canonical matching `spec.next`** | ❌ **This ticket** |
| 4 | `CycleSieveSequence` ≡ Canonical, using ONLY Cycle's structural rules (no Spec link) | Future |

**Key architectural fact (confirmed with user, 2026-06-24):** Canonical is *built around Spec by definition* and is allowed to use Spec freely. The "walks with its own legs" / "no Spec link" constraint applies to **`CycleSieveSequence`** (Leg 4), not to Canonical (Leg 3). So Leg 3 may invoke Spec facts.

## Goal

Prove that the **cycle strategy** — computing the next head and next gaps from the cycle's own arithmetic — produces results that match what `spec.next` produces:

```
next head:  cycle(1) == spec.next.head.value                          [already proven: assertNextHeadMatches]
next gaps:  <cycle strategy output> == spec.next.gapList(0, nextPeriod)   [open]
```

The "cycle strategy" is whichever verified idiom produces the next gap list from Canonical's own data and matches `spec.next.gapList`. Multiple idioms are admissible (per user guidance 2026-06-24, citing `RecursiveCycleMatchesModCycle`, `assertSimplifiedDiffValuesMatchCycle`, `ModIdempotence`).

## Current State

- **Next head:** ✅ Proven. `CanonicalCycleSieve.assertNextHeadMatches()` gives `cycle(1) == spec.next.head.value`. The pure cycle-arithmetic form `cycle(1) = cycle.head + cycle.gapCycle.memCycle(0)` is exposed by `CycleSieveSequence.assertNextHeadGreaterThanHead`.
- **Next gaps:** ❌ Open. This is the real work of this ticket.

## Expected State

A Canonical-side lemma, e.g.:

```
assertNextGapsMatchSpecNextGapList(nextPeriod)
  :  <canonical-computed next gap list>
     == spec.next.gapList(0, nextPeriod)
```

under the period anchors:
```
period > 0
spec(period) == spec.head.value + spec.filterModulus
nextPeriod > 0
spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus
spec.primes.nextPrime.value < spec.head.value * spec.head.value
```

## Known Proof Idioms (per Q2 guidance)

| Idiom | Source | Shape | Trade-off |
|---|---|---|---|
| **Diff-based induction** | `ClassicCycleIntegralProperties.assertDiffEqualsCycleValue` + `assertSameDiffAfterCycle` | `integral(k+1) - integral(k) == cycle(k+1)`; diffs repeat per period via `MemCycleProperties.valueMatchAfterManyLoopsInBoth` | **Primary candidate.** Pure cycle arithmetic, avoids the walk's opacity, periodic so no `head × period` scan. |
| Merge via `indexOfAccepted` | `SpecSieveSequence.mergedGapPrefix` + `assertMergedGapPrefixMatchesNext` | Walks current stage's accepted indices, no positional scan over naturals | Verified on Spec; reusable as fallback. |
| Walk / `collectGaps` | `SieveSequenceNextLevel.nextGapsWalk` | Recurses `head × period` positions | **AVOID.** Timed out 3× (per `canonical-spec-to-cycle-alignment.md` Update Log). Diff depends on `lastSurvivor` (all previous positions), so Stainless treats it as opaque. |

**Decision:** Pursue the **diff-based induction** idiom first. Fall back to the `mergedGapPrefix`/`indexOfAccepted` idiom if the diff approach stalls.

## Placement

- New computation/lemmas live on **`CanonicalCycleSieve`** (or a small sibling object if cohesion demands it). Not on `CycleSieveSequence` (that's Leg 4) and not on `SpecSieveSequence`.

## Alternatives Considered

1. Reuse `SpecSieveSequence.mergedGapPrefix` directly. Rejected as primary: it walks Spec's `apply`, which is fine for Canonical (Leg 3 may use Spec) but doesn't surface the cycle-arithmetic structure that Leg 4 will need. Keep as fallback.
2. Write a `CanonicalNextLevel` sibling object. Deferred — start with methods on `CanonicalCycleSieve`; refactor if it grows.
3. The residue pipeline (`nextRotatedGaps`). Rejected: `v0-v2-apply-equivalence.md` 2026-06-23 log shows the project deliberately de-prioritized residue-pipeline proofs.

## Risks and Assumptions

1. **Diff idiom applicability.** `assertSameDiffAfterCycle` proves `integral(pos+1)-integral(pos) == integral(pos+size+1)-integral(pos+size)`. This is a *single-period* shift. The next gap list spans `head` periods (one per value filtered by the new head). Need to confirm the diff idiom lifts cleanly across `head` periods, not just one.
2. **Cross-instance calls are expensive (LEARNINGS 18).** Canonical calling `spec.next.gapList` and `spec.next.indexOfAccepted` is a cross-instance call. Keep the number of such calls per lemma small; isolate them.
3. **Period anchor for the next stage.** `nextPeriod` must satisfy `spec.next(nextPeriod) == spec.next.head.value + spec.next.filterModulus`. This is the same shape as the current-stage anchor; carry it as a precondition.
4. **The product-not-divisible caveat** (`Calc.mod(SieveUtils.product(filterValues), head.value) != 0`) is still an open constructor obligation on `CycleSieveSequence`. Out of scope here; it's tracked in `primorial-not-divisible-by-new-prime.md`.

## Validation

- `green-to-green`: check `verify.log` (do not re-run on clean state) before each code change; run full `just verify` after each non-markdown change.
- `small-changes`: ONE lemma/assertion per verify cycle.
- `stop-and-ask`: 3 failed attempts on a lemma → stop, paste the error, ask.
- Mirror the structure of existing verified cycle lemmas (`ClassicCycleIntegralProperties`, `SpecSieveSequence.assertMergedGapPrefixMatchesNext`) per PROOF_GUIDE.

## Related Tickets

- `tickets/active/canonical-spec-to-cycle-alignment.md` — Leg 2 (canonical construction + current-stage equivalence). Its Lemma 5 (gap-walk equality) is superseded in scope by this ticket's diff-based approach.
- `tickets/active/v0-v2-apply-equivalence.md` — overall Spec/Cycle equivalence plan; documents the residue-vs-walk decision and the conditional next bridge.
- `tickets/superseded/walk-based-pipeline.md` — failed walk approach to avoid.

## Update Log

### 2026-06-24 — Ticket created
Scoped Leg 3. Confirmed with user: Canonical may use Spec freely; the "no Spec link" constraint is Leg 4 (`CycleSieveSequence`) only. Selected diff-based induction (`ClassicCycleIntegralProperties` pattern) as the primary proof idiom, with `mergedGapPrefix`/`indexOfAccepted` as fallback. Walk approach explicitly excluded (3 prior timeouts).

### 2026-06-24 — First single-gap lemma verified
Added `CanonicalCycleSieve.assertNextFirstGapMatchesSpecNext(nextPeriod)`.

**Statement:** `spec.next(1) - spec.next(0) == spec.next.gapList(0, nextPeriod).head`, proved without scanning positions.

**Why this approach (not the diff idiom yet):** For the *first* gap, the cleanest statement is just `spec.next(1) - spec.next(0)`, which by `apply`'s base case reduces to `spec.next(1) - spec.next.head.value`. The `gapList` head is definitionally `apply(from+1) - apply(from)`, so the proof is pure arithmetic substitution plus `assertApplyMonotonic`. No `indexOfAccepted` and no diff induction needed at this smallest step.

**Validation:** `just verify` passed with `9001 valid: 9001 (8961 from cache, 20 trivial) invalid: 0 unknown: 0`. +30 VCs over the previous green state (8971).

**Lesson:** The single-gap case is trivial because both sides are direct `apply` differences. The hard part (matching the *whole* gap list) is where the strategy choice matters; the diff idiom will enter there. This confirms the "smallest meaningful step first" approach from `small-changes` is paying off: we have a green foundation before tackling the list-level induction.

**Next:** Either (a) lift to the full list via diff induction, or (b) first add a positional single-gap lemma `assertNextGapAtMatchesSpecNext(i)` generalizing this to arbitrary `i`, mirroring `assertNextGapEqualsCurrentGapSum`. Leaning (b) as the next atomic step, since it's the natural generalization and consumes the same pattern.

### 2026-06-24 — Positional single-gap lemma verified (with one fixed timeout)
Added `CanonicalCycleSieve.assertNextGapAtMatchesSpecNext(nextPeriod, index)`.

**Statement:** For any `0 <= index < nextPeriod`,
`spec.next(index + 1) - spec.next(index) == spec.next.gapList(0, nextPeriod).apply(index)`.

This generalizes `assertNextFirstGapMatchesSpecNext` from `index = 0` to any valid index, and is the per-position input to the list-level equality.

**Attempt 1 — timeout (VC at CanonicalCycleSieve.scala:549):** the precondition `index < gapList.size` for `gapList(0, nextPeriod).apply(index)` timed out at 120s. The solver could not connect `index < nextPeriod` to `gapList(0, nextPeriod).size == nextPeriod` on its own.

**Attempt 2 — fix and verify:** added one `assert(spec.next.assertGapListSize(0, nextPeriod))` to discharge the size precondition before the `.apply(index)` call. Verified:
`total: 9033 valid: 9033 (8993 from cache, 20 trivial) invalid: 0 unknown: 0`.
+32 VCs over the previous clean green (9001).

**Supporting change:** `SpecSieveSequence.assertGapListApplyEqualsGapAtPosition` was `private`; promoted to public so the Canonical lemma can consume it. Visibility-only change, no logic change.

**Lesson (candidate for LEARNINGS.md):** When a lemma calls `list.apply(index)` with `index` bounded by an *external* parameter (here `nextPeriod`) rather than by `list.size` directly, Stainless cannot synthesize the size precondition even when `index < externalBound` is required. Always precede such an `.apply` with an explicit `assertGapListSize` (or equivalent) so the bound is locally available. This is the same family of issues as LEARNINGS 1.2 (facts must be locally visible to the solver, not just globally true).

**Next:** Lift from per-position equality to full list equality. Two candidate idioms: (a) induction on `nextPeriod` using `assertNextGapAtMatchesSpecNext` for the head + recursive IH for the tail (mirrors `SpecSieveSequence.assertMergedGapPrefixMatchesNext`); (b) diff-based induction via `ClassicCycleIntegralProperties.assertSameDiffAfterCycle`. Leaning (a) since the per-position lemma is already verified and the list-equality induction is a direct structural lift.

### 2026-06-24 — List-equality lemma verified (after fixing a real bug in attempt 1)
Added `CanonicalCycleSieve.nextGapList(from, count)` (builder) and
`CanonicalCycleSieve.assertNextGapListMatchesSpecNext(from, count)` (lemma).

**Statement:** `nextGapList(from, count) == spec.next.gapList(from, count)` for all `from, count >= 0`.

This is the list-level lift: the Canonical-computed next gap list (built directly from `spec.next` adjacent differences, forward order) equals Spec's own `gapList`, element-for-element.

**Attempt 1 — FAILED (2 timeouts, `unknown: 2`):** Two real problems, not just solver weakness:
1. **Builder-order bug (my error):** the first builder `(spec.next(count) - spec.next(count-1)) :: nextGapList(count-1)` produced the list in REVERSED order — `[gap(count-1), ..., gap(0)]` — while `spec.next.gapList` is forward-ordered. The equality being proved was simply false. The solver timed out choking on an unprovable goal.
2. **Recursion-precondition timeout (LEARNINGS 2.1 family):** the recursive call `assertNextGapListMatchesSpecNext(nextPeriod - 1)` needs the period anchor `spec.next(nextPeriod - 1) == head + modulus`, which does NOT follow from the outer anchor on `nextPeriod`.

**Attempt 2 — FIX and verify:** Rewrote the builder to forward order with a sliding `from` parameter, mirroring `SpecSieveSequence.gapList`'s own recursion shape exactly:
```scala
(spec.next(from + 1) - spec.next(from)) :: nextGapList(from + 1, count - 1)
```
and restructured the induction to recurse on `count` with `from + 1`, mirroring the verified `assertGapListPositive`/`assertGapListApplyEqualsGapAtPosition` pattern. This keeps the induction self-contained — no period-anchor precondition needs to be re-derived at recursive calls. Verified:
`total: 9062 valid: 9062 (9019 from cache, 20 trivial) invalid: 0 unknown: 0`.
+29 VCs over the previous clean green (9033).

**Supporting changes:** `SpecSieveSequence.assertGapListFirstEqualsGap` promoted `private → public` (visibility-only), so the lemma can consume it for the head case.

**Lessons (candidates for LEARNINGS.md):**
- **Builder/list-equality bugs are easy to miss.** When proving `myBuilder == specBuilder` by induction, FIRST sanity-check the builder produces the same order as the spec builder on paper. A reversed builder makes the goal unprovable, and the solver expresses this as a timeout rather than a counterexample — which looks like solver weakness but is actually a logic bug.
- **Sliding-window induction over `from` beats fixed-`from` induction over `count`** when the list builder recurses on `from + 1`. The period anchor / other preconditions stay local; no re-derivation needed at recursive calls. This is the same shape used by every verified list lemma in `SpecSieveSequence` (`assertGapListPositive`, `assertGapListSize`, `assertGapListApplyEqualsGapAtPosition`).

**Status of Leg 3:** The direct-difference next gap list now has a verified equality to `spec.next.gapList`. What remains is connecting the *cycle strategy* (the walk/rotate pipeline, or an equivalent cycle-arithmetic computation) to this list — i.e., proving the cycle strategy's output equals `nextGapList` (and therefore `spec.next.gapList`). That is the genuinely hard producer theorem.

### 2026-06-24 — STRATEGY CORRECTION: transfer Spec's gap facts through assertApplyMatches
User feedback (2026-06-24): the perceived "complexity" of Leg 3 was self-inflicted. Spec has already proven gap periodicity (`assertGapPeriodic`) and gap merging (`assertMergeGapEqualsOldGapSum`, `mergedGapPrefix`). And Leg 2 has already proven the canonical cycle replicates Spec at every index (`assertApplyMatches`: `cycle(k) == spec(k)` for all `k >= 0`).

Therefore every Spec gap fact transfers to the canonical cycle by rewriting each `spec.apply(i)` to `cycle(i)` through the verified equivalence — **no new pipeline, no walk, no residue computation**. The previous framing ("connect the cycle strategy to nextGapList") was chasing a hard theorem that isn't required.

**Revised Leg 3 plan:** add transfer lemmas, one per Spec gap fact:
1. `assertGapPeriodicMatchesSpec(k, period)` — periodicity transfer. **DONE.**
2. `assertMergeGapEqualsOldGapSumMatchesSpec(...)` — merge transfer (next).
3. (possibly) `assertGapSumMatchesSpec(period)` — period-sum transfer.

Each is a pure transfer: call the Spec lemma, rewrite through `assertApplyMatches`, conclude. No timeouts expected.

### 2026-06-24 — Periodicity transfer verified (first attempt)
Added `CanonicalCycleSieve.assertGapPeriodicMatchesSpec(k, period)`.

**Statement:** `cycle(period + k + 1) - cycle(period + k) == cycle(k + 1) - cycle(k)`.

**Proof:** pure transfer — `spec.assertGapPeriodic(k, period)` gives the Spec-side equality; four calls to `assertApplyMatches` rewrite `spec(...)` → `cycle(...)` at the four positions `k, k+1, k+period, k+period+1`.

**Validation:** `just verify` passed first attempt with `9087 valid: 9087 (9043 from cache, 20 trivial) invalid: 0 unknown: 0`. +25 VCs over the previous green (9062).

**Lesson:** This confirms the user's point — when a property is already proven on Spec and Canonical is proven equivalent to Spec index-by-index, the transfer is mechanical (call + rewrite) and verifies trivially. Do NOT re-derive the property from scratch on the cycle side.

### 2026-06-24 — Scoping principle for the cycle rule list
User guidance (2026-06-24): the rules stated over `canonical.cycle` should carry **only what the equivalence check requires**, not everything that is true. For example, the next head is in fact prime (proven on the Spec side), but the cycle does not need to know that for the gap/apply equivalence. Adding "head is prime" as a cycle rule would add complexity without load-bearing value.

**Decision rule for what becomes a cycle fact:**
- INCLUDE if a downstream equivalence lemma (or the eventual Leg-4 `CycleSieveSequence` proof) consumes it.
- EXCLUDE if it's merely true but not required by any consumer.

So far the load-bearing cycle facts are: gap positivity, gap periodicity, the copy rule, the merge rule, and the period sum. "Head is prime" is excluded.

### 2026-06-24 — Gap positivity transfer verified
Added `CanonicalCycleSieve.assertGapPositiveMatchesSpec(k)`.

**Statement:** `cycle(k + 1) - cycle(k) > 0` for all `k >= 0`.

**Proof:** pure transfer — `spec.assertGapPositive(k)` gives the Spec-side positivity; two calls to `assertApplyMatches` rewrite `spec(k), spec(k+1)` → `cycle(k), cycle(k+1)`.

**Validation:** `just verify` passed first attempt with `9100 valid: 9100 (9068 from cache, 20 trivial) invalid: 0 unknown: 0`. +13 VCs over the previous green (9087).

**Next:** The gap copy rule — if `cycle(k)` and `cycle(k+1)` are both not multiples of the new head `cycle(1)`, the next gap is `cycle(k+1) - cycle(k)`. Transfers from `SpecSieveSequence.assertFilterPreservesNextGap`.

### 2026-06-24 — Copy rule attempt 1 TIMED OUT (logical gap, not solver weakness)
Attempted `assertCopyGapMatchesSpec(k)` with preconditions
`Calc.mod(cycle(k), cycle(1)) != 0` and `Calc.mod(cycle(k+1), cycle(1)) != 0`.

**Timeout:** `unknown: 2` at precondition 4/6 of `spec.assertFilterPreservesNextGap`,
which is `spec.next.accepts(spec(k))`.

**Root cause (genuine logical gap, NOT solver weakness):** the cycle-side
hypothesis "not a multiple of `cycle(1)`" only gives coprimality against the
new head. But `spec.next.accepts(v)` requires coprimality against the **whole**
`cycle.primes` list (new head + tail). `assertNextAcceptsMatches` bridges
`spec.next.accepts(v) == SieveUtils.isCoprime(v, cycle.primes)` — so the
hypothesis is too weak by exactly the tail-coprimality part.

**The catch:** for a *current* generated value `cycle(k)`, tail-coprimality
(`isCoprime(cycle(k), cycle.primes.tail)`) IS true (it's why `cycle(k)` was
generated in the first place). So the right statement is:
> if `cycle(k)` survives the tail filter (always true for generated values)
> AND `cycle(k)`, `cycle(k+1)` are not multiples of the new head,
> then the gap is copied.

The fix is to either (a) strengthen the precondition to full coprimality
against `cycle.primes`, or (b) prove a cycle-side lemma that generated values
are tail-coprime and layer the copy rule on top.

**Action taken:** commented out the lemma (per `never-destroy`), restored green
at `9100 valid`. Promoted `spec.assertFilterPreservesNextGap` to public
(benign; no caller now, but keeps it available for the retry).

**Status:** STOPPED per `stop-and-ask` (1 of 3 attempts; this is a logical gap
worth user input, not a retry-the-same-thing situation). Awaiting direction
between options (a) and (b) above.

### 2026-06-24 — Copy rule correction approved

The previous `assertFilterPreservesNextGap` is not reusable for the actual
`spec.next` stage because it also requires:

```text
nextSeq.head.value == head.value
```

That is false for a real next stage, whose head is `spec(1) > spec.head`.
Tail-coprimality alone therefore cannot repair the old lemma.

The corrected pure-Spec lemma will use the actual load-bearing contract:

```text
nextSeq.filterValues.tail == filterValues
nextSeq.head.value >= head.value
nextSeq.accepts(apply(k))
nextSeq.accepts(apply(k + 1))
```

From those assumptions:

1. `apply(k)` and `apply(k+1)` both occur in `nextSeq`.
2. They are consecutive in the old stream.
3. Any `nextSeq` value between them is accepted by the old tail filter because
   `nextSeq.filterValues.tail == filterValues`.
4. Therefore no third accepted value can lie strictly between them in either
   stream.

The conclusion is the copied-gap equality:

```text
nextSeq(nextSeq.indexOfAccepted(apply(k)) + 1)
  - nextSeq(nextSeq.indexOfAccepted(apply(k)))
==
apply(k + 1) - apply(k)
```

Canonical will then use `assertWalkDecisionMatchesNextAccept` at `k` and
`k + 1` to establish the two next-acceptance assumptions, and transfer the old
values through `assertApplyMatches`.

### 2026-06-24 — Corrected Spec copy lemma attempt 1 timed out

Attempted
`SpecSieveSequence.assertConsecutiveAcceptedByNextPreservesGap(nextSeq, k)`
with the corrected no-equal-head contract described above.

The mathematical body mostly verified, including:

- projecting a `nextSeq` value through `nextSeq.filterValues.tail` into old
  acceptance;
- proving the old successor is at or below the next-sequence successor;
- proving the next-sequence successor is at or below the accepted old
  successor;
- concluding the copied-gap equality.

However, focused verification timed out on three precondition VCs before or at
the beginning of the body:

```text
nextSeq.accepts(apply(k))
nextSeq.accepts(apply(k + 1))
nextSeq.indexOfAccepted(apply(k)) requires apply(k) >= nextSeq.head.value
```

Stainless did not retain the lower-bound component hidden inside the
cross-instance `accepts` requirements. Result:

```text
47 total, 44 valid, 3 unknown, 3 timeouts at 120 seconds each
```

This matches `LEARNINGS.md` section 18: cross-instance calls can lose simple
arithmetic facts when several unfoldings share one VC.

The attempted lemma was commented out, not deleted. Full verification was
restored:

```text
9100 valid, 0 invalid, 0 unknown
```

Do not retry the same shape. The next viable approach is to isolate the lower
bound as its own tiny lemma or change the copy lemma contract to carry explicit
facts:

```text
apply(k) >= nextSeq.head.value
apply(k + 1) >= nextSeq.head.value
```

Only one of those changes should be tried in the next verification cycle.

### 2026-06-24 — Corrected Spec copy lemma attempt 2 verified

Retried the same mathematical sandwich proof with the two domain facts exposed
as explicit preconditions:

```text
apply(k) >= nextSeq.head.value
apply(k + 1) >= nextSeq.head.value
```

This separates two logically distinct obligations:

- `nextSeq.accepts(value)` says that the value passes the next filter;
- `value >= nextSeq.head.value` says that the value belongs to the searchable
  domain of `nextSeq.indexOfAccepted`.

With those facts available directly, Stainless verifies
`assertConsecutiveAcceptedByNextPreservesGap`. The lemma proves that when two
consecutive old-sequence values are both accepted by the next sequence, they
remain consecutive there, so their gap is copied unchanged. It does not assume
equal sequence heads.

Focused verification:

```text
49 valid, 0 invalid, 0 unknown
```

Full verification:

```text
9149 valid, 0 invalid, 0 unknown
```

**Next:** transfer this pure-Spec fact through `CanonicalCycleSieve`. The
canonical lemma must use the old head `cycle.head` as the newly added filter,
not `cycle(1)`: `cycle(1)` is the next sequence's starting value, while
`cycle.head` is the prime newly included in `spec.next.filterValues`.

### 2026-06-24 — Canonical copy transfer attempt 1 timed out

Attempted `CanonicalCycleSieve.assertCopyGapMatchesSpec(k)` with the corrected
filter condition:

```text
Calc.mod(cycle(k), cycle.head) != 0
Calc.mod(cycle(k + 1), cycle.head) != 0
```

and the corrected next-stage index:

```text
nextIndex = spec.next.indexOfAccepted(spec(k))
```

The proof body was layered through `assertApplyMatches`,
`assertWalkDecisionMatchesNextAccept`, and the newly verified
`assertConsecutiveAcceptedByNextPreservesGap`.

**Timeout:** `nextIndex` was declared before those assertions. Stainless checks
method-call preconditions at the declaration site, so it timed out before
entering the useful proof body on both requirements of `indexOfAccepted`:

```text
spec(k) >= spec.next.head.value
spec.next.accepts(spec(k))
```

This is an ordering problem in the attempted implementation, not a new
mathematical gap. The attempted method is commented out. Full verification was
restored:

```text
9149 valid, 0 invalid, 0 unknown
```

**Next planned attempt:** establish acceptance and lower bounds first, invoke
`assertConsecutiveAcceptedByNextPreservesGap`, and only then evaluate
`indexOfAccepted(spec(k))`. Do not place any `indexOfAccepted` call, including a
`val` initializer, before those facts.

### 2026-06-24 — Canonical copy transfer attempt 2 timed out

Moved `indexOfAccepted(spec(k))` below all acceptance and lower-bound
assertions, exactly as planned. This removed both index precondition timeouts
from attempt 1.

The next isolated failure was:

```text
nextSeq.accepts(spec(k))
```

even after calling:

```text
assertWalkDecisionMatchesNextAccept(k)
```

Focused verification reached 10 of 59 obligations before the acceptance
assertion timed out at 120 seconds. The diagnostic context retained the walk
lemma call and the lower bound, but did not cheaply rewrite its equality result
through both representation equality and the local `nextSeq = spec.next` alias.

The method remains commented out. Full verification was restored:

```text
9149 valid, 0 invalid, 0 unknown
```

**Current conclusion:** the pure-Spec copy theorem is verified. The canonical
wrapper is not yet verified. Index ordering is fixed; the remaining blocker is
the cross-representation acceptance transfer.

**Next planned unit:** create one small canonical lemma whose postcondition is
directly:

```text
Calc.mod(cycle(k), cycle.head) != 0
  ==> spec.next.accepts(spec(k))
```

for `k >= 1`. Its body should call `assertApplyMatches(k)` and
`assertWalkDecisionMatchesNextAccept(k)`, then expose only this implication.
The copy lemma can consume that direct endpoint without asking Stainless to
reconstruct the equality inside its larger VC.

### 2026-06-24 — Acceptance transfer attempt 3 timed out

Created the planned isolated lemma
`assertWalkNonMultipleAcceptedByNext(k)`. It had only the two essential
requirements:

```text
k >= 1
Calc.mod(cycle(k), cycle.head) != 0
```

Its body called `assertWalkDecisionMatchesNextAccept(k)`, selected the positive
acceptance branch for `cycle(k)`, and then used `assertApplyMatches(k)` to
rewrite the endpoint to `spec(k)`.

Focused verification generated only 17 obligations, but timed out on:

```text
spec.next.accepts(cycle(k))
```

The final `spec.next.accepts(spec(k))` obligation was also unknown. Result:

```text
17 total, 15 valid, 0 invalid, 2 unknown
```

This establishes that the problem is not caused by the size of the copy-gap
lemma or by the local `nextSeq` alias. Stainless is not exporting the positive
branch of the boolean equivalence from
`assertWalkDecisionMatchesNextAccept` cheaply enough for a caller.

The attempted lemma is commented out. Full verification is restored:

```text
9149 valid, 0 invalid, 0 unknown
```

This is the third failed canonical acceptance-transfer attempt. Per
`AGENTS.md`, stop before trying another variation.

**Decision required before continuing:**

1. Strengthen or reshape `assertWalkDecisionMatchesNextAccept` so the needed
   positive acceptance fact is part of a direct implication/postcondition,
   then reverify that existing lemma.
2. Avoid consuming the equivalence and prove next acceptance directly inside a
   new small lemma from tail coprimality plus non-divisibility by `cycle.head`.

Option 2 duplicates part of the existing bridge proof but gives Stainless a
straight-line positive theorem. Option 1 is less duplication but changes a
currently verified load-bearing lemma and may reproduce the same timeout.

### 2026-06-24 — Direct constructive acceptance test

Tested option 2 as `assertCurrentNonMultipleAcceptedByNext(k)`. The proof
constructs next acceptance directly:

1. `assertApplyMatches(k)` transfers the current value to `spec(k)`.
2. `spec.accepts(spec(k))` provides coprimality with the old tail filter.
3. The nonzero remainder against `cycle.head` supplies the newly added filter.
4. Structural unfolding proves coprimality with all of `cycle.primes`.
5. Direct list equalities prove `spec.next.filterValues == cycle.primes`.
6. The final expression proves `spec.next.accepts(spec(k))`.

Focused result:

```text
46 total, 45 valid, 0 invalid, 1 unknown
```

The single timeout was:

```text
assert(value >= nextSpec.head.value)
```

This assertion is redundant. Stainless subsequently verified the same
lower-bound precondition at the final `nextSpec.accepts(spec(k))` call in
0.1 seconds, and it verified the final acceptance postcondition in 0.4 seconds.
All coprimality and filter-list construction obligations passed.

The attempted lemma is commented out and full verification is restored:

```text
9149 valid, 0 invalid, 0 unknown
```

**Recommended next iteration:** re-enable the exact constructive lemma and
remove only the redundant standalone lower-bound assertion. Do not otherwise
change the proof. This is materially different from the earlier equivalence
approach: the desired final theorem already verified in this test.

### 2026-06-24 — Direct constructive acceptance attempt 2 timed out

Applied exactly the recommended change: re-enabled the constructive lemma and
removed only:

```text
assert(value >= nextSpec.head.value)
```

Focused verification then timed out on the lower-bound precondition of the
final call:

```text
nextSpec.accepts(spec(k))
```

Result:

```text
45 total, 44 valid, 0 invalid, 1 unknown
```

The acceptance postcondition itself remained valid, and every coprimality and
filter-list equality obligation remained valid. Removing the standalone
assertion did not eliminate the expensive lower-bound VC; it moved that VC to
the final consumer. The earlier interpretation that the final call had already
proved the bound cheaply was cache/run-order dependent and was too optimistic.

The method is commented out again. Full verification is restored:

```text
9149 valid, 0 invalid, 0 unknown
```

**Current precise blocker:** prove or carry
`spec(k) >= spec.next.head.value` without combining it in one VC with the full
constructive coprimality context. A future plan should isolate this ordering
fact in a separate lemma or add it as an explicit requirement to the
acceptance-transfer lemma. Do not retry another assertion-order variation.

### 2026-06-24 — Isolated next-head ordering lemma verified

Added `CanonicalCycleSieve.assertCurrentValueAtOrAboveNextHead(k)`:

```text
k >= 1 ==> spec(k) >= spec.next.head.value
```

The proof follows an already verified local pattern:

```text
spec(1) <= spec(k)                  [current Spec monotonicity]
spec(1) == cycle(1)                 [canonical apply equality]
cycle(1) == spec.next.head.value    [next-head correspondence]
```

Focused verification:

```text
21 valid, 0 invalid, 0 unknown
```

Full verification:

```text
9170 valid, 0 invalid, 0 unknown
```

This confirms the ordering fact is independently cheap and stable. The next
small change should make the constructive acceptance lemma consume this public
ordering lemma before its final `accepts` call. No coprimality proof needs to be
changed.

### 2026-06-24 — Constructive next acceptance verified

Re-enabled `assertCurrentNonMultipleAcceptedByNext(k)` and replaced its local
ordering reconstruction with:

```text
assertCurrentValueAtOrAboveNextHead(k)
```

No coprimality or filter-list reasoning changed. The lemma now verifies:

```text
k >= 1
Calc.mod(cycle(k), cycle.head) != 0
------------------------------------------
spec.next.accepts(spec(k))
```

Focused verification:

```text
43 valid, 0 invalid, 0 unknown
```

The final `accepts` lower-bound precondition, which previously timed out at
120 seconds, verified in 0.1 seconds.

Full verification:

```text
9213 valid, 0 invalid, 0 unknown
```

**Lesson:** the timeout was caused by combining the ordering derivation with
the full constructive coprimality context in one VC. Exporting the ordering
fact through a small verified lemma made the final consumer cheap and stable.

**Next:** re-enable the corrected `assertCopyGapMatchesSpec(k)`, call
`assertCurrentNonMultipleAcceptedByNext` at `k` and `k + 1`, and then consume
the already verified pure-Spec
`assertConsecutiveAcceptedByNextPreservesGap`.
