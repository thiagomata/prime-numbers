# V0 Filter Preserves Next Position

**Created:** 2026-06-19
**Status:** Plan phase — not yet started
**Depends on:** `v0-gap-properties.md` (P1/P2/P3 completed, 6335 valid)

## Related Tickets

- `v0-gap-properties.md` — P1-P3 gap properties proved. Establishes gap lemmas used for reasoning about position shifts.
- `v0-residue-cycle-proof.md` — P2 (Residues Completeness) + P3 (Residue Periodicity). Foundation for V0 completeness and periodicity.

## Goal

Add a lemma `assertFilterPreservesNextPosition(nextSeq, k)` to `SpecSieveSequence` that proves:

Given two V0 sequences with the same head, where `nextSeq` has one additional filter prime `p`:
- `V = this.apply(k) = nextSeq(vIdx)` (same value, different indices)
- `W = this.apply(k + 1)` (next value in current seq)
- If `Calc.mod(W, p) != 0` (W survives the extra filter)
- Then `W == nextSeq(vIdx + 1)` (W is also the next value in nextSeq)

## Current State

- 6335 valid, 0 invalid, 0 unknown
- `applySkipsNoAcceptedBetween(k)` — proves `noAcceptedBetween(apply(k-1)+1, apply(k))`
- `nextDoesNotPassAcceptedValue(k, value)` — proves `apply(k) < value ∧ accepts(value) ⇒ apply(k+1) <= value`
- `applyStrictlyIncreases(k)` — proves `apply(k+1) > apply(k)`
- `indexOfAccepted(value)` — returns k where `apply(k) == value`, proving completeness

## Proof

Let V = seq_n(k), W = seq_n(k+1), p = nextSeq.filterValues.head.

**Step 1 — W is accepted by nextSeq:**
- `seq_n.accepts(W)` (W ∈ seq_n) ⇒ `SieveUtils.isCoprime(W, F)` where F = seq_n.filterValues
- `nextSeq.filterValues == p :: F` (precondition)
- `Calc.mod(W, p) != 0` (precondition)
- Therefore `SieveUtils.isCoprime(W, p :: F)` ⇒ `nextSeq.accepts(W)`

**Step 2 — No value in (V, W) is accepted by nextSeq:**
- `applySkipsNoAcceptedBetween(k+1)` ⇒ `noAcceptedBetween(V+1, W)` in seq_n
- `accepts_nextSeq(Z) ⇒ accepts_seq_n(Z)` (since p :: F is stricter than F alone)
- Therefore no Z ∈ (V, W) satisfies `accepts_nextSeq(Z)`

**Step 3 — vIdx = nextSeq.indexOfAccepted(V):**
- `nextSeq(vIdx) = V < W` and `nextSeq.accepts(W)` (Step 1)
- `nextSeq.nextDoesNotPassAcceptedValue(vIdx, W) ⇒ nextSeq(vIdx+1) <= W`
- If `nextSeq(vIdx+1) < W`, then `nextSeq(vIdx+1) ∈ (V, W)` and `accepts_nextSeq(nextSeq(vIdx+1))`
- Contradicts Step 2, therefore `nextSeq(vIdx+1) >= W`
- Therefore `nextSeq(vIdx+1) == W`

## Implementation Plan

1. Add `assertFilterPreservesNextPosition(nextSeq, k)` to SpecSieveSequence — one `.holds` lemma
2. Verify

## Risks

- `noAcceptedBetweenRejects` is called on `this`, but needs the value `nextSeq(vIdx+1)`. The solver must track that `nextSeq(vIdx+1)` is within `(V, W)`. Need explicit assertions.
- `accepts_nextSeq(Z) ⇒ accepts_seq_n(Z)` requires unfolding `SieveUtils.isCoprime` — need explicit assertion.
- `nextDoesNotPassAcceptedValue` is private. Accessible from same class, but called on `nextSeq` instance. Should work in Scala/Stainless.

## Validation

- `just verify`: 0 invalid, 0 unknown, valid >= 6335
- Verify green before and after

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-06-19 | Ticket created. Three-step proof identified: (1) W accepted by nextSeq, (2) no Z in (V,W) accepted by nextSeq, (3) nextSeq(vIdx+1) == W by contradiction + nextDoesNotPassAcceptedValue. | Implement lemma. |
| 2026-06-19 | **Attempt 1**: `if (z < W) { assert(noAcceptedBetweenRejects(...)); assert(false) }` — postcondition timed out. The solver couldn't prove `z >= W` from the contradiction. Added explicit `assert(z >= W)`. | Move to alternative approach. |
| 2026-06-19 | **Attempt 2**: `assert(noAcceptedBetweenRejects(...))` inside `if` timed out on precondition check. Added explicit `isCoprime(z, filterValues)` + `accepts(z)` assertions — those verified, but `noAcceptedBetweenRejects` still timed out. | Switch to direct inequality using `nextDoesNotPassAcceptedValue`. |
| 2026-06-19 | **Attempt 3**: Clean proof using `nextDoesNotPassAcceptedValue` in BOTH directions: `this.nextDoesNotPassAcceptedValue(k, z)` gives `W <= z`; `nextSeq.nextDoesNotPassAcceptedValue(vIdx, W)` gives `z <= W`. Therefore `z == W`. **6379 valid (+44), 0 invalid, 0 unknown.** Verified in 20.10s. | Done. Update OBJECTS.md. |
