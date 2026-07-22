# Generalize Mod-Zero Shift to Negative Offsets

## START HERE

Micro-goal: check whether `ModOperations.modZeroPlusC` can be generalized from
`c >= 0` to arbitrary integer `c`, and if so create/verify the generalized
property.

## Goal

The current source lemma:

```scala
def modZeroPlusC(a: BigInt, b: BigInt, c: BigInt): Boolean = {
  require(b != 0)
  require(c >= 0)
  require(mod(a, b) == 0)
  ...
}.holds
```

proves:

```math
a \text{ mod } b = 0 \implies (a + c) \text{ mod } b = c \text{ mod } b
```

only for nonnegative `c`. Mathematically, the property should hold for every
integer `c`, because `Calc.mod` and `DivMod.solve` support negative dividends.

## Expected Result

Either:

1. Generalize `modZeroPlusC` by removing `require(c >= 0)` and verify it; or
2. Add a new verified lemma, for example:

```scala
def modZeroPlusAnyC(a: BigInt, b: BigInt, c: BigInt): Boolean = {
  require(b != 0)
  require(Calc.mod(a, b) == 0)
  Calc.mod(a + c, b) == Calc.mod(c, b)
}.holds
```

If that generalized plus lemma is awkward for Stainless, prove the subtraction
case directly as a special lemma:

```scala
def modZeroMinusC(a: BigInt, b: BigInt, c: BigInt): Boolean = {
  require(b != 0)
  require(Calc.mod(a, b) == 0)
  Calc.mod(a - c, b) == Calc.mod(-c, b)
}.holds
```

For the generalized plus lemma, the subtraction corollary should then be
available by substituting `-c`:

```math
a \text{ mod } b = 0 \implies (a - c) \text{ mod } b = (-c) \text{ mod } b
```

## Current Hypothesis

The `c >= 0` precondition appears to be an old simplification rather than a
mathematical requirement. The existing proof already uses:

- `ModOperations.modAdd(a, b, c)`, which requires only `b != 0`
- `ModIdempotence.modIdempotence(c, b)`, which handles negative `c`

So the generalized lemma may verify with only a precondition removal.

## Risks

- `modZeroPlusC` may have callers that rely on the current precondition shape.
  Search all callers before changing its contract.
- If removing the precondition causes Stainless trouble, prefer adding a new
  lemma rather than destabilizing the existing one. If the generalized plus
  lemma is still difficult, try the direct subtraction lemma `modZeroMinusC`.
- If any Scala source changes are made, run verification. For a focused first
  pass, use `just verify modZeroPlusC` or the new lemma name. For acceptance,
  use the chapter verification path required by AGENTS.md.

## Search Plan

- Read `src/main/scala/v1/chapter2/div/properties/ModOperations.scala`.
- Search callers of `modZeroPlusC`.
- Read `ModOperations.modAdd` and `ModIdempotence.modIdempotence`.
- Check whether `Summary.scala` should include the generalized property.

## Validation

- If source changes are made, verify the changed lemma with Stainless.
- Run the relevant chapter verification (`just verify-ch 2`) before marking the
  proof work done.
- If the property verifies, update `articles/chapter2/modulo.md` to state the
  generalized divisible-base shift property and optionally the subtraction
  corollary.
- Update `OBJECTS.md` if a new lemma is added.

## Article Note

The article should not claim the generalized property is formally verified until
the source proof exists and passes verification. Until then, it can be discussed
only as a mathematical expectation or pending proof.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-22 | Confirmed the hypothesis: the `modZeroPlusC` proof body never used `c >= 0` — it only calls `modAdd(a, b, c)` (requires `b != 0`) and `ModIdempotence.modIdempotence(c, b)` (already branches on `c >= 0` internally). Removed `require(c >= 0)` and reran `just verify modZeroPlusC`: 30/30 valid, no changes needed to the proof body. | Chose option 1 (generalize in place) over adding a new lemma, since no proof rework was required. |
| 2026-07-22 | Searched all callers (`SpecSieveSeqPeriodProperties`, `SpecSieveSequence`, `BezoutUtils`, `PrimeProperties`, both `ModOperationsTest` files). All pass nonnegative `c` (`c.abs`, `BigInt(1)`, etc.), so widening the precondition is backward compatible — no caller changes needed. | No source changes beyond `ModOperations.scala`. |
| 2026-07-22 | Ran `just verify-ch 2` (1374/1374 valid), `just verify-ch 5` (2145/2145 valid), `just verify-ch 6` (4390/4390 valid), and the full `sbt` test suite (12531 VCs valid, 8/8 ModOperationsTest cases pass) — all green. | Full acceptance validation passed. |
| 2026-07-22 | `articles/chapter2/modulo.md`'s "Modular Shift Invariance under Divisible Base" section already stated the property for `∀ a, b, c ∈ ℤ` with no `c >= 0` restriction — it was already the generalized (previously overclaimed) form. `OBJECTS.md`'s entry for `modZeroPlusC` also never mentioned a `c >= 0` precondition. Neither needed edits now that the source matches. The subtraction corollary requested in the ticket is already available for free by calling `modZeroPlusC(a, b, -c)`, so no separate `modZeroMinusC` lemma was added. `Summary.scala` does not reference `modZeroPlusC` (it uses `modAdd`/`modLess` directly), so no change there either. | Strengthened `ModOperationsTest.scala`'s `modZeroPlusC` test to also exercise negative `c` directly (previously only tested via `c.abs`). Ticket closed — done. |
