# Stainless Verification Lessons

Consolidated lessons learned across all tickets in this project — techniques,
pitfalls, and patterns that worked.

## 1. Lemma Propagation

### 1.1 Private lemmas reduce VC complexity at call sites

External `.holds` lemmas DO propagate their proven equalities — they are used
successfully throughout the codebase (e.g., `ATimesBSameMod`, `ALessBSameModDecreaseDiv`,
`ModOperations.modZeroPlusC`). The solver can consume their return expressions
at call sites.

However, when a `.holds` lemma's return expression is complex (e.g., involves
`isCoprime` with multiple arguments, conditional branches, or quantifier-like
reasoning), the solver may time out trying to USE it at a call site — not
because the equality is hidden, but because re-deriving the fact in a new
context is expensive.

**Solution:** Private lemmas inside the same class reduce VC complexity because
the solver sees the return expression directly without crossing a module
boundary. This is particularly effective when the needed fact is a simple
instance of a more general lemma.

```scala
// Instead of:
assert(SieveUtils.assertExpandedCoprime(r, i, modulus, primes))
// which may be expensive for the solver to inline at the call site:

// Use a private lemma that inlines the specific needed fact:
private def expandedCoprimePreservesFilter(r: BigInt, i: BigInt, modulus: BigInt, primes: List[BigInt]): Boolean = {
  isCoprime(r + i * modulus, primes)
}.holds
```

**Affected:** P3 `assertBlockShift` timeout. Solved by using V0's own private
`expandedCoprimePreservesFilter` instead of `SieveUtils.assertExpandedCoprime`.

### 1.2 `.ensuring` with explicit postcondition

**Problem:** Internal `assert()` inside `.holds` functions are cached but the
solver may not USE them at call sites (times out trying to re-derive the fact).

**Solution:** Put the needed equality directly in `.ensuring`:
```scala
def foo(k: BigInt): Boolean = {
  // body with internal assertions
  true
}.ensuring(res => {
  // call lemmas HERE to make their postconditions available
  res && theEqualityIWant
})
```

The `.ensuring` block makes the equality part of the function's POSTCONDITION,
which IS visible to callers.

**Affected:** P3 `assertBlockShift`. The inductive equality
`apply(k+p) == apply(k) + M` was originally asserted internally and timed out.
Moving it to `.ensuring` with lemma calls inside the block resolved the issue.

### 1.3 Return the equality directly (don't just assert it)

Instead of asserting internally and returning `true`, return the EQUALITY
expression itself:
```scala
def foo(k: BigInt): Boolean = {
  // ...
  apply(k + p) == apply(k) + M
}.holds  // the body IS the equality, .holds proves it's true
```

This is cleaner but has the same propagation issue — `.holds` still only caches
`true` at call sites. Use `.ensuring` (Section 1.2) for propagation.

### 1.4 `.holds` caching vs raw conjunctions

`.holds` lemmas cache internal `assert` statements and make them available
across function call boundaries. Raw conjunctions (non-`.holds`) are inlined by
the solver, giving different behavior.

No need to over-engineer postconditions to expose every internal fact — simple
`assert(...)` within `.holds` is sufficient. The solver uses cached assertions
across call boundaries.

**Source:** `dead-code-cleanup-and-euclid-article.md`

## 2. Induction and Recursion

### 2.1 `.holds` recursive calls don't propagate IH to callers

When a `.holds` function calls itself recursively and asserts the IH internally,
the solver may time out trying to USE the IH at the call site. The IH is "cached"
but the solver re-derives it from scratch.

**Solution:** Put the IH in `.ensuring` (see 1.2), or restructure the function
so the IH is the return value.

### 2.2 Induction needs `decreases` and explicit recursive calls

Stainless induction requires:
- `decreases(k)` annotation on the function
- An explicit recursive call: `assert(foo(k - 1))` or `val ih = foo(k - 1)`
- The IH must be explicitly stated (as an `assert` or return expression)

Without the explicit recursive call, `.decreases` only provides termination
checking, not inductive hypothesis.

## 3. Modulo Arithmetic

### 3.1 `modZeroPlusC` vs `modAdd` + `modIdempotence`

`modZeroPlusC(a, b, c)` directly proves `mod(a + c, b) == mod(c, b)` when
`mod(a, b) == 0`. This is a SINGLE lemma call instead of chaining `modAdd` +
`modIdempotence`. The solver handles one call much faster.

**Affected:** P1 `assertModIsCoprimeForAll`. Switched from `modAdd` +
`modIdempotence` to `modZeroPlusC` to resolve timeout.

### 3.2 `APlusMultipleTimesBSameMod` for periodicity

`APlusMultipleTimesBSameMod(a, b, m)` proves `mod(a + b*m, b) == mod(a, b)`.
This is the cleanest way to prove `mod(v + M, M) == mod(v, M)`.

**Affected:** P3 `assertApplyResidueCycles` postcondition timeout. Using
`modAdd` + `modIdempotence` timed out; `APlusMultipleTimesBSameMod` resolved it.

### 3.3 Avoid `Calc.mod` in loop-like patterns

Calling `Calc.mod` inside a loop/recursion creates a new VC per iteration. For
inductive proofs, compute the mod once outside and pass it as a parameter.

### 3.4 Never use `%` — always `Calc.mod` / `Calc.div`

The `%` operator is not natively supported by Stainless. Use `Calc.mod(a, b)`
and `Calc.div(a, b)` which use `DivMod` internally.

## 4. Product and Modulus

### 4.1 Prefix-product decomposition

To prove `Calc.mod(modulus, p) == 0` for each `p` in a list `values` where
`modulus == product(values)`, use the prefix-product approach:

```scala
val tailProd = SieveUtils.product(values.tail)
assert(modulus == p * tailProd)
assert(assertMultipleModZero(tailProd, p))
assert(Calc.mod(modulus, p) == 0)
```

This avoids needing `allElementsDivideProduct` (which requires
`allGreaterThan` preconditions that may be hard to satisfy).

**Pattern:** `expandedCoprimePreservesFilter`, `assertModIsCoprimeForAll` (P1),
`assertReverseCoprimePreservation` (P3 Lemma 1) all use this approach.

### 4.2 `primorialMatchesSieveProduct` is the product invariant

This lemma proves `filterModulus == SieveUtils.product(filterValues)`. It should
be called at the start of any lemma that needs the product equality.

## 5. List Functions

### 5.1 `contains` on lists can be expensive

`List.contains(v)` for a large list is O(n) recursion. Calling it inside a loop
creates O(n^2) VCs. Use structural induction aligned with the list's construction.

### 5.2 `generateResidues` completeness requires explicit lemma

`assertResiduesAllCoprime` proves soundness (all residues are coprime) but NOT
completeness (all coprime values are in the list). To prove completeness, use
structural recursion aligned with `generateResidues`:

```scala
def assertGenerateResiduesContainsCoprime(v, i, modulus, primes): Boolean = {
  require(isCoprime(v, primes))  // ...
  if (i == v) generateResidues(i, modulus, primes).contains(i)
  else { assertGenerateResiduesContainsCoprime(v, i+1, modulus, primes)
         generateResidues(i, modulus, primes).contains(v) }
}.holds
```

## 6. Timeout Resolution Strategies

### 6.1 Substitution chain

When the solver times out on a chain of lemmas, insert explicit intermediate
assertions:

```scala
val intermediate = expr1
assert(intermediate == expr2)  // explicit step
assert(final_result)
```

### 6.2 Use private lemmas from the same class

As noted in 1.1, private lemmas are inlined by the solver. When a timeout
persists with an external lemma, rewrite it as a private lemma in the same class.

### 6.3 Restructure to reduce VC count

- One lemma per verify cycle (AGENTS.md small-changes rule)
- Split large proofs into smaller `.holds` lemmas
- Use `decreases` on structural parameters (list size, modulus - i, k)

### 6.4 When timeout repeats 3 times, stop

After 3 failed attempts on the same VC, stop and ask for help. Do NOT try
variations. Document the error and the attempted fixes.

## 7. Structural Patterns

### 7.1 Reverse periodic direction

`expandedCoprimePreservesFilter` proves `isCoprime(r, values) ⇒ isCoprime(r + i*modulus, values)`.
The reverse direction `isCoprime(r + i*modulus, values) ⇒ isCoprime(r, values)` is
also true but NOT proved by any existing lemma. It uses the same identity:
`mod(v + M, p) == mod(v, p)`.

### 7.2 `indexOfAccepted` as a period finder

Instead of counting residues per block (which requires heavy counting lemmas),
use `p = indexOfAccepted(head + M)` as the period directly. This is the number
of accepted values in `[head, head + M)` — exactly what the induction needs.

### 7.3 Two-direction inequality for block shift

To prove `apply(k+p) == apply(k) + M`, prove two inequalities:
1. `apply(k+p) <= apply(k) + M` (using `nextDoesNotPassAcceptedValue` forward)
2. `apply(k) + M <= apply(k+p)` (using reverse periodic preservation + `nextDoesNotPassAcceptedValue` backward)

Each direction is proved independently, then combined with `assert(==)`.

## 8. Testing

### 8.1 Always run tests after verification

Verification proves the lemmas; tests prove the runtime behavior matches.
Run `just test` after `just verify` succeeds.

### 8.2 Check verify.log

`just verify` writes to `verify.log`. Check `grep "total:" verify.log` for
the summary. Timeouts appear as "unknown" in the valid/invalid/unknown count.

## 9. Common Pitfalls

### 9.1 `.ensuring` on class methods breaks type inference

Methods with `.ensuring` postconditions cannot be used as functions in
higher-order contexts. Use `.holds` or move to a companion object.

**Source:** `v0-next-level-construction.md`

### 9.2 Cannot `rm` files

The `rm` command is blocked. To clear logs, overwrite them or use `mv`.

### 9.3 Never use `git checkout`, `git revert`, `git push --force`

These are blocked by opencode.json. If state is wrong, stop and ask for help.

### 9.4 Never modify MemCycle, ModCycle, or CycleIntegral

These are core types with complex invariants. Changes to them cascade into
unpredictable verification failures.

## 10. SMT Limits

### 10.1 Deep number theory is beyond SMT

Bertrand's postulate, prime gaps, Jacobsthal function — none provable in SMT.
Z3 handles only simple divisibility and linear arithmetic.

**What failed:** Proving `apply(1) < head^2` without Bertrand. Case analysis
showed `searchBound(1)` can exceed `head^2` (at `head=11`, bound=221 > 121).

**When to stop:** If the proof requires Bertrand, Jacobsthal, or prime gaps,
stop. Use axioms or structural construction instead.

**Source:** `prove-apply1-is-prime.md`

### 10.2 Euclid's lemma wall

`Calc.mod(a * b, p) != 0` for prime `p` where `a,b < p` requires Euclid's
lemma. Z3 handles concrete values but times out on abstract variables.

**Three failed approaches:**
1. Direct induction on primes list — times out on `Calc.mod(h * tailPrim, p)`
2. Induction on `a` in `Calc.mod(a * b, p)` — `sum == p` case requires Euclid's lemma itself
3. Reduce modulo p first — still fails at final step

**Mitigation:** Avoid product-modulo proofs with symbolic variables. Use
addition-based reasoning (`modAdd`, `assertMultiplePreservesDivisible`).

**Source:** `primorial-not-divisible-by-new-prime.md`

### 10.3 Non-linear arithmetic is limited

Prefer addition-based approaches over `mod(a * b, p)`:
- `assertMultiplePreservesDivisible(a, b, p)` for `mod(a * b, p) == 0`
- `assertAddPreservesNotZeroMod(v, add, p)` for `mod(v + add, p) != 0`

## 11. Structural Invariants

### 11.1 Constructor `require` as escape hatch

When `@extern` blocks pipeline reasoning, add `require` to the case class
constructor. Makes the property structural — available at construction time
without inductive proof.

**Pattern (Path B from `sieve-properties-step5-coprime-to-modulus.md`):**
```scala
case class CycleSieveSequence(primes: SortedPrimeList) {
  require(SieveUtils.isCoprime(primes.head.value, PrimeUtils.primeValues(primes.list.tail.list)))
}
```

**Tradeoff:** Every construction site must satisfy the require.

### 11.2 Named constructor helpers

Before removing `@extern`, isolate each constructor requirement into a named
helper. One per verify cycle:
```
assertNextPrimesNonEmpty → assertNextHeadPositive → assertNextPrimesPositive →
assertNextHeadBiggerThanOne → assertNextPrimesBiggerThanOne →
assertNextTailProductEqualOrBiggerThanElements → assertNextHeadCoprimeToPrimes
```

**Source:** `next-constructor-requirement-assertions.md`

### 11.3 Restricted representations

A wrapper type (like `CompletePrimePrefix`) that enforces invariants at
construction makes proofs easier — invariants become structural.

**Source:** `complete-prime-prefix-sieve-cycle.md`

## 12. `@extern` Removal

### 12.1 Cascading VCs

Removing `@extern` reveals every unproven invariant. Each must be addressed
independently. Phase breakdown from `remove-extern-from-next.md`:
- **Phase 1 (Gap positivity) — worked:** Fixed `%` → `Calc.mod`,
  `assert(current > lastSurvivor)`, `assertCycleIntegralIncreasing`
- **Phase 2 (Head coprimality) — worked:** Structural invariants on V2
- **Phase 3 (NonEmpty) — BLOCKED:** Can't prove survivor in `head * gapCycle.size` steps
- **Phase 4 (Remove `@extern`) — BLOCKED by Phase 3**

### 12.2 Bridge `apply(k)` to concrete access

`seq.apply(1)` is opaque. Bridge: `seq.apply(1) == seq.primes.head + seq.gapCycle.memCycle(0)`.

### 12.3 Avoid expensive helpers in constructors

Don't call `nextGapCycleV2(seq)` inside every helper. Take trimmed parameters
instead.

## 13. Proof Strategies

### 13.1 Abstract foundation lemmas

Prove foundation lemmas in isolation before any data model depends on them.
From `sieve-foundation-cycle-integral-ones-and-filter-preserves-primes.md`:
1. `assertCycleIntegralOfOnes(init, pos)` — induction on `pos`
2. `assertCycleIntegralOfOnesStrictlyIncreasing` — uses Lemma 1
3. `assertPrimeNotDivisibleByDistinctPrime(q, p)` — case analysis
4. `assertFilterPreservesAllPrimes` — from Lemma 3
5. `assertFilteredContainsAllPrimes` — induction on list structure

**Distinct primes pattern:**
- q > p: `noDivisorInRange(q, 2, q)` implies `mod(q, p) != 0`
- q < p: `ModSmallDividend.modSmallDividend(q, p)` gives `mod(q, p) = q != 0`

### 13.2 Proof objects before data model changes

Before modifying a verified type, create a separate proof object. Split the
target lemma into smaller requirements, verify independently, then apply.

**Source:** `sieve-sequence-residue-representation-proof-object.md`

### 13.3 Head primality wiring

Class invariants provided preconditions without `require`:
- `seq.head > 1` from `Prime` type
- `checkAllPositive(seq.primes.tail)` from `SortedPrimeList`

**Source:** `sieve-properties-step4-assertHeadIsPrime.md`

### 13.4 Gap positivity pattern

1. Use `Calc.mod` — never `%`
2. `assert(current > lastSurvivor)` before gap computation
3. Leverage `assertCycleIntegralIncreasing`

**Source:** `remove-extern-from-next.md`

## 14. Article Writing

### 14.1 VC counts are brittle — omit from articles

Never embed repository-wide counts. Use: "described properties are verified".

**Source:** `article-review-comparison-2026-06-17.md`

### 14.2 Draft/failed properties go in learnings, not articles

Articles focus on what's verified. Unverified math goes in learnings docs.

**Source:** `article-evaluation-2026-06-15.md`

### 14.3 Articles don't cite tickets or learnings

Published output vs internal helpers. Use source code links instead.

**Source:** `article-review-comparison-2026-06-17.md`

### 14.4 Three-form presentation

Every property: English → LaTeX math → Scala `.holds` with source reference.

### 14.5 Framing integrity

Abstract/intro/conclusion must match content. Use text markers:
`[Verified]` `[Proven]` `[Open]` `[Failed]`. No emojis.

## 15. Empirical Verification

### 15.1 Runners complement SMT

When SMT can't prove it, write a standalone Scala runner.
- No Stainless dependencies
- Clear hypothesis with pass/fail criteria
- BigInt for all numerical types

**Source:** `empirical-g-local-crossover.md`

## 16. Path Choice Framework

### 16.1 Analyze alternatives before building

Map all possible paths. Evaluate each: what info does it need? Does the solver
have it? What's the verification cost?

**Example:** 5 paths analyzed in `sieve-properties-step5-coprime-to-modulus.md`;
only Path B (structural invariant) worked.

### 16.2 Avoid opaque return values

The solver can't connect "the first value satisfying property X" at call sites.

### 16.3 Avoid `forall` over `BigInt`

Induct on `k` with `decreases(k)` instead.

## 17. Project Workflow

### 17.1 One assertion per verify cycle

NEVER batch `assert(a && b && c)`. One per change.

### 17.2 Check `verify.log` before action

`grep "total:" verify.log`. Don't re-run on clean state.

### 17.3 Tests after verify

`just test` after every `just verify`.

### 17.4 Ticket before long action

If >2 tool calls expected, create a ticket. Update after each loop.

### 17.5 Search tickets for related work

Before starting, search `tickets/` for similar work. Extract lessons.

## 18. Cross-instance Lemma Calls [Open]

### 18.1 Cross-instance calls can time out even for simple lemmas

**Observation:** Calling a `.holds` lemma on a different instance of the same
class (e.g. `seq.assertApplyOneGtHead()` where `seq` is a second
`SpecSieveSequence`) can time out at 600s per VC even when the lemma itself
verifies instantly (25s) when called on `this`.

**Failed fixes (ticket `conditional-nextprime-gap-cycle-bridge.md`):**
1. Increasing per-VC timeout from 120s to 600s — no change for 2 of 3 unknowns
2. Returning stronger inequality (`h+1 ≤ a1` instead of `a1 > h`) — no change
3. Adding pure-arithmetic bridge lemma (`assertLeqFromLt`) — no change
4. Breaking Lemma 4 into smaller pieces (`assertApplyOneLeqValue`) — VC count
   unchanged, same timeouts persisted

**What's still untested:** Isolating each cross-instance call in its own small
wrapper lemma where it is the ONLY cross-instance call. The hypothesis is that
each cross-instance call doubles the VC size because the solver must unfold
`apply(k)` for the new instance. In a lemma with 3 cross-instance calls, each
assertion's VC includes ALL 3 unfoldings.

### 18.2 The solver can't derive `a > b ⇒ a ≥ b+1` in cross-instance context

**Observation:** `assert(head + BigInt(1) <= v1)` in Lemma 4 consistently
times out even though `seq.assertApplyOneGtHead()` (which returns this
expression directly) was called on the previous line. The solver can't make
the connection between the lemma's return value and the local variables
`head` (aliasing `seq.head.value`) and `v1` (aliasing `seq.apply(1)`) in a
large cross-instance VC.

**Root cause not confirmed.** Possible causes:
- VC includes all preceding assertions, making the formula too large
- Cross-instance `apply(k)` unfolding dominates the solver's search space
- The solver doesn't use cached lemma results across assertion boundaries in
  large VCs

## Index

| Lesson | Source ticket | Area |
|--------|--------------|------|
| 1.1 Private lemmas | `v0-residue-cycle-proof.md` | Propagation |
| 1.2 `.ensuring` postcondition | `v0-residue-cycle-proof.md` | Propagation |
| 1.3 Return equality directly | `v0-residue-cycle-proof.md` | Propagation |
| 1.4 `.holds` caching | `dead-code-cleanup-and-euclid-article.md` | Propagation |
| 2.1 IH propagation | `v0-residue-cycle-proof.md` | Induction |
| 3.1 `modZeroPlusC` | `v0-apply-modulus-loop.md` | Modulo |
| 3.2 `APlusMultipleTimesBSameMod` | `v0-residue-cycle-proof.md` | Modulo |
| 3.4 No `%` operator | `v0-apply-modulus-loop.md` | Modulo |
| 4.1 Prefix-product | `v0-apply-modulus-loop.md` | Product |
| 4.2 `primorialMatchesSieveProduct` | `v0-apply-modulus-loop.md` | Product |
| 5.2 Residues completeness | `v0-residue-cycle-proof.md` | Lists |
| 6.2 Private lemmas over external | `v0-residue-cycle-proof.md` | Timeouts |
| 6.4 3-attempt rule | `v0-apply-modulus-loop.md` | Timeouts |
| 7.2 `indexOfAccepted` period | `v0-residue-cycle-proof.md` | Periodicity |
| 7.3 Two-direction inequality | `v0-residue-cycle-proof.md` | Induction |
| 8.1 Run tests after verify | `v0-apply-modulus-loop.md` | Testing |
| 9.1 `.ensuring` breaks type inference | `v0-next-level-construction.md` | Pitfalls |
| 9.2 No `rm` | `v0-next-level-construction.md` | Pitfalls |
| 9.3 No destructive git | `v0-next-level-construction.md` | Pitfalls |
| 9.4 No core cycle modifications | `v0-apply-modulus-loop.md` | Pitfalls |
| 10.1 Deep number theory limits | `prove-apply1-is-prime.md` | SMT Limits |
| 10.2 Euclid's lemma wall | `primorial-not-divisible-by-new-prime.md` | SMT Limits |
| 11.1 Constructor `require` as invariant | `sieve-properties-step5-coprime-to-modulus.md` | Structural |
| 11.2 Named constructor helpers | `next-constructor-requirement-assertions.md` | Structural |
| 11.3 Restricted representations | `complete-prime-prefix-sieve-cycle.md` | Structural |
| 12.1 `@extern` cascading VCs | `remove-extern-from-next.md` | @extern |
| 12.2 Bridge `apply(k)` to cycles | `next-constructor-requirement-assertions.md` | @extern |
| 13.1 Abstract foundation lemmas | `sieve-foundation-cycle-integral-ones-and-filter-preserves-primes.md` | Proof Strategies |
| 13.2 Proof objects before data changes | `sieve-sequence-residue-representation-proof-object.md` | Proof Strategies |
| 13.3 Head primality wiring | `sieve-properties-step4-assertHeadIsPrime.md` | Proof Strategies |
| 13.4 Gap positivity pattern | `remove-extern-from-next.md` | Proof Strategies |
| 14.1 VC counts brittle in articles | `article-review-comparison-2026-06-17.md` | Articles |
| 14.2 Draft/failed in learnings | `article-evaluation-2026-06-15.md` | Articles |
| 14.3 No ticket/learning citations in articles | `article-review-comparison-2026-06-17.md` | Articles |
| 15.1 Empirical runners | `empirical-g-local-crossover.md` | Verification |
| 16.1 Path analysis before building | `sieve-properties-step5-coprime-to-modulus.md` | Process |
| 17.1 One assertion per cycle | AGENTS.md | Workflow |
| 17.4 Ticket before long action | AGENTS.md | Workflow |
| 17.5 Search tickets first | AGENTS.md | Workflow |
| 18.1 Cross-instance timeouts [Open] | `conditional-nextprime-gap-cycle-bridge.md` | Cross-instance |
| 18.2 Solver can't derive `a > b ⇒ a ≥ b+1` cross-instance [Open] | `conditional-nextprime-gap-cycle-bridge.md` | Cross-instance |
