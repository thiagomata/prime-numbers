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

This lemma proves `tailPrimorial == SieveUtils.product(filterValues)`. It should
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

### 5.3 Keep extracted predicates canonical

When extracting helper predicates into a utility object, do not leave
logically-equivalent local copies behind unless they are deliberate wrappers
that delegate to the canonical helper. Stainless treats
`OldObject.contains(x, list)` and `NewUtils.contains(x, list)` as different
functions even if their bodies are textually identical, so a lemma that proves a
fact about one surface may not satisfy a caller that consumes the other.

**Pattern that worked:** make old/public surfaces delegate to the extracted
utility, then keep postconditions stated through the wrapper only when callers
need backward compatibility.

```scala
def contains(current: BigInt, list: SortedPrimeList): Boolean =
  PrimeListUtils.contains(current, list)
```

Also preserve load-bearing postconditions when moving recursive helpers.
`searchNextPrimeUpTo` needed the full `noPrimesBetween(current, res.value)`
postcondition as its induction hypothesis; weakening it to a numeric bound made
later VCs time out even though the implementation looked unchanged.

**Affected:** Chapter 5 `PrimeListUtils` extraction. `PrimeProperties` proved
facts using `PrimeListUtils.contains`, while `AllPrimesSoFarList` still consumed
local duplicate predicates. Aligning `AllPrimesSoFarList.contains`,
`allPrimesSoFar`, `noPrimesBetween`, and
`primeAtOrBelowHeadIsContained` through `PrimeListUtils` removed the
`PrimeListUtils._` and `AllPrimesSoFarList._` unknowns.

**Chapter 6 audit note:** `SpecSieveSequence` has proofs that call the Chapter 5
prime-list wrappers (`AllPrimesSoFarList.contains`,
`primeAtOrBelowHeadIsContained`, `nextPrime`, and `noPrimesBetween*`) in the
`assertApplyOneEqualsNextPrime` chain. Those wrappers are safe only while they
delegate to the canonical `PrimeListUtils` predicates; if Chapter 6 develops
similar timeouts, first check for a split predicate surface before increasing
timeouts or adding heavier assertions.

### 5.4 Bridge related predicates explicitly

Sometimes two predicates are not duplicates, but one logically implies the
other through a structural relationship. Do not expect Stainless to infer that
relationship at a distant call site.

**Pattern that worked:** add a named bridge lemma at the owner of the
relationship, then call it before the expensive precondition.

```scala
def assertNextValueAcceptedByThis(k: BigInt): Boolean = {
  val nextSeq = next
  val value = nextSeq(k)
  // nextSeq filters by the old whole prime list; this stage filters by its tail.
  accepts(value)
}.holds
```

**Affected:** Chapter 6 `SpecDerivedSieveSequence.assertSurvivorGapEqualsSpecNextGap`
timed out proving that `spec.next(k + 1)` could be passed to
`spec.indexOfAccepted`. The value was accepted by `spec.next`, while
`indexOfAccepted` needed acceptance by `spec`. Adding
`SpecSieveSequence.assertNextValueAcceptedByThis` exposed the filter-tail
projection once, and the class-level check dropped from a 300s timeout to a
green `SpecDerivedSieveSequence._` run.

### 5.5 Assert list size before `.apply()` with external bound

When a lemma calls `list.apply(index)` where `index` is bounded by an external
parameter (e.g. `nextPeriod`) rather than by `list.size` directly, Stainless
cannot synthesize the size precondition even when `index < externalBound` is
required. Always precede such an `.apply` with an explicit size assertion:

```scala
assert(spec.next.assertGapListSize(0, nextPeriod))
// now safe: spec.next.gapList(0, nextPeriod).apply(index)
```

**Source:** `sieve-sequence-proof.md` — `assertNextGapAtMatchesSpecNext` timeout.

### 5.6 Verify builder order before induction

When proving `myBuilder == specBuilder` by induction, sanity-check the builder
produces the same order as the spec builder on paper first. A reversed builder
makes the goal unprovable, and the solver expresses this as a timeout rather
than a counterexample — which looks like solver weakness but is actually a
logic bug.

**Sliding-window induction** over `from` beats fixed-`from` induction over
`count` when the list builder recurses on `from + 1`. The period anchor and
other preconditions stay local; no re-derivation needed at recursive calls.

```scala
// Forward-order builder with sliding window:
(spec.next(from + 1) - spec.next(from)) :: nextGapList(from + 1, count - 1)
```

**Source:** `sieve-sequence-proof.md` — `assertNextGapListMatchesSpecNext` bug.

## 6. Timeout Resolution Strategies

### 6.0 Stop orphaned verification workers before reruns

If a Stainless run is interrupted or appears stale, run `just verify-stop`
before starting another verification command. It terminates orphaned Stainless,
Java verifier, SBT, `smt-z3`, and `z3` workers with `TERM` first, then uses
`KILL` only for matching verification processes that are still alive.

Avoid overlapping solver runs. They hide the real timeout profile and can make
otherwise-local Chapter 5/6 proof changes look much worse than they are.

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

### 6.4 Direct return from if/else eliminates thin-fork `.ensuring` timeouts

**Problem:** A thin fork function with a complex `.ensuring` block (containing `val` defs that re-compute `specGapCycle → CycleIntegral → survivorValues → nextSeq`) times out in its postcondition VC when the body uses `assert(subLemma(...)); ...; true`:

```scala
// TIMEOUT: VC combines all assert contexts + 50+ congruence terms simultaneously
if (cond) {
  assert(assertBase_LT(seq, period, nextPeriod, i))
  assert(nextSeq.apply(i) == survivors(i))
} else {
  assert(assertBase_GEQ(seq, period, nextPeriod, i))
  assert(nextSeq.apply(i) == survivors(i))
}
true
```

**Fix:** Make the if/else the DIRECT RETURN EXPRESSION — no `assert()` wrappers, no trailing `true`:

```scala
// WORKS: Stainless WP calculus generates per-path postcondition VCs
// each with ~20 terms, not a combined 50+ term VC
if (cond) {
  assertBase_LT(seq, period, nextPeriod, i)
} else {
  assertBase_GEQ(seq, period, nextPeriod, i)
}
```

**Why it works:** With the if/else as the return expression, Stainless's WP calculus generates INDEPENDENT postcondition VCs per branch. Z3 gets: `pre ∧ branch_cond ⊢ subLemma(args) ∧ ensuring_equality`. The sub-lemma's postcondition axiom supplies `nextSeq.apply(i) == survivors(i)` for the ACTUAL symbolic terms. The ensuring block's fresh `val` defs (copies of the body defs) are unified via 5-6 EUF congruence steps — tractable in seconds.

With `assert(...); true`, the VC is NOT split per branch. Z3 must work through 4 copies of each symbolic term simultaneously (body vars, ensuring vars, sub-lemma body vars, sub-lemma ensuring vars) → 60+ congruence steps → TIMEOUT.

**Validated:** `assertSurvivorMatchesNextSeqApply_Base` (51/51, 39s), `assertSurvivorMatchesNextSeqApply_Step` (similar), `assertSurvivorAtIndexMatchesNextSeqApply` (similar). Previously timed out at 109/110, 43/44, 52/53 with `assert+true` pattern.

**Prerequisite:** Sub-lemmas must have `.ensuring(res => { val gapCycle = ...; val baseCI = ...; val survivors = ...; val nextSeq = ...; res && nextSeq.apply(i) == survivors(i) })` with the SAME computation shape as the caller's ensuring. Without `.ensuring`, the axiom is missing.

**Source:** `tickets/active/chapter6-goal-driven-audit.md`, abandoned indexed bijection attempt (2026-07-18).

### 6.5 `verify-debug --functions=X` crashes for mutually-recursive X

**Problem:** `just verify-debug "X"` uses `--batched --debug=verification,full-vc,solver --functions=X --debug-objects=X`. When `X` is part of a mutual recursion group (X calls Y which calls X), Stainless's TypeChecker throws a fatal error:
```
FatalError: Call to function Y is not allowed here, because it is mutually recursive with the current function X
```

**Why:** `--batched --debug-objects=X` restricts the TypeChecker's visibility graph. It rejects calls from X to Y when Y is in X's SCC (strongly connected component of the call graph), treating it as an illegal cross-boundary call.

**Fix:** Verify the entire mutual recursion group together. Use `verify-debug "package.ClassName._"` to focus on all functions in the class, which includes the whole SCC. Alternatively run `just verify-ch N`.

**Pattern in ch60 abandoned indexed bijection (2026-07-18):** `assertSurvivorMatchesNextSeqApply_Step` calls `assertSurvivorAtIndexMatchesNextSeqApply` (IH), and `assertSurvivorAtIndexMatchesNextSeqApply` calls `assertSurvivorMatchesNextSeqApply_Step`. They are mutually recursive and BOTH need `decreases(nextPeriod - i)` for Stainless to accept the SCC. Without `decreases` on Step, any attempt to verify Step or the whole class crashes with this FatalError even when the class-level `._` focus is used.

**Source:** ch60 abandoned indexed bijection, 2026-07-18.

### 6.6 When timeout repeats 3 times, stop

After 3 failed attempts on the same VC, stop and ask for help. Do NOT try
variations. Document the error and the attempted fixes.

### 6.5 Constructor invariants kill cross-file unknowns

A single constructor `require` can eliminate unknowns spread across multiple
files by making a fact structurally available everywhere. Adding
`require(PrimeUtils.primorial(primes.list.tail.list) > BigInt(0))` to
`CycleSieveSequence` (i.e. `modulus > 0`) killed 5 unknowns in 4 different
functions across 3 files.

**Tradeoff:** Every construction site must satisfy the new require. Work on
small stages first (S_0, S_1) where the fact is trivially true.

**Source:** `fix-ch6-timeout-file-by-file.md`

### 6.6 Don't disable working lemmas due to timeout

Timeout on a lemma means the solver failed, not that the lemma is wrong.
Disabling it loses a verified fact. Instead: add `require` preconditions that
make the solver's job easier, or strengthen constructor invariants to make the
fact available structurally (6.5).

**Source:** `fix-ch6-timeout-file-by-file.md` — user corrected the attempt to
comment out 5 timeout lemmas.

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
Run `just test` after the chapter-by-chapter verification sequence succeeds.

### 8.2 Check verification logs

`just verify-ch N` writes to chapter-specific files under `logs/verify-ch-*.log`.
Check the `total:` summary in each chapter log. Timeouts appear as "unknown" in
the valid/invalid/unknown count.

`just verify` still writes to `logs/verify.log`, but the aggregate run is not
the preferred regression signal because it can time out on the combined VC set.

### 8.3 Prefer chapter-by-chapter regression for full-project validation

The all-at-once `just verify` command can time out on the combined project VC
set even when the codebase is healthy. For regression validation, run the
chapter-scoped sequence instead:

```bash
just verify-ch 1
just verify-ch 2
just verify-ch 3
just verify-ch 4
just verify-ch 5
just verify-ch 6
```

Each `just verify-ch N` run loads chapters up to `N` but auto-focuses Stainless
on `v1.chapterN._`, so dependencies are present without asking the solver to
reprove the whole repository in one batch. Treat a full `just verify` timeout
as an aggregate-batch limitation until the chapter logs say otherwise.

### 8.4 `just verify <name>` matches across ALL chapters, not just the target chapter

`just verify functionName` passes `--functions=functionName` to Stainless. Stainless
matches this against functions in ALL loaded source files. If two chapters define a function
with the same name, the wrong chapter's version may be verified from cache while the intended
chapter is skipped entirely.

**Symptoms:** output says "Generating VCs for N functions" where N is suspiciously small;
all results are `valid from cache`; file paths in the output point to the wrong chapter.

**Fix:** For chapter-specific verification, always use `just verify-ch N`. Never rely on
`just verify <name>` unless you confirm the paths in the log output match the intended chapter.

**Source:** `assertFirstSurvivorAtOrBeforeNextValue` targeted run, 2026-07-20. No longer
applicable after old chapter6 was removed and chapter60 became chapter6 (2026-07-20).

### 8.5 Do not run multiple verify instances in parallel

Each `just verify` call begins with `bash verify-stop.sh`, which kills any running
Stainless/Z3 processes. Running two `just verify` commands concurrently means each
will kill the other's solver, producing no useful output. Run one at a time and wait
for it to finish before starting the next.

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

### 14.4 Moment-in-time articles do not need future-state references

When reviewing an article, treat it as a self-contained moment in time. Do not
complain that its Future Work, conclusion, or scope note fails to reference
later articles, later repository state, or work completed after the article's
narrative point. Only flag future-work wording when it is internally
contradicted by the article itself.

The same rule cuts the other way: do not add future-facing framing to abstracts,
introductions, or conclusions. Avoid phrases like "used by later sieve proofs",
"needed downstream", or "future chapters will use this." The article should be
justified by the definitions, mathematical properties, and formal verification
it contains now. Future Work can discuss mathematical extensions, but should not
turn the article into repository sequencing.

**Source:** `cycle.md` PR review discussion, 2026-07-22.

### 14.5 Use cons for element-list structure, concat for list-list structure

In article math, use `h :: t` when the left side is a single element and the
right side is a list. Use `A \mathbin{\texttt{++}} B` only when both sides are
lists. This avoids type confusion such as `head(L) ++ tail(L)` or
`head(L) + init ++ acc(...)`, where the left side is not a list. Avoid
singleton-list construction such as `[x]`, `[e]`, or `[L_t]` when the expression
is really cons, suffix append, or insertion; prefer `x :: L_e`, `e :: suffix`,
or `A \mathbin{\texttt{++}} (e :: B)`. Display lists and set-builder/range
lists are still fine.

Good:
```math
\begin{aligned}
L &= \text{head}(L) :: \text{tail}(L) \\
\text{acc}(L, init) &=
  (\text{head}(L) + init) :: \text{acc}(\text{tail}(L), \text{head}(L) + init) \\
\text{slice}(L, f, t) &=
  \text{slice}(L, f, t - 1) \mathbin{\texttt{++}} (L_t :: L_e) \\
\text{product}(A \mathbin{\texttt{++}} (e :: B)) &=
  e \cdot \text{product}(A \mathbin{\texttt{++}} B)
\end{aligned}
```

Avoid:
```math
\begin{aligned}
L &= \text{head}(L) \mathbin{\texttt{++}} \text{tail}(L) \\
\text{sum}([x] \mathbin{\texttt{++}} L) &= x + \text{sum}(L) \\
\text{product}(A \mathbin{\texttt{++}} [e] \mathbin{\texttt{++}} B) &=
  e \cdot \text{product}(A \mathbin{\texttt{++}} B)
\end{aligned}
```

For Scala code snippets, keep real Scala syntax such as `List(x) ++ list` when
quoting source. The notation rule applies to mathematical exposition.

**Source:** `list-article-math-rendering-2026-07-22.md`.

### 14.6 Three-form presentation

Every property: English → LaTeX math → Stainless-backed Scala code with source
reference. `.holds` is common, but verified assertions, `ensuring`
postconditions, constructor invariants, and helper predicates used by verified
proofs also count when the source supports the claim. The thing to avoid is a
fake commented conclusion presented as proof.

### 14.7 Proof-code embedding

Use `articles/chapter4/cycle.md` as the preferred article-code pattern. The
main text should stay readable: English explanation, mathematical derivation,
and source reference. Small inline Scala blocks are fine when they show the
core idea with a good signal/noise ratio. Move longer selected proof excerpts
to an appendix; for routine companion lemmas, link to the source instead of
embedding the whole body inline.

Appendix excerpts still need source links. When an appendix includes Scala
code, add a nearby Markdown link to the repository file that owns the
maintained proof, rather than leaving the excerpt as an orphaned copy or a
plain-text path.

Main-body source excerpts need nearby source links too, preferably before the
block. Also verify appendix item references after moving code around; stale
"Appendix A.n" pointers are article-integrity bugs, even when the proof itself
is correct.

### 14.8 Framing integrity

Abstract/intro/conclusion must match content. Use text markers:
`[Verified]` `[Proven]` `[Open]` `[Failed]`. No emojis.

### 14.9 Preliminaries instead of ASCII dependency maps

Use the `cycle.md` pattern for prerequisites: a plain `## 2. Preliminaries`
section with prose and links to foundational articles. Avoid "Prerequisite
Structure" or "Dependency Map" ASCII arrow diagrams; they read like scaffolding
instead of publication text.

### 14.10 Keep coding strategy out of articles

Published articles should focus on the mathematical result, definitions,
verified properties, and source-backed proof code. Solver tactics such as
`.holds` cache behavior, postcondition-enrichment strategy, timeout workarounds,
and verification workflow belong in `LEARNINGS.md` or tickets, not as article
sections.

### 14.11 Avoid tutorial voice for verification mechanics

Do not write article prose like "the `.holds` annotation tells Stainless..." or
explain basic verifier mechanics as if teaching the tool. Prefer proof-oriented
language: state what the lemma establishes, which mathematical facts it
combines, and where the source-backed proof lives.

### 14.12 Use math spans for inline mathematics

Inline mathematical statements belong in `$...$`, not code backticks. For
example, write $d \cdot d \le d \cdot q = n$, $d^2 \le n$, and
$\text{mod}(n,d)=0$ as math. Reserve backticks for code identifiers, source
expressions, and literal Scala syntax. Do not use unsupported LaTeX macros such
as `\operatorname`; use `\text{...}` or established infix notation instead.

### 14.13 Use `:=` only for definitions

Use `:=` in article math when introducing a definition, notation convention, or
local alias. Use `=` for ordinary mathematical equalities, theorem statements,
and proof derivation steps. For example,
$S := \text{DivMod}(a,b,0,a).\text{solve}$ defines $S$, while $a = bq + r$
states the invariant being proved or used.

### 14.14 Theorem articles are math-first, not source walkthroughs

The main body of a theorem article should carry the mathematical argument and
then cite where it is verified in source. Avoid interleaving long Scala blocks
throughout the proof narrative. Keep code excerpts in an appendix only when
they add high-signal context; otherwise, a source link is enough.

### 14.15 Keep the article centered on its theorem

Do not present every nearby helper as a peer of the theorem. The main theorem
should be the spine of the article; adjacent corollaries and utility lemmas
belong in a clearly secondary supporting section, with prose framed as
mathematical context rather than repository or downstream implementation needs.

### 14.16 Explain helper lemmas as properties, not inventory bullets

When an article depends on helper lemmas, do not list them as code names plus a
one-line "used to..." note. Give each important helper a property name, explain
the mathematical statement, show the derivation in a math block, and then cite
the source proof. This keeps the article at the same level as the other proof
articles.

### 14.17 Properties are first-class; methods are verification references

Article sections should be organized around mathematical properties, not source
method names. The source method is evidence that the property is verified; it
should appear in the verification reference, not drive the section's narrative.

### 14.18 Formal verification should stay visible

Avoid tutorial prose about `.holds`, cache behavior, or solver mechanics in
articles, but do not erase formal verification from the result. When a theorem
or property has been formally verified, the abstract, introduction, conclusion,
and source references should say so clearly. Formal verification is often a
harder achievement than the paper proof alone; be proud of it while keeping the
article focused on the mathematics.

### 14.19 Conclusions and future work should be prose

Do not end articles with simple bullet lists of completed tasks or possible
next projects. A conclusion should synthesize what the proof established, how
the main argument works, what was verified, and what the result's scope is. It
must also bring back the core proved properties and proof structure in
mathematical form: include a compact math recap of the main theorem,
definitions, and supporting properties that the article established, as in
`integral.md` and `cycle.md`. Future work should explain the next mathematical
directions in prose and state how they extend the article's result.

## 15. Structural Index Lemmas (ch60, abandoned indexed bijection)

### 15.1 Body `val`s are not in scope in `.ensuring` blocks

In Stainless, `.ensuring(res => ...)` is a closure that only captures function
PARAMETERS — not local `val`s defined in the body. Writing:

```scala
val survivors = computeSurvivors(...)
survivors(index) <= baseCI(end)
}.ensuring(res => res && survivors(index) <= baseCI(end))
// ERROR: 'survivors' is not found in the ensuring scope
```

**Fix:** Recompute inside the ensuring block using the same function parameters:

```scala
}.ensuring(res => {
  val gapCycle2  = SpecSieveSeqPeriodProperties.specGapCycle(seq, period)
  val baseCI2    = CycleIntegral(seq.head.value, gapCycle2.memCycle)
  val survivors2 = CycleIntegralFilterProperties.survivorValues(baseCI2, seq.head.value, startPos, count)
  res == (survivors2(index) <= baseCI2(startPos + count - BigInt(1)))
})
```

Z3 proves `survivors == survivors2` via 3-step EUF (same function, same args).
This is the SAME-SHAPE recomputation: 3 congruence steps, NOT the 4-chain
EUF problem from section 6.4. The key distinction: here BOTH the body and
ensuring compute the same 3 val-chain from the same parameters → Z3 unifies
them trivially. The original EUF timeout (section 6.4) happened when the
ensuring recomputed the chain INDEPENDENTLY of the body's locals, with no
structural helper to align them.

### 15.2 Structural index lemmas for `survivorValues`

Z3 cannot automatically derive how `survivorValues(ci, fv, sp, count)(k)`
relates to `survivorValues(ci, fv, sp+1, count-1)(k')` because:
- `survivorValues` is a recursive function returning an OPAQUE list term
- Z3 needs to case-split on the ADT constructor + unfold `apply` — 2 quantifier
  instantiation steps that compose poorly under the 300s timeout
- When the PRECONDITION check for a recursive call also requires this structural
  fact (e.g., `index-1 < survivorsTail.size`), the timeout is even more likely

**Solution:** Add explicit STRUCTURAL LEMMAS to `CycleIntegralFilterProperties`:

```scala
// When Calc.mod(ci(sp), fv) != 0:
def assertSurvivorApplyZeroWhenNonMultiple(ci, fv, sp, count):
  // survivors(0) == ci(sp)   [first element IS ci at startPos]

def assertSurvivorApplyKPlusOneWhenNonMultiple(ci, fv, sp, count, k):
  // survivors(k+1) == survivorsTail(k)   [shift-by-one when head included]

def assertSurvivorSizeNonMultiple(ci, fv, sp, count):
  // survivors.size == 1 + survivorsTail.size   [head increases size by 1]

// When Calc.mod(ci(sp), fv) == 0:
def assertSurvivorApplyKWhenMultiple(ci, fv, sp, count, k):
  // survivors(k) == survivorsTail(k)   [identity when head skipped]

def assertSurvivorSizeMultiple(ci, fv, sp, count):
  // survivors.size == survivorsTail.size   [skip preserves size]
```

Each lemma is TRIVIALLY PROVED (one unfolding of `survivorValues` definition).
Use them as explicit bridge assertions BEFORE the goal assertion:

```scala
// Non-multiple, index > 0 case in assertSurvivorLEQEndCI:
assert(CycleIntegralFilterProperties.assertSurvivorSizeNonMultiple(baseCI, head, sp, count))
assert(survivors.size == BigInt(1) + survivorsTail.size)
assert(index - BigInt(1) < survivorsTail.size)            // now provable
assert(assertSurvivorLEQEndCI(seq, period, sp+1, c-1, index-1))   // precondition satisfied
assert(survivorsTail(index-1) <= baseCI(sp+c-1))          // from .ensuring
assert(CycleIntegralFilterProperties.assertSurvivorApplyKPlusOneWhenNonMultiple(baseCI, head, sp, count, index-1))
assert(survivors(index) == survivorsTail(index-1))         // bridge
// Now Z3 derives survivors(index) <= baseCI(sp+c-1) trivially
```

**Why bridge assertions work:** After adding these, the goal VC context has only
2-3 simple equalities and one inequality — all immediate Z3 arithmetic steps.

### 15.3 Lexicographic `decreases` for mutual recursion

When two functions call each other (mutual recursion), `decreases(k)` on BOTH
causes the termination VC to check `k < k` (false!):

- `topLevel` calls `step` at SAME `k` → `decreases(n-i)` → must check `n-i < n-i` → UNKNOWN

**Fix:** Use LEXICOGRAPHIC measure `decreases(k, rank)` where rank differs:
- `step`: `decreases(nextPeriod - i, BigInt(0))` (lower rank)
- `topLevel`: `decreases(nextPeriod - i, BigInt(1))` (higher rank)

Now:
- `topLevel(i) → step(i)`: `(n-i, 1) → (n-i, 0)` → lex decrease ✓
- `step(i) → topLevel(i+1)`: `(n-i, 0) → (n-i-1, 1)` → lex decrease ✓

**Source:** ch60 abandoned indexed bijection, 2026-07-19.

### 15.4 `.ensuring(res => res == expression)` gives callers direct semantic access

When a recursive function has a complex body (with if-else and asserts) and
returns a BOOLEAN expression, callers can't easily extract the semantic fact
from `f(args) == true` without unfolding the body.

**Fix:** Add `.ensuring(res => res == theReturnExpression)` with inline recompute:

```scala
survivors(index) <= baseCI(startPos + count - BigInt(1))
}.ensuring(res => {
  val gapCycle2  = ...   // same computation as body
  val survivors2 = ...
  res == (survivors2(index) <= baseCI2(startPos + count - BigInt(1)))
})
```

Callers of `assertSurvivorLEQEndCI(seq, period, sp+1, c-1, index-1)` then get:
`true = (survivorsTail(index-1) <= baseCI(sp+c-1))` → direct semantic fact.

This is CRUCIAL for recursive calls where the IH must be usable in the BODY:
without `.ensuring`, the caller must unfold the callee body to get the semantic
fact — which requires Z3 to process the if-else branches, failing at 300s.

**Source:** ch60 `assertSurvivorLEQEndCI`, `assertSurvivorStrictlyIncreases`, 2026-07-19.

### 15.5 Richer postconditions cause regressions via cache invalidation

**Problem:** Adding `.ensuring(res => res == expr)` to an existing function `f`
that previously had `.holds` causes ALL callers to have their caches invalidated
AND makes their SMT formulas harder: the axiom `f(args) == expr` is added to
the call-site formula, increasing complexity. Borderline VCs that previously
passed within 300s may now timeout.

**Root cause:** With just `.holds`, the call-site VC `assert(f(k, v))` is:
"prove f(k, v) == true" — Z3 checks preconditions and the body logic (fast).
With the richer `.ensuring(res => res == (apply(k+1) <= v))`, the axiom
`f(k, v) == (apply(k+1) <= v)` is injected. Now Z3 must prove
`(apply(k+1) <= v) == true`, i.e., unfold the sequence — potentially hard.

**Fix:** Use a SEPARATE new function with the richer postcondition, called ONLY
where needed. Keep the original function with `.holds`:

```scala
// Original — keep as .holds (no change)
def nextDoesNotPassAcceptedValue(k: BigInt, v: BigInt): Boolean = {
  ...
}.holds   // callers unaffected, cache stays valid

// NEW: explicitly proves the upper bound
def nextApplyUpperBound(k: BigInt, v: BigInt): Boolean = {
  require(...)
  val next = apply(k + BigInt(1))
  if (next > v) { assert(...); assert(false) }  // contradiction branch
  apply(k + BigInt(1)) <= v
}.ensuring(res => res && apply(k + BigInt(1)) <= v)
```

Callers of the indexed bijection attempt use `nextApplyUpperBound` (gets the fact directly), while
existing callers keep using `nextDoesNotPassAcceptedValue` (no regression).

**Key insight:** Cache entries for callers of the ORIGINAL function remain valid
after the revert. Adding a NEW function doesn't invalidate any existing cache.
Only functions that CALL `nextApplyUpperBound` need new VCs.

**Source:** ch60 abandoned indexed bijection (2026-07-19). Three existing callers in SpecSieveSeqHeadIsPrime.scala:91 and SpecSieveSeqNextProperties.scala:117,121 timed out after the richer postcondition was added.

## 16. Empirical Verification

### 16.1 Runners complement SMT

When SMT can't prove it, write a standalone Scala runner.
- No Stainless dependencies
- Clear hypothesis with pass/fail criteria
- BigInt for all numerical types

**Source:** `empirical-g-local-crossover.md`

## 17. Path Choice Framework

### 17.1 Analyze alternatives before building

Map all possible paths. Evaluate each: what info does it need? Does the solver
have it? What's the verification cost?

**Example:** 5 paths analyzed in `sieve-properties-step5-coprime-to-modulus.md`;
only Path B (structural invariant) worked.

### 17.2 Avoid opaque return values

The solver can't connect "the first value satisfying property X" at call sites.

### 17.3 Avoid `forall` over `BigInt`

Induct on `k` with `decreases(k)` instead.

## 18. Project Workflow

### 18.1 One assertion per verify cycle

NEVER batch `assert(a && b && c)`. One per change.

### 18.2 Check `logs/verify.log` before action

`grep "total:" logs/verify.log`. Don't re-run on clean state.

### 18.3 Tests after verify

`just test` after every `just verify`.

### 18.4 Ticket before long action

If >2 tool calls expected, create a ticket. Update after each loop.

### 18.5 Search tickets for related work

Before starting, search `tickets/` for similar work. Extract lessons.

## 19. Cross-instance Lemma Calls [Open]

### 19.1 Cross-instance calls can time out even for simple lemmas

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

### 19.2 The solver can't derive `a > b ⇒ a ≥ b+1` in cross-instance context

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

### 19.3 Local `val` aliases block the solver from using cached lemma results [Open — workaround: directed equality lemmas]

**Problem:** `val nextSeq = spec.next` creates an opaque binding. A `.holds` lemma
returning `spec.next.accepts(v)` caches its result, but the solver cannot connect
it to `nextSeq.accepts(v)` — the assertion times out. `def` does not inline in
Stainless and has the same problem.

**Workaround (verified):** Prove acceptance equality through a directed lemma
that unfolds structural equalities explicitly. The solver handles positive
`require(seq1.accepts(v))` preconditions better than bare `==`:

```scala
def assertAcceptsEqualWhenTrue(seq1, seq2, v): Boolean = {
  require(seq1 == seq2)
  require(v >= seq1.head.value)
  require(seq1.passesFilter(v))
  require(seq1.accepts(v))
  assert(seq1.head == seq2.head)
  assert(v >= seq2.head.value)
  assert(seq1.primes == seq2.primes)
  seq1.accepts(v) == seq2.accepts(v)
}.holds
```

Key ingredients: (a) explicit `require(v >= seq1.head.value)` to avoid inferring
the lower bound through equality, (b) `require(seq1.passesFilter(v))` to access
the disjunctive filter structure, (c) explicit `assert(seq1.head == seq2.head)` etc.
to surface component equalities from structural equality.

**Prior failures:** `val` version timed out (9 VCs, 8/9). `def` version timed out
(same). Bare `seq1.accepts(v) == seq2.accepts(v)` without directed requires timed out.

### 19.4 Put reusable recursive producer facts in `.ensuring`

**Observation:** `SortedList.fromUnsorted(list)` guarantees
`SortedList.isAscending(sorted.list)`, but asking Stainless to rediscover that
inside a larger compositor lemma can produce a 300s timeout. In Phase E of
`independent-next-cycle.md`, `assertNextGapsAllPositiveGivenSortedBounds`
timed out twice when the lemma body or a downstream helper precondition had to
prove `SortedList.isAscending(nextSorted(seq).list)` from the `SortedList`
wrapper.

**Debug evidence:** `just verify-debug assertNextGapsAllPositiveGivenSortedBounds`
showed repeated matcher instantiation for `isAscending(nextSorted(seq).list)`,
followed by unrolling through `nextSorted(seq)`,
`SortedList.fromUnsorted(nextFiltered(seq))`, `nextFiltered(seq)`, recursive
`isAscending` tails, and unrelated prime-tail invariants. This is the signature
that Stainless is not shortcutting to the already verified constructor/helper
fact at the compositor site; it is reopening the producer pipeline. The debug
log stopped before a final summary, so use the focused non-debug run as the
validation result and the debug log only as mechanism evidence.

**Better fix (verified):** Put the reusable recursive facts directly on the
producer functions:

- `SortedList.insertSorted(x,list)` now ensures
  `isAscending(list) => isAscending(result)`.
- `SortedList.sortFiltered(list)` now ensures `isAscending(result)`.

After those postconditions were attached to the recursive producers,
`assertNextGapsAllPositiveGivenSortedBounds` no longer needed
`require(SortedList.isAscending(nextSorted(seq).list))`; the focused run
verified `24/24`. `assertNextRotatedGapsAllPositiveGivenSortedBounds` also no
longer needed that sortedness precondition and verified `36/36`.

**Proof shape (verified):** Keep low-level facts proved independently and make
the compositor lemma's role explicit. For the next-gap positivity bridge:

- `assertPairwiseGapsAllPositive` proves adjacent gap positivity.
- `assertWrapGapPositive` proves the final wrap gap is positive.
- `assertCalculateGapsAllPositive` composes those two.
- `assertNextGapsAllPositiveGivenSortedBounds` consumes sortedness from
  `sortFiltered`'s postcondition, requires only the remaining sorted-output
  range/head facts (`nonEmpty`, upper bound, nonnegative head), and verifies
  quickly.
- `assertNextRotatedGapsAllPositiveGivenSortedBounds` adds only rotation
  preservation on top.

**Lesson:** When a fact comes from a recursive producer and will be used by
large downstream VCs, prefer attaching it to the producer with `.ensuring`.
If the fact is only proved by a separate `.holds` lemma, Stainless may still
try to reopen the producer at the call site unless the exact lemma is called in
a shape the solver recognizes.

**Source:** `tickets/active/canonical-next-strategy.md`.
`assertAcceptsEqualWhenTrue` / `assertAcceptsEqualWhenFalse` verified in
`CanonicalCycleSieve.scala` at 9299 valid.

### 19.5 Return explicit branch invariants from recursive-search wrappers

**Observation:** When a public wrapper exposes a fact proved by a private
recursive search, Stainless may time out at the final postcondition even after
all internal recursive lemma calls verify. The solver tries to rediscover that
the wrapper result is the same first-survivor/search result used by the private
lemma, then reopens the branch structure.

**Failure shape:** `SpecSieveSequence.assertSkippedBeforeNextAcceptedOldIndexIsMultiple`
initially proved the needed recursive fact inside the branch that called
`assertSkippedIndexBeforeFirstIsMultiple`, but returned the final expression
after the branch:

```scala
if (skippedCase) {
  assert(assertSkippedIndexBeforeFirstIsMultiple(k, idx, p, bound))
}

Calc.mod(apply(idx), p) == BigInt(0)
```

The focused run verified `51/52` VCs but timed out for 300s on the final
postcondition. The recursive lemma call itself was valid; the timeout was the
solver failing to cheaply reuse its result after crossing the wrapper/branch
boundary.

**Fix (verified):** Return the branch invariant itself as a local value:

```scala
val skippedIsMultiple =
  if (immediateSuccessorSurvives) {
    false
  } else {
    assert(assertSkippedIndexBeforeFirstIsMultiple(k, idx, p, bound))
    assert(Calc.mod(apply(idx), p) == BigInt(0))
    Calc.mod(apply(idx), p) == BigInt(0)
  }

skippedIsMultiple
```

This makes the recursive-call result part of the expression Stainless is
verifying, rather than a fact it must recover later. The same focused proof then
verified `56/56`, and the public wrapper `nextAcceptedOldIndex` verified
`27/27`.

**Lesson:** For recursive-search wrappers, carry the exact recursive invariant
through the branch result or an `.ensuring` postcondition. Do not leave the
important fact as an internal assertion followed by a distant final expression,
especially when the final expression depends on equality between a public
wrapper result and a private recursive finder.

**Source:** `tickets/active/independent-next-cycle.md`.
Verified in `SpecSieveSequence.nextAcceptedOldIndex` and
`SpecSieveSequence.assertSkippedBeforeNextAcceptedOldIndexIsMultiple`.

### 19.6 Next-stage head is not the next-stage front filter

**Observation:** In `SpecSieveSequence` next-stage proofs, two similarly named
facts are easy to confuse:

- `nextSeq.head.value` is the new sequence head, the next emitted prime.
- `nextSeq.filterValues.head` is the front filter used by that new sequence,
  which is the previous sequence head.

These are NOT equal in general, so the OLD contract shape is unsound as a
precondition even though it happened to verify on its own:

```scala
require(nextSeq.head.value == head.value)   // OLD shape — weaker (head != front filter)
```

The intended NEW shape is stronger and correct:

```scala
require(nextSeq.filterValues.head == head.value)
require(apply(k) >= nextSeq.head.value) // when calling nextSeq.accepts(apply(k))
```

**Status (updated 2026-07-03 recovery):** The migration from OLD to NEW was
attempted in commits `cb49ccf2`/`d97bffcb` and **broke HEAD red**. The previous
"validated" numbers below came from that broken state and have been retracted.
The migration was left half-finished: the NEW-shape callees were committed but
their A-side callers and B-side dependent lemmas were not, so callers could not
discharge the stronger precondition (timeout at `assertMergedGapPrefixAllPositive`).
Recovery reverted both files to the green OLD-shape baseline (`5145c1e5`,
committed `bd444a35`) and re-activated only the migration-independent leaf lemma
(`assertHeadPlusFilterModulusNotFrontMultiple`, commit `49c79b58`).

**The mathematics here is correct, but the migration is NOT done.** To redo it
safely, see **18.8** below — migrate callee + ALL callers + dependent lemmas in
one green-to-green change. Do NOT repeat the partial migration.

**Reusable leaf fact (verified, migration-independent):** Expose the period
endpoint non-multiple fact once, regardless of contract shape:

```scala
assertHeadPlusFilterModulusNotFrontMultiple()
```

This proves `mod(spec.head.value + spec.tailPrimorial, spec.next.filterValues.head) != 0`
without depending on the head-vs-front-filter contract debate. It is currently
the ONLY piece of the next-stage-filter work that is active and green.

**Source:** `tickets/active/independent-next-cycle.md` (Recovery Log section).

### 19.7 Recursive list lifts need explicit coverage predicates

**Observation:** A pointwise survivor equality is not enough for a recursive
list proof unless each recursive call can prove its own index coverage. In the
next-cycle bridge, `count > offset` was too weak because `count` measures raw
cycle-integral scan positions, while `offset` measures retained survivors.

**Fix (verified):** Create a recursive coverage predicate with the same shape
as the list proof:

```scala
initialSurvivorGapListCovers(scanCount, from, gapCount)
```

It records that every adjacent pair required by a survivor-gap prefix is
available. With that invariant, the proof can use same-shape recursion:

- `initialSurvivorGapList(from,gapCount,scanCount)` builds survivor gaps in
  forward order.
- `assertInitialSurvivorGapListMatchesNextGapList` proves equality with the
  canonical adjacent-difference list.
- `assertInitialSurvivorGapListMatchesSpecNextGapList` composes that with the
  existing `nextGapList == spec.next.gapList` bridge.

### 19.8 A precondition migration must move callee + ALL callers + dependents together

**Observation:** Strengthening a `require` (contract migration) is the most
dangerous kind of edit in this codebase, because it is *backwards-incompatible*:
every caller that previously discharged the old (weaker) precondition must now
discharge the new (stronger) one. The 2026-07-03 red HEAD was caused by a
partial migration of `nextAcceptedOldIndex` and 4 siblings in
`SpecSieveSequence` to a stronger shape, while their callers were left on the
old shape. Stainless then timed out trying to prove the callers could meet a
precondition they were no longer given the facts for.

**The rule — migrate as one atomic, green-to-green change:**

1. **List every site** before touching code: the callee(s) being strengthened,
   every direct caller, and every lemma in *other files* whose `require`/proof
   was written against the new shape. A `grep` for the callee name across the
   whole `src/main/scala/` is mandatory — the dependency can cross files (it
   crossed from `SpecSieveSequence` into `SpecDerivedSieveSequence` here).
2. **Migrate callee + callers together**, in one working-tree state, NOT one
   commit at a time. A mid-migration commit is red by construction: the callee
   is strong, the callers are weak, the precondition cannot be discharged.
3. **`just verify` the whole chapter** (not just the touched function) before
   committing. Focused `--functions=` runs hide cross-file breakage.
4. **If it goes red, do NOT commit and continue.** Revert to green and replan.
   Committing a red state and "finishing later" is how HEAD stayed red for
   multiple commits.

**Smell test for a partial migration:** if your working tree strengthens a
`require` in function F but you have NOT edited every `grep` hit for `F(`,
you are mid-migration and almost certainly red. Stop.

**Recovery pattern that worked (when a partial migration was already committed
across two commits + working tree):** since the offending commits touched only
code-and-its-dependents, restoring *both* files to the last green commit
(`git restore --source=<green-sha> --worktree <file>`) was cleaner than
commenting out individual functions. `git restore` is permitted (only
`checkout`/`revert`/`push --force`/`rm` are denied). Tag the broken HEAD first
(`git tag <name> HEAD`) so nothing is lost.

**Anti-pattern that failed: the "surgical callee-only revert."** Reverting only
the callee back to the weak shape cleared *its* timeout but surfaced a *new*
timeout in a dependent lemma in the other file that had been written against
the strong shape. When two files are touched by the same commit, assume they
are coupled.

**Source:** `tickets/active/independent-next-cycle.md` (Recovery Log + Correct
Track sections).

**Validation:** Focused runs verified
`initialSurvivorGapListCovers` (`9/9`),
`initialSurvivorGapList` (`18/18`),
`assertInitialSurvivorGapListMatchesNextGapList` (`46/46`), and
`assertInitialSurvivorGapListMatchesSpecNextGapList` (`24/24`).

**Source:** `tickets/active/independent-next-cycle.md`.

## 20. Lemma Composition [Verified]

### 20.1 Reuse the expensive construction, not the `.holds`

Two independently-verified `.holds` lemmas should compose cleanly. When they don't,
the culprit is almost always **duplicate construction of an expensive object** inside
their bodies — not a logical gap or a "wall."

In chapter 6, `assertCanonicalGapsEqSpecNextGapList` and `assertCycleNextEqSpecNext`
both constructed `SpecDerivedSieveSequence(spec.next, nextPeriod)` internally.
Individually verified at 48s and 45s. Composed in a third lemma, they timed out
at 313s with 1 unknown VC.

The fix: merge them into ONE lemma (`assertCanonicalCycleNextMatchSpecNext`, 36/36,
62s) that constructs the expensive object once and does both proof steps in a
single body. Both composition lemmas now call this merged lemma as a cached call
(11s each, from cache).

**Pattern:** When two lemmas share an expensive construction, extract the
construction into the outermost proof body and pass the result to both. Don't
construct it inside each `.holds` separately — the `.holds` boundary doesn't
cache the construction across the composition boundary.

**Source:** `tickets/active/lean-ch6-proof-spine.md`, `SpecDerivedBySurvivors.scala`.

## 21. Cross-Chapter Dependency Management

### 21.1 Avoid circular imports between chapters

If chapter 5 imports from chapter 6 and chapter 6 imports from chapter 5, the
solver must verify ALL chapters in one batch, generating too many VCs.

**Fix:** Extract shared utilities into the lower-numbered chapter and update
imports so the dependency flows one direction only. Applied to `SieveUtils` in
ch6 → `CoprimeUtils` in ch5.

**Source:** `verify-timeout-root-cause.md` — root cause #1.

### 21.2 macOS DYLD_LIBRARY_PATH stripping

macOS strips `DYLD_LIBRARY_PATH` from subprocesses, so the Z3 dynamic library
cannot be found by Java JNI even when the environment variable is set. Fix:
use `install_name_tool -change libz3.dylib <absolute-path>` to embed the
absolute path in `libz3java.dylib`.

**Source:** `verify-timeout-root-cause.md` — root cause #2.

## Index

| Lesson | Source ticket | Area |
|--------|--------------|------|
| 18.1 Cross-instance timeouts [Open] | `conditional-nextprime-gap-cycle-bridge.md` | Cross-instance |
| 18.2 Solver can't derive `a > b ⇒ a ≥ b+1` cross-instance [Open] | `conditional-nextprime-gap-cycle-bridge.md` | Cross-instance |
| 18.3 Local `val` aliases block cached lemma results — workaround: directed equality lemmas | `canonical-next-strategy.md` | Cross-instance |
| 18.4 Recursive producer facts belong in `.ensuring` | `canonical-next-strategy.md` | Recursive producers |
| 18.5 Return explicit branch invariants from recursive-search wrappers | `independent-next-cycle.md` | Recursive search |
| 18.6 Next-stage head is not the next-stage front filter | `independent-next-cycle.md` | Next-stage filters |
| 18.7 Recursive list lifts need explicit coverage predicates | `independent-next-cycle.md` | Recursive list proofs |
| 18.8 Precondition migration must move callee + ALL callers + dependents together | `independent-next-cycle.md` | Contract migration / workflow |
| 5.5 Assert list size before `.apply()` with external bound | `sieve-sequence-proof.md` | List functions |
| 5.6 Verify builder order before induction | `sieve-sequence-proof.md` | List functions |
| 6.5 Constructor invariants kill cross-file unknowns | `fix-ch6-timeout-file-by-file.md` | Timeout resolution |
| 6.6 Don't disable working lemmas due to timeout | `fix-ch6-timeout-file-by-file.md` | Timeout resolution |
| 19.1 Reuse the expensive construction, not the `.holds` | `lean-ch6-proof-spine.md` | Lemma composition |
| 20.1 Avoid circular imports between chapters | `verify-timeout-root-cause.md` | Dependency management |
| 20.2 macOS DYLD_LIBRARY_PATH stripping | `verify-timeout-root-cause.md` | Tooling |
| 21.1 Indexed bijection via mutual induction always times out — use Step 9 bridge instead | See below | Goal 3 bridge |
| 21.2 `assert(false)` branch causes Stainless to combine all VCs — use `if` guard instead | See below | VC structure |
| 21.3 `res == expr` ensuring clause forces call sites to re-prove `expr` — use `.holds` or `res && expr` | See below | Ensuring clauses |
| 21.4 `mergedGapPrefix` walk must start at k=1, not k=0, for seq.next | See below | Bridge / seq.next |
| 21.5 `nextSeq.head.value == seq.head.value` is impossible for seq.next — use `<=` | See below | Preconditions / seq.next |
| 21.6 Make predicate functions total to eliminate precondition VCs at call sites | See below | Predicate design |
| 21.7 `indexOfAccepted(z)` must be called AFTER `accepts(z)` is established | See below | Call ordering |
| 21.8 Strict-monotonicity bridge for propagating lower bounds through index gaps | See below | Bridge patterns |
| 8.4 `just verify <name>` matches across ALL chapters — use `verify-ch N` for chapter-specific work | See above | Workflow |
| 8.5 Do not run multiple verify instances in parallel | See above | Workflow |

## 22. Chapter 60 Goal 3 — bridge patterns and the abandoned indexed bijection

### 22.1 Indexed bijection via mutual induction always times out — DELETE the code

Every session gets drawn back to trying `survivors(i) == nextSeq.apply(i)` by mutual induction
(the abandoned indexed bijection approach).
It always fails: the postcondition VC for the inductive step times out because Z3 cannot unify
the `specGapCycle → CycleIntegral → survivorValues` chain for both sides independently in 300s.

**Rule:** Do NOT write any `assertSurvivorMatchesNextSeqApply*` or `assertEqualityViaContradiction`
or `assertEqualityFromBounds` functions. They will time out.

**The correct approach (Step 9):** Bridge via `mergedGapPrefix` (chapter 6's strategy):
```
gapsFromValues(survivors) == mergedGapPrefix(seq, nextSeq, 1, nextPeriod, period)
                          == nextSeq.gapList(0, nextPeriod)
```
This avoids proving indexed value equality entirely.

**Danger signal:** If you see functions with names containing "SurvivorMatches", "EqualityVia",
"SurvivorAtIndex" — DELETE them. They are indexed bijection mutual induction in disguise.

### 22.2 `assert(false)` branch causes combined VC

When a branch ends with `assert(false)` (to mark it unreachable), Stainless creates ONE combined
VC for the entire function instead of separate per-assert VCs. This means a single complex VC
that always times out.

**Fix:** Use an explicit `if` guard:
```scala
// BAD:
val result = someComputation
assert(result <= end)
if (result > end) { assert(false); BigInt(0) }
else result

// GOOD:
val result = someComputation
if (result <= end) result
else result  // unreachable — the <= condition in the ensuring handles it
```

Or use `nextDoesNotPassAcceptedValue` pattern that returns `false` through the unreachable path
without `assert(false)`.

### 22.3 `res == expr` ensuring clause forces call sites to re-prove `expr`

When you write `.ensuring(res => res == someExpression)`, the call site must re-prove
`someExpression` independently. This times out if `someExpression` is complex.

**Fix:** Use `.holds` (returning the equality as the body) or `res && someExpression` in ensuring:
```scala
// BAD:
def foo(...) = someComplexComputation
}.ensuring(res => res == theResult)  // call site must re-prove theResult

// GOOD:
def foo(...) = {
  ...
  theResult
}.holds  // or .ensuring(res => res && theResult)
```

### 22.4 `mergedGapPrefix` walk must start at k=1 for seq.next

`seq.apply(0) = seq.head.value` is rejected by `seq.next` because:
- `seq.next.filterValues.head = seq.head.value`  
- `seq.head.value % seq.head.value = 0` → rejected

The correct starting point is `k=1` where:
- `seq.apply(1) = seq.next.head.value = seq.next.apply(0)`
- `seq.next.accepts(seq.apply(1))` is true (next prime is coprime to all filter values including itself)

**In `assertPipelineOutputMatchesNextGapList`:** call with `BigInt(1)` not `BigInt(0)`, and
require `nextSeq(BigInt(0)) == seq.apply(BigInt(1))` explicitly.

### 22.5 `nextSeq.head.value == seq.head.value` is impossible for seq.next

`seq.next.head.value` is the NEXT LARGER prime (`seq.apply(1) > seq.head.value`), never equal.
Using this equality as a precondition makes any lemma vacuously satisfied by seq.next (the
preconditions can never ALL hold simultaneously).

**Fix:** Replace `require(nextSeq.head.value == seq.head.value)` with
`require(seq.head.value <= nextSeq.head.value)` throughout `mergedGapPrefix` machinery (~22
occurrences). Add bridge assertions for places that deduced lower bounds from the equality:
```scala
assert(seq.apply(k) >= nextSeq.head.value)  // from nextSeq.accepts(seq.apply(k))
assert(seq.applyStrictlyIncreases(k))
assert(seq.apply(k + 1) >= nextSeq.head.value)
```

### 22.6 Make predicate functions total to eliminate precondition VCs at call sites

**Problem:** `accepts` was a PARTIAL function:
```scala
def accepts(value: BigInt): Boolean = {
  require(value >= head.value)
  passesFilter(value)
}
```
Every call `nextSeq.accepts(seq.apply(k))` generated a VC: prove `seq.apply(k) >= nextSeq.head.value`.
After replacing `require(nextSeq.head.value == seq.head.value)` with `<=`, these 21+ VCs could no
longer be discharged trivially — they all timed out.

**Fix:** Make `accepts` a TOTAL predicate:
```scala
def accepts(value: BigInt): Boolean =
  value >= head.value && passesFilter(value)
```

**Effect:** All 21 precondition VCs disappear. AND the implication now flows the other direction for
free: `accepts(v) == true` → by Stainless body-unfolding → `v >= head.value`. So a `require(accepts(v))`
anywhere gives you `v >= head.value` as a derivable fact without any extra assertion.

**Rule:** When a predicate naturally embeds a lower-bound check (`value >= head.value`), fold it INTO
the boolean expression instead of making it a `require`. This way:
- callers get acceptance checking without discharging a precondition VC
- the lower-bound fact is recoverable by Stainless unfolding wherever `accepts(v)` is known true

**Source:** ch60 `SpecSieveSequence.accepts` refactor, 2026-07-20. Reduced VC count from 4995 to 4893
and eliminated all 21 timeout-inducing precondition obligations in `SpecSieveSeqNextProperties`.

### 22.7 `indexOfAccepted(z)` must be called AFTER `accepts(z)` is established

`indexOfAccepted` has `require(accepts(value))`. If you bind `val zIdx = seq.indexOfAccepted(z)` before
establishing `seq.accepts(z)`, Stainless generates an unprovable precondition VC.

The correct order when `z` comes from `nextSeq(vIdx + 1)` (which ensures `z >= nextSeq.head.value`
and `nextSeq.accepts(z)`, but NOT `seq.accepts(z)`):
```scala
val z = nextSeq(vIdx + BigInt(1))
assert(z >= nextSeq.head.value)          // from nextSeq.apply.ensuring
assert(nextSeq.accepts(z))               // from nextSeq.apply.ensuring
assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, z))
assert(seq.accepts(z))                   // NOW established via bridge lemma
val zIdx = seq.indexOfAccepted(z)        // safe: require satisfied
```

**Rule:** Always establish `accepts(z)` (via the appropriate bridge) BEFORE binding the result of
`indexOfAccepted(z)`. Declaring the `val` before the bridge puts the precondition VC in a context
where `accepts` cannot yet be derived.

**Source:** `assertNextSuccessorOldIndexWithinBound` and `assertFirstSurvivorAtOrBeforeNextValue` in
`SpecSieveSeqNextProperties.scala`, ordering fix 2026-07-20.

### 22.8 Strict-monotonicity bridge for propagating lower bounds through index gaps

**Problem:** Need to prove `seq.apply(m) >= nextSeq.head.value` when only `seq.apply(k) >= nextSeq.head.value`
(derived from `nextSeq.accepts(seq.apply(k))` unfolding) and `m > k` are available.

**Pattern (3-step bridge):**
```scala
assert(seq.apply(k) >= nextSeq.head.value)       // from accepts unfolding
assert(seq.applyIndexStrictlyPreservesValues(k, m))  // strict monotonicity lemma
assert(seq.apply(m) > seq.apply(k))              // from strictly-preserves ensuring
assert(seq.apply(m) >= nextSeq.head.value)        // arithmetic: a > b >= c => a >= c
```

Z3 closes this in one step once the three bridge assertions are present.

**Also used for derived-index lower bounds** (when `idx` comes from a `findFirstNonMultipleAfter` call
and `idx > k`):
```scala
require(seq.apply(k) >= nextSeq.head.value)
assert(seq.applyIndexStrictlyPreservesValues(k, idx))
assert(seq.apply(idx) > seq.apply(k))
assert(seq.apply(idx) >= nextSeq.head.value)
```

**Source:** `assertSkippedOldValueRejectedByNext`, `assertNextValueAtOrBeforeFirstSurvivor` in
`SpecSieveSeqNextProperties.scala`, 2026-07-20.
