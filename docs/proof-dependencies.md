# Proof Dependency Map: Primality, Coprimality, and the Size Closed Form

**Created:** 2026-07-11
**Purpose:** A consolidated reference mapping what is VERIFIED vs. what is
OPEN in the three interlocking proof efforts:
1. `apply(1)` is prime (the sieve's first generated value).
2. The equivalences between prime-ness characterizations.
3. The next-stage gap-size closed form `|G'| = |G|·(h−1)`.

This document is **descriptive** (it records the state of the dependency graph),
not prescriptive. Each claim is backed by a `file:line` reference; lemmas marked
VERIFIED have a real proof body that passes `just verify` (baseline
`12002 valid, 0 unknown` as of 2026-07-11).

**Verification baseline (this doc's reference point):**
HEAD + the 2026-07-11 changes (cheap `isPrime`, Option B contract on
`assertCompositeSmallestPrimeDivisor`, `findSmallestDivisor` moved to `Prime`).
Full verify and no-cache verify both green at `12002 / 0 / 0`.

---

## Part 1 — `apply(1)` Is Prime

### The chain (layered, each wrapper adds one fact)

```
assertApplyOneEqualsNextPrime              [PUBLIC — the load-bearing entry]
  require: primes.nextPrime.value < head²                    ← OPEN (Bertrand)
  ├─ assertApplyOneGtHead                  ✅ apply(1) > head
  ├─ assertApplyOneAtOrBeforeOwnNextPrime  ✅ apply(1) <= nextPrime
  │     ├─ assertOwnNextPrimeAccepted      ✅ accepts(nextPrime)
  │     └─ assertApplyOneLeqValue          ✅ apply(1) <= any accepted value
  ├─ assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq
  │     require: nextPrime < head²                          ← OPEN (Bertrand)
  │     └─ assertApplyOnePrimeFromUpperBelowHeadSq
  │           ├─ assertApplyOneBelowHeadSqFromUpper  ✅ transitivity
  │           └─ assertApplyOneIsPrimeIfBelowHeadSq  ✅ THE primality core
  │                 require: apply(1) < head²                ← OPEN (Bertrand)
  └─ noPrimesBetween(head+1, nextPrime)    ✅ nextPrime postcondition
  ⟹ apply(1) == nextPrime
```

### Status of each fact

| Fact | Status | Reference |
|---|---|---|
| `apply(1) > head` | ✅ VERIFIED | `SpecSieveSequence.scala:2774` `assertApplyOneGtHead` |
| `apply(1) <= nextPrime` | ✅ VERIFIED | `SpecSieveSequence.scala:2868` `assertApplyOneAtOrBeforeOwnNextPrime` |
| `nextPrime` is prime, `> head`, no primes in `(head, nextPrime]` | ✅ VERIFIED | `AllPrimesSoFarList.scala:121-141` (postcondition) |
| `apply(1) < head² ⟹ isPrime(apply(1))` | ✅ VERIFIED (conditional) | `SpecSieveSequence.scala:2749` `assertApplyOneIsPrimeIfBelowHeadSq` |
| `nextPrime < head² ⟹ apply(1) == nextPrime` | ✅ VERIFIED (conditional) | `SpecSieveSequence.scala:2909` `assertApplyOneEqualsNextPrime` |
| **`nextPrime < head²`** (the bound itself) | ❌ **OPEN — Bertrand's postulate** | carried as `require` at `:638, :665, :2889, :2910`; never discharged |

### The single missing fact

> **`primes.nextPrime.value < head.value * head.value`** (equivalently
> `apply(1) < head²`, since `apply(1) <= nextPrime` is already proven).
> This is Bertrand's postulate: "there is always a prime between `p` and `p²`."
> It is carried as an explicit `require` at 4 call sites and re-declared by all
> 3 downstream consumers. It is never proven anywhere. The conditional
> implications are fully verified; only the bound is open.

### Downstream consumers — is the unconditional form load-bearing?

**No.** `isPrime(apply(...))` appears in exactly one file
(`SpecSieveSequence.scala`), only inside this proof chain. The public
`assertApplyOneEqualsNextPrime` is consumed by 3 sites, **all of which
re-declare the Bertrand `require`**:

| Consumer | Location |
|---|---|
| `SpecDerivedSieveSequence.assertNextHeadMatches` | `SpecDerivedSieveSequence.scala:91` (inherits from class invariant `:41`) |
| `SpecCycleSieveEquivalence.assertCurrentApplyOneEqualsSpecNextHead` | `SpecCycleSieveEquivalence.scala:311` |
| `SpecCycleSieveEquivalence.assertNextAcceptsMatchesCyclePrimesCoprime` | `SpecCycleSieveEquivalence.scala:334` |

The Bertrand precondition propagates verbatim to the top of the call tree;
nothing discharges it. So the **conditional** form is what the codebase actually
uses; making it unconditional requires Bertrand.

### Article discrepancy (worth knowing)

- `sieve-sequence-v2.md` §8 (line 503-528) claims **one** undischarged
  assumption (Bertrand) and states "No Euclid's lemma requirement remains."
- `sieve-sequence.md` §8.2-8.3 (line 644-685) lists **two** (Bertrand + Euclid).
- The code at `SpecDerivedSieveSequence.scala:41-48` carries **both** the
  Bertrand `require` AND a Euclid-style `require(mod(product(filterValues), head) != 0)`.
  The v1 article matches the code; the v2 article is optimistic.

### Stale reference

`SpecSieveSequence.scala:2747` (the Scaladoc on
`assertApplyOneIsPrimeIfBelowHeadSq`) references
`tickets/active/prove-apply1-is-prime.md`, but the ticket is at
**`tickets/blocked/prove-apply1-is-prime.md`**.

---

## Part 2 — Prime/Coprime Characterizations and Equivalences

### Catalog of characterizations

| # | Characterization | Kind | Reference |
|---|---|---|---|
| C1 | `Prime.isPrime(v)` = `noDivisorInRange(v, 2, v)` | DEFINITION | `Prime.scala:83` |
| C2 | `Prime.noDivisorInRange(n, from, to)` | DEFINITION (tail-rec) | `Prime.scala:18` |
| C3 | `Prime.findSmallestDivisor(n, from)` | DEFINITION; `ensuring mod(n,res)==0` | `Prime.scala:48` |
| C5 | `CoprimeUtils.isCoprime(v, primes)` | DEFINITION (canonical) | `CoprimeUtils.scala:14` |
| C5' | `SieveUtils.isCoprime(v, primes)` | ALIAS to C5 | `SieveUtils.scala:29` |
| C10 | `passesFilter(v)` = `isCoprime(v, primeValues(filterPrimes))` | DEFINITION | `SpecSieveSequence.scala:888` |
| C11 | `accepts(v)` = `v >= head && passesFilter(v)` | DEFINITION (tail-only filter; weaker than primality) | `SpecSieveSequence.scala:163` |
| C12 | `allPrimesSoFar(list)` = gap-free descending prime list | DEFINITION | `PrimeListUtils.scala:9` |
| C13 | `noPrimesBetween(from, to)` | DEFINITION | `PrimeListUtils.scala:34` |
| C15 | `containsAllPrimesUpTo(max, values)` | DEFINITION (ch6 content form) | `CompletePrimePrefix.scala:30` |

### Master equivalence table

| Fact | Direction | Status | Reference | Preconditions |
|---|---|---|---|---|
| `isPrime ⟺ noDivisorInRange(v,2,v)` | both | ✅ VERIFIED (by definition) | `Prime.scala:83` | `v>=0` |
| `isPrime ⟺ findSmallestDivisor(v,2)==v` | both | ✅ VERIFIED | `Prime.scala:72`; `PrimeProperties.scala:54` | `v>1` |
| `isPrime(v) ⟹ isCoprime(v, smallerPrimes)` | ⟹ | ✅ VERIFIED | `PrimeUtils.scala:177` `primeIsCoprimeWithSmallerList` | descending, head<v |
| `isCoprime(v, primes) ⟹ isPrime(v)` | ⟹ | ✅ VERIFIED **with completeness** | `PrimeProperties.scala:475` `assertHeadIsPrime` | **`assertAllNotCoprimeInRange(v,2,primes)`** (every d in [2,v) has a prime factor in the list) |
| `isCoprime ⟹ ∀p. mod≠0` (unfold) | ⟹ | ✅ VERIFIED | `CoprimeUtils.scala:60` `assertIsCoprimeForAll` | checkAllPositive |
| `(∀p. mod≠0) ⟹ isCoprime` (fold) | ⟹ | ❌ **MISSING (standalone)**; folded inline in callers | — | — |
| `allPrimesSoFar ⟹ prime≤head ∈ list` (membership) | ⟹ | ✅ VERIFIED | `PrimeListUtils.scala:80` `primeAtOrBelowHeadIsContained` | isPrime(value), value≤head |
| `allPrimesSoFar ⟹ list = exactly primes below head` (content) | both | ❌ **MISSING** | — | — |
| `allPrimesSoFar ⟹ filterValues == primes below head` | both | ❌ **MISSING** | — | — |
| `allPrimesSoFar ⟹ containsAllPrimesUpTo` (bridge C12→C15) | ⟹ | ❌ **MISSING** | — | — |
| two distinct primes don't divide each other | ⟹ | ✅ VERIFIED | `FilterPreservesPrimesProperties.scala:121` | — |

### The Bézout / Euclid layer (all VERIFIED)

| Tag | Lemma | Proves | Reference |
|---|---|---|---|
| B1-B4 | Bézout identity, gcd divides both, coprime⟹g=1, linear combo =1 | foundation | `BezoutUtils.scala:115-244` |
| **B7** | `assertPrimeDivProductImpliesDivFactor` | `isPrime(p) ∧ p∤h ∧ p∣k·h ⟹ p∣k` (Euclid, direct via Bézout) | `BezoutUtils.scala:282` (41/41) |
| **B8** | `assertPrimeProductNotDivisible` | `isPrime(p) ∧ p∤k ∧ p∤h ⟹ p∤k·h` (**the contrapositive**) | `BezoutUtils.scala:367` (31/31) |
| E5 | `euclidLemmaPrime` | `isPrime(p) ∧ p∣a·b ∧ a<p ⟹ p∣a ∨ p∣b` (disjunction) | `EuclidLemma.scala:166` (50/50) |
| E6 | `euclidConsequence` | `isPrime(p) ∧ p∤k ∧ p∣k·h ⟹ p∣h` | `EuclidLemma.scala:221` (38/38) |
| — | `assertTwoFactorsProductNotDiv` | 2-factor non-divisibility via B7 | `EuclidLemma.scala:299` (18/18) |
| — | `assertPeelDividesTail` | peel step (implication) | `EuclidLemma.scala:413` (12/12) |

B8 broke the "contrapositive wall" — it proves the 2-factor contrapositive
**directly** from the Bézout linear combination, not by deriving a contrapositive
from an implication (which Stainless cannot do in one VC).

### The three real gaps in the equivalence graph

1. **Reverse coprimality lift** (`∀p. mod≠0 ⟹ isCoprime`) — missing as a
   standalone lemma. The fold is performed inline inside callers
   (`primeIsCoprimeWithSmallerList` reconstructs `isCoprime` by recursion while
   asserting each `mod(v,p)≠0`), but no named, reusable lemma exports it.

2. **`allPrimesSoFar` content/completeness** — only *membership* is exported
   (`primeAtOrBelowHeadIsContained`). Exact-content ("list = the primes below
   head"), counting, duplicate-freedom, and the bridge to `containsAllPrimesUpTo`
   (the ch6 content predicate) are all **missing**. Within `loopCheckAllPrimesSoFar`
   per-element `isPrime(head)` IS checked, but that fact is internal to the
   recursion and not exported.

3. **List-product non-divisibility** (`assertPrimeNotDivideProduct`): a prime h
   does not divide the product of a list of smaller values. **DRAFT, commented
   out** at `EuclidLemma.scala:316-347` and `:363-395`. Base + 2-factor step
   verified; recursive composition times out (3 attempts). See Part 3.

---

## Part 3 — The Size Closed Form `|G'| = |G|·(h−1)`

### The chain of equalities

```
|G'| = |G|·(h−1)                                    [TARGET — UNPROVEN]
 │
 ├─ L1  |G'| = |nextRotatedGaps|                   ✅ VERIFIED (rotation preserves size)
 │      SieveSequenceNextLevel.scala:61-67
 │
 ├─ L2  = |nextGaps|                               ✅ VERIFIED (assertNextGapsSize)
 │      SieveSequenceNextLevel.scala:263
 │
 ├─ L3  = |nextFiltered|.size                      ✅ VERIFIED (assertCalculateGapsSize)
 │      SieveUtils.scala:397
 │
 ├─ L4  = |residues|·(h−1)          ◀── FACT A     ❌ BLOCKED
 │      │
 │      ├─ A1  |expanded| = |residues|·h           ✅ VERIFIED
 │      │      assertExpandResiduesSize  SieveUtils.scala:751
 │      │        ├─ assertExpandSingleResidueSize  SieveUtils.scala:723
 │      │        ├─ assertAddOffsetSize            SieveUtils.scala:679
 │      │        └─ assertAppendSize               SieveUtils.scala:699
 │      │
 │      └─ A2  |removed| = |residues|              ❌❌ BLOCKED (THE LINCHPIN)
 │             │  = #{j∈[0,M): j coprime to P̄}
 │             │
 │             ├─ Route 1 (product): gcd(h, product(tailPrimes))=1
 │             │     ├─ n-factor induction "h ∤ product(tailPrimes)"
 │             │     │   └─ assertPrimeNotDivideProduct  ❌ COMMENTED OUT (3 timeouts)
 │             │     │      EuclidLemma.scala:323-347, 363-395
 │             │     ├─ assertTwoFactorsProductNotDiv    ✅ 18/18
 │             │     ├─ assertPeelDividesTail            ✅ 12/12
 │             │     └─ A3 findSmallestDivisor decomp    ❌ REVERTED, last 27/30
 │             │
 │             ├─ Route 2 (per-prime, avoids product): per-prime B8, then n-factor list lift
 │             │     ├─ B8 assertPrimeProductNotDivisible ✅ 31/31
 │             │     ├─ n-factor lift over prime list       ❌ UNWRITTEN
 │             │     └─ ⟸ could re-route via allPrimesSoFar (see below)
 │             │
 │             ├─ CRT crux (uniqueness + existence)        ❌ UNWRITTEN
 │             │
 │             └─ LIST↔VALUE bridge                       ❌ MISSING
 │                    |filterList(expandResidues,h)| = #{coprime h-mults}
 │
 └─ L5  = |G|·(h−1)                  ◀── FACT B    ⚠️ UNTESTED (not attempted)
        |residues| = |G| (cardinality)
        positional lemmas exist (assertResiduesComplete, SieveUtils.scala:1011)
        but NO cardinality bridge. High timeout risk.
```

### Bottom line on the chain

- **L1, L2, L3, A1: VERIFIED.** If A2 landed, the ticket would have a valid
  *partial* closed form `|G'| = |residues|·(h−1)` (Fact A) without Fact B.
- **A2 is the single hard blocker.** It needs three unwritten pieces:
  (i) a 2-factor→n-factor list lifting, (ii) the CRT uniqueness/existence crux,
  (iii) the list↔value-count bridge.
- **Fact B (`|residues|=|G|`) is untouched**, gated behind A, rated high-risk.

### The A2 blocker — three unwritten pieces

**Piece (i): 2-factor → n-factor list lifting.**
B8 gives the 2-factor case. A2 needs it lifted over the whole prime list.
This is structurally the same composition that times out on the product route
(`assertPrimeNotDivideProduct`, 3 timeouts) and the findSmallestDivisor route
(A3, 27/30 reverted). The blocker is **solver-visibility / composition**,
not math — every atomic piece (B8, B7, `assertTwoFactorsProductNotDiv`,
`assertPeelDividesTail`) is green; only the recursive IH-discharge times out
(LEARNINGS §1.2 family).

**Piece (ii): CRT uniqueness/existence.**
For the value-domain framing: `for each residue r, exactly one j in [0,h)
makes mod(r + j·M, h) == 0`. Needs `gcd(h,M)=1` (which is piece (i) in product
form). The per-prime route (B8) sidesteps the bijection but still needs the lift.

**Piece (iii): list↔value-count bridge.**
`filterList(expandResidues(...), h).size == count of coprime h-multiples`.
No lemma connects the list structure to the value-domain count.
`assertExpandedCoprime` (soundness, per-element) and `assertResiduesComplete`
(containment) exist but stop short of a size/counting fact.

### The `allPrimesSoFar` re-route (promising, not free)

The active ticket does **not** mention `allPrimesSoFar`; it frames A2 exclusively
via `product(tailPrimes)`. But the completeness invariant offers a product-free
alternative that matches the native per-prime definition of `isCoprime`:

- For each tail prime `p`: `mod(h,p) ≠ 0` is immediate from `h > p` (the head is
  a larger prime) — no product needed, no Euclid needed.
- B8 then gives `mod(j,p)≠0 ∧ mod(h,p)≠0 ⟹ mod(j·h,p)≠0`, per-prime.
- `allPrimesSoFar` guarantees the tail list is *complete* (so per-prime checks
  cover all relevant primes, with no missing factor).

**This is exactly the ticket's own dangling option** (lines 540-577: "A2 may not
strictly need product-non-divisibility — Re-examine whether A2 can use B8
per-prime instead of via the product").

**Caveats — the re-route does NOT eliminate:**
1. The n-factor list induction (piece (i)) — just reframes it over the prime list
   with a cleaner precondition source.
2. The list↔count bridge (piece (iii)).
3. It needs an `allPrimesSoFar` `require` threaded into the A2 lemma (consistent
   with the documented "strengthen requires over re-derivation" lesson).

**Net:** the re-route is a *better-conditioned framing of Route 2*, not a
substitute for the remaining induction/bridge work. But it removes the fragile
primorial/product bridge (LEARNINGS §4.2) and aligns with how `isCoprime` is
natively defined.

---

## Part 4 — Synthesis: The Three Open Points and How They Relate

| Open point | Real blocker | Difficulty |
|---|---|---|
| `apply(1)` always prime | Bertrand's postulate (`nextPrime < head²`) | **Hard** — major number theory; article judges "beyond current scope" |
| Prime-def equivalences | (a) reverse coprime fold, (b) `allPrimesSoFar` content form, (c) list-product non-divisibility | (a)(b) Medium, (c) Blocked-at-composition |
| Size closed form | A2 (n-factor lift + CRT + list↔count bridge), then Fact B | **Hard** — multiple unwritten pieces |

### Key relationships (these are easy to conflate — keep them distinct)

1. **`apply(1)` prime ⟂ size closed form.** They are *independent*. The size
   proof does not consume `isPrime(apply(1))`; it works on residue/gap counts.
   Fixing Bertrand does not unblock the size proof, and vice versa.

2. **The size proof's "product" is an artifact of framing, not a requirement.**
   The per-prime definition of `isCoprime` (and `allPrimesSoFar`'s completeness)
   never needs the product. The product entered via the CRT-bijection framing.
   The per-prime + B8 route (Route 2) avoids it — but still needs the n-factor
   list lift, which is the genuine hard piece.

3. **The "missing equivalence" (isPrime's converse) is not the size blocker.**
   Inside the sieve, `allPrimesSoFar` supplies the completeness precondition
   that `assertHeadIsPrime` needs. The size proof's blocker is list-composition,
   not the isPrime↔coprime biconditional.

4. **B8 broke the contrapositive wall but is not sufficient.** It proves the
   2-factor case directly. The n-factor lifting (over the prime list) is the
   remaining composition problem — a solver-visibility issue, not a math wall.

### Recommended attack order (lowest-risk, highest-information first)

1. **`allPrimesSoFar` content lemma** (Part 2 gap #2): prove
   `allPrimesSoFar(list) ⟹ filterValues == primes below head` (or the
   `containsAllPrimesUpTo` bridge). This is the cleanest gap — it uses the
   already-verified `primeAtOrBelowHeadIsContained` + `noPrimesBetween`
   machinery, and it unblocks the per-prime re-route of A2. **Medium risk.**

2. **Reverse coprime fold** (Part 2 gap #1): package the inline fold as a
   standalone `(∀p. mod≠0) ⟹ isCoprime` lemma. Low number-theory content;
   structural induction over the list. **Lower risk.**

3. **A2 via per-prime B8 + the content lemma** (Part 3, Route 2): with gaps #1
   and #2 closed, attempt the n-factor list lift using B8 per-prime over the
   complete prime list. The composition risk remains, but the precondition
   sourcing is cleaner. **Medium-high risk.**

4. **Bertrand's postulate** (Part 1): only if the unconditional form becomes
   load-bearing. Currently it is not — all consumers carry the conditional form.
   **Do not start casually — weeks of work.**

---

## Appendix — File/Line Quick Reference

### Chapter 5 (prime foundations)
- `Prime.scala:83` — `isPrime` definition
- `Prime.scala:48` — `findSmallestDivisor` (with `mod` ensuring)
- `Prime.scala:72` — `assertFindSmallestDivisorEquivNoDivisorInRange`
- `CoprimeUtils.scala:14` — `isCoprime` (canonical)
- `CoprimeUtils.scala:60` — `assertIsCoprimeForAll` (unfold)
- `CoprimeUtils.scala:85` — `assertNoDivisorByFactorList`
- `PrimeUtils.scala:177` — `primeIsCoprimeWithSmallerList` (isPrime ⟹ coprime)
- `PrimeListUtils.scala:9` — `allPrimesSoFar`
- `PrimeListUtils.scala:34` — `noPrimesBetween`
- `PrimeListUtils.scala:80` — `primeAtOrBelowHeadIsContained` (membership)
- `AllPrimesSoFarList.scala:121` — `nextPrime` (postcondition: prime, > head, gap)
- `PrimeProperties.scala:475` — `assertHeadIsPrime` (coprime ⟹ prime, w/ completeness)
- `PrimeProperties.scala:599` — `assertCompositeSmallestPrimeDivisor` (Option B: +mod contract)
- `BezoutUtils.scala:282` — B7 `assertPrimeDivProductImpliesDivFactor` (41/41)
- `BezoutUtils.scala:367` — B8 `assertPrimeProductNotDivisible` (31/31, contrapositive)
- `EuclidLemma.scala:166` — E5 `euclidLemmaPrime` (disjunction, 50/50)
- `EuclidLemma.scala:221` — `euclidConsequence` (38/38)
- `EuclidLemma.scala:299` — `assertTwoFactorsProductNotDiv` (18/18)
- `EuclidLemma.scala:316-347` — `assertPrimeNotDivideProduct` **(DRAFT, commented out)**

### Chapter 6 (sieve)
- `SpecSieveSequence.scala:67` — `apply(k)` (postcondition: accepted, in range)
- `SpecSieveSequence.scala:163` — `accepts`
- `SpecSieveSequence.scala:888` — `passesFilter`
- `SpecSieveSequence.scala:2749` — `assertApplyOneIsPrimeIfBelowHeadSq` (conditional primality)
- `SpecSieveSequence.scala:2909` — `assertApplyOneEqualsNextPrime` (the public conditional)
- `SieveUtils.scala:679-758` — expansion-size lemmas (A1)
- `SieveUtils.scala:397` — `assertCalculateGapsSize`
- `SieveSequenceNextLevel.scala:263` — `assertNextGapsSize`

### Active tickets
- `tickets/active/next-gaps-size-closed-form.md` — the size closed form
- `tickets/blocked/prove-apply1-is-prime.md` — apply(1) primality (note: code references `active/`, stale)
- `tickets/blocked/primorial-not-divisible-by-new-prime.md` — the product-composition gap
