# Next-Gaps Size Closed Form: |G'| = |G| · (h - 1)

**Created:** 2026-07-09
**Updated:** 2026-07-09
**Status:** Plan phase
**Depends on:** `fix-ch6-timeout-file-by-file.md` (complete, green baseline), `sieve-sequence-proof.md` (active, P2 open)

## Related Tickets

- `fix-ch6-timeout-file-by-file.md` — chapter-6 timeout elimination (complete). Resolved the
  `assertNextGapsSize` *congruence* VC (`|gaps| == |survivors|`) by strengthening
  `require(nextSorted(seq).list.nonEmpty)`. Did NOT prove the multiplicative closed form.
  Key lesson: the surrounding VCs are fragile; prefer explicit `require`s over solver
  re-derivation of facts like `nonEmpty` / `modulus > 0`.
- `sieve-sequence-proof.md` — P2 walk connection (3 timeouts). Different problem
  (walk-vs-`gapList` list-builder equality), NOT the gap count. Key lesson for this ticket:
  proving equality/size between two opaque recursive list-builders times out; keep the
  proof *local* to one builder and induct on the list itself.
- `sieve-properties-step5-coprime-to-modulus.md` (done) — Path B for coprime-to-modulus.
- `verify-timeout-root-cause.md` (done) — primorial/product bridge gap (LEARNINGS §4.2).

## Goal

Prove the closed form for the next-stage gap count as a standalone `.holds` lemma:

```text
|G'| = |G| · (h - 1)
```

where `G' = nextRotatedGaps(seq)` (size-preserving rotation of `nextGaps`), `G = seq.gapCycle`,
`h = seq.head`. Currently `articles/chapter6/sieve-sequence-v2.md` §7.3 (lines 487–501)
states this is "pending". The only verified size fact today is the weaker congruence
`|nextGaps| == |nextSorted|.list.size` (`SieveSequenceNextLevel.scala:263`).

## Current State

- Verification: GREEN. `fix-ch6-timeout-file-by-file.md` reports ch6 4678/4678, 0 unknown.
  (Will re-confirm baseline with `just verify` before any code change — no `logs/verify.log`
  exists in this session yet.)
- `assertNextGapsSize` (`SieveSequenceNextLevel.scala:263`) proves `|gaps| == |survivors|`
  via `SieveUtils.assertCalculateGapsSize`. Delegates to `calculateGaps(sorted, M).size == sorted.size`.
- Rotation is size-preserving: `assertRotateSameSize` (ch3 `RotationProperties`) is verified.
  So `|G'| = |nextGaps|` is free; the real work is `|nextGaps| = |G|·(h−1)`.
- Existing size lemmas usable:
  - `ListRepeatProperties.assertRepeatSize` — `repeat(list, times).size == list.size * times`.
    Right algebra, but NOT wired to `expandResidues` (which uses `addOffset`+`++`, not `repeat`).
  - `SieveUtils.assertPairwiseGapsSize` — `pairwiseGaps(list).size == list.size - 1`.
  - `SieveUtils.assertCalculateGapsSize` — `calculateGaps(sorted, M).size == sorted.size`.

## Expected State

One or more new `.holds` lemmas (likely in `SieveUtils.scala` and/or
`SieveSequenceNextLevel.scala`) proving the closed form, with ch6 still GREEN (0 unknown).
Article §7.3 rewritten to the rigorous CRT/density argument and the "pending" note updated
or removed.

## Approaches Considered

The closed form decomposes into TWO independent facts. Per user direction, attempt
sequenced: easy half first (verify green), then hard half (stop-and-ask after 3 timeouts).

### Fact A (EASY half): |filtered| = |residues| · (h - 1)

```text
nextFiltered(seq) = filterList(nextExpanded(seq), seq.head)
nextExpanded(seq) = expandResidues(residues(M, Pbar), M, h)   // = values in [0, h*M) coprime to Pbar
|nextExpanded|     = h * |residues|                            // [sub-lemma A1]
|nextFiltered|     = |nextExpanded| - (multiples of h in nextExpanded)
                   = h*|residues| - |residues|                 // [sub-lemma A2: CRT density]
                   = |residues| * (h - 1)
```

**Sub-lemma A1** — `expandResidues(r, M, h).size == h * r.size`.
Built on a general `addOffset` size lemma (`addOffset(L, off).size == L.size`) and
an `append` size lemma (`(a ++ b).size == a.size + b.size`). Neither exists today;
both are trivial structural inductions (ch3-appropriate, no number theory). Induct on `p - i`
in `expandSingleResidue`.

**Sub-lemma A2** — multiples of `h` among the expanded coprime residues = `|residues|`.
This is the CRT step. Since `h` is prime and `h > p` for every `p ∈ P̄`, `gcd(h, M) = 1`.
By CRT, the map `x ↦ (x mod h, x mod M)` is a bijection on `[0, h·M)`. The multiples of
`h` in `[0, h·M)` are `{0, h, 2h, …, (M−1)h}`; their residues mod `M` run through all of
`[0, M)` exactly once. A multiple of `h` is coprime to `P̄` iff its `mod M` residue is
coprime to `P̄`, i.e. iff it is in `residues`. So the count = `|residues|`.

A2 is the linchpin and the hardest part of the EASY half. Candidate lemmas to reuse:
`ConsecutiveIntegers.countModZeroEqualsM` (exactly `m` multiples of `p` in `m·p` consecutive
integers) and `densityForDivisor` (when `divisor | modulus`). The bridge to "coprime to P̄
AND divisible by h" needs `gcd(h, M) = 1`, which is adjacent to `assertNextHeadCoprimeToPrimes`
(`SieveSequenceNextLevel.scala:185`, about the NEW head) but for the CURRENT head must cross
the primorial/product bridge (LEARNINGS §4.2 — known fragile territory).

**Status:** RECOMMENDED (attempt first). Pure density + CRT, no cycle structure. Sidesteps
the hard cycle-counting entirely. Yields a valid closed form `|G'| = |residues|·(h−1)` even
without Fact B.

**Risk:** A2's coprime-to-product precondition may hit the primorial/product bridge timeout.
Mitigation: state `gcd(h, M) = 1` (or equivalently `isCoprime(h, Pbar)`) as an explicit
`require` rather than deriving it — consistent with the `fix-ch6-timeout` lesson that
strengthening `require`s beats re-derivation.

### Fact B (HARD half): |residues| = |G|

A *counting form* of the §6 current-stage equivalence: the residue scan
(`generateResidues`, which emits each value in `[0, M)` coprime to `P̄`) and the gap
cycle `G` (adjacent differences between accepted values in `[h, h+M)`) encode the same
survivor set, hence have the same count.

**Status:** UNTESTED, high risk. Same difficulty family as the §5.2 gap-cycle
reconstruction and the P2 walk timeouts in `sieve-sequence-proof.md`. The survivor-set
equality is established positionally (`assertResiduesComplete`, `assertGenerateResiduesContainsCoprime`)
but never as a *cardinality* fact.

**Risk:** Likely timeout. Per `sieve-sequence-proof.md` lesson, do NOT prove list-builder
equality directly; instead count via the bijection. If it times out 3× → STOP and ask.
The easy half (Fact A) stands on its own regardless.

### Composition

`|G'| = |nextRotatedGaps|` (rotation, size-preserving, free via `assertRotateSameSize`)
      `= |nextGaps|` (via `assertNextGapsSize`, already verified)
      `= |nextFiltered|` (via `assertCalculateGapsSize`, already verified)
      `= |residues| · (h − 1)` (Fact A)
      `= |G| · (h − 1)` (Fact B, if it lands)

## Risks / Assumptions

- **Assumption:** `h` is coprime to every tail prime (so `gcd(h, M) = 1`). True for every
  real sieve stage (head is prime, larger than all tail primes). May need to be a `require`.
- **Assumption:** `expandResidues`'s `addOffset`+`++` structure admits a clean size induction.
  Needs the two missing ch3 lemmas (addOffset size, append size). Trivial but must be added.
- **Risk:** Fact B (|residues| = |G|) may be unprovable in reasonable time. The ticket is
  valuable even if only Fact A lands — it converts "pending" into a verified (if differently-
  shaped) closed form and isolates the true open problem.
- **Rule compliance:** ONE assertion/lemma per verify cycle. Verify between each. Never
  modify MemCycle/ModCycle/CycleIntegral. Use `Calc.mod`/`Calc.div`, never `%`.

## How to validate

1. `just verify` green BEFORE any change (baseline).
2. After each new lemma: `just verify <FunctionName>` focused → if green, `just verify` full.
3. Stop-and-ask after 3 failed attempts on any single VC.
4. Final: ch6 valid count unchanged-or-higher, 0 unknown.
5. Article §7.3 rewritten and cross-checked for framing-integrity (abstract/conclusion match).

## START HERE

1. Confirm green baseline with `just verify` (no log exists this session).
2. Sub-lemma A1: add `addOffset` size lemma + `append` size lemma in ch3 (or SieveUtils
   if ch3 placement risks cross-file timeouts), then `assertExpandResiduesSize`. ONE per
   verify cycle.
3. Sub-lemma A2: the CRT/density bridge. State coprime precondition as `require` first.
4. Compose into `assertNextFilteredSizeClosedForm` (or similar) = `|filtered| = |residues|·(h−1)`.
5. Only if A is green: attempt Fact B.

## Progress Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-09 | Ticket created. Confirmed via git history that NO standalone closed-form size lemma was ever committed — article "pending" is accurate. The prior timeout was the congruence VC (resolved by `require`), not a closed-form attempt. | — |
| 2026-07-09 | Baseline green: 11502 valid, 0 unknown (66s, cached). | — |
| 2026-07-09 | **A1a DONE.** `assertAddOffsetSize` (addOffset preserves size). Focused 6/6. | added to SieveUtils |
| 2026-07-09 | **A1b DONE.** `assertAppendSize` ((a++b).size == a.size+b.size). Focused 6/6. | added to SieveUtils |
| 2026-07-09 | **A1 DONE.** `assertExpandSingleResidueSize` (== residues.size*(p-i)) + `assertExpandResiduesSize` (== residues.size*p). Composes A1a+A1b by induction on p-i. Focused 11/11 then 6/6. | added to SieveUtils |
| 2026-07-09 | **Full verify after A1: 11531 valid, 0 unknown** (+29 over baseline). A1 foundation globally clean. | — |
| 2026-07-09 | A2 is the deep step: needs per-residue "exactly one j in [0,h) makes mod(r+j*M,h)==0", which is modular-inverse / CRT reasoning requiring gcd(h,M)=1. Highest timeout risk. `assertNoDivisorByFactorList` (CoprimeUtils:85) is the closest existing Euclid-style lemma. Strategy decision pending before proceeding. | — |

## A2 strategy note (2026-07-09)

The `|removed| = |residues|` count needs, for each residue r, exactly one j in [0,h) with
mod(r + j*M, h) == 0. This is the CRT bijection (multiplication by M mod h is a permutation
when gcd(M,h)=1). Two sub-strategies:

- **A2-count**: recursive count over expandSingleResidue blocks, per-block lemma
  "block j contributes 1 multiple of h per residue iff mod(r + j*M, h)==0, and summed over
  j exactly 1 per residue". Needs the modular-permutation fact.
- **A2-density-via-hM**: reframe on [0, h*M). There are exactly M multiples of h in
  [0, h*M) (countModZeroEqualsM(0, h, M)). Of those, the ones coprime to Pbar = |residues|
  by CRT. Same core fact, different framing.

Both need the gcd(h,M)=1 ⟹ "mod(j*M, h) permutes [0,h)" fact, which has no existing lemma.
This is the genuine open risk. If 3 timeouts → stop-and-ask (the easy half still yields
|filtered| = |residues|*(h-1) only if A2 lands; without A2 we have |expanded| = |residues|*h
but not the filter count).

## A2 BLOCKED — Euclid converse required, no Bezout machinery (2026-07-09)

User selected A2-density route. Investigation confirmed that **every** route to the filter
count requires the **Euclid converse**: `isPrime(p) ∧ mod(k,p)≠0 ∧ mod(h,p)≠0 ⟹ mod(k·h,p)≠0`
("a prime divides a product only if it divides a factor").

- The expanded-list count A1 is proven (`|expanded| = |residues|·h`).
- The filter count A2 needs: a multiple `k·h` of the new head is coprime to a tail prime `p`
  iff `k` is coprime to `p` — i.e. exactly the Euclid converse (since `h` is coprime to `p`).
- Existing lemmas cover only the FORWARD direction: `assertMultiplePreservesDivisible`
  (p|b ⟹ p|a·b) and `assertNoDivisorByFactorList` (n coprime, d not ⟹ n∤d). Neither gives
  the converse.

**Attempt (1, the only one made):** `assertPrimeProductNotDivisible` stated as a bare
postcondition (no proof body), `isPrime(p)` as a `require`. Result: **TIMEOUT** (1 unknown,
300s on postcondition, `U:smt-z3`). Reverted to green (11531 valid, 0 unknown).

**Root cause:** The codebase has NO Bezout / extended-Euclid / unique-factorization
machinery. `Prime.isPrime` is defined structurally as "no divisor in [2,n)". The elementary
proof of Euclid's lemma fundamentally requires either Bézout's identity (gcd = linear
combination) or unique factorization — neither is formalized. Proving it here would be a
major standalone undertaking (a Euclid/Bezout theory in chapter 5), not a single-lemma
addition to the size proof.

**Status:** A2 BLOCKED on the Euclid converse. The closed form `|G'| = |G|·(h−1)` cannot
be completed without it. Per stop-and-ask: NOT iterating variations on the bare assertion
(would just re-timeout). Options for the user:
  1. Build a Bezout/extended-Euclid theory in ch5 (large, separate effort), then retry A2.
  2. Accept A1 as partial progress: `|expanded| = |residues|·h` is verified; document A2 +
     the Euclid-converse dependency as the precise open hole in the article.
  3. Accept the filter count as an additional axiom (analogous to Bertrand's postulate in §8).

**Banked result (green):** 4 new verified lemmas in SieveUtils.scala:
`assertAddOffsetSize`, `assertAppendSize`, `assertExpandSingleResidueSize`,
`assertExpandResiduesSize`. Full verify 11531/0/0 (+29 over baseline).

## Resolution path chosen (2026-07-09): Route B — Euclid first, then density

User decision: prove Euclid's lemma (minimal-counterexample, Route B) as the foundation,
THEN build the density counting on top. Rationale: every route (direct filter-count,
density/inclusion-exclusion, even `gcd(h,M)=1` as a precondition) reduces to Euclid's lemma
at the "1/head" uniformity step. The density framing is the natural way to PRESENT the math,
but it cannot AVOID the hard number theory — proving it once unblocks everything.

Draft proof already exists: `tickets/blocked/primorial-not-divisible-by-new-prime.md:60-87`
(the minimal-counterexample `euclidLemmaPrime` recursing on `d = mod(p,a) < a`).

### Phase 1 — Euclid's lemma (new object `EuclidLemma` in ch5 properties)

- **E1** `assertDivModReconstruct(a,b)`: `div(a,b)*b + mod(a,b) == a` (from DivMod invariant).
- **E2** `assertRemainderLessThanDivisor(a,b)`: `0 <= mod(a,b) < b` (from Calc.mod ensuring).
- **E3** `assertPrimeNotDividedBySmaller(a,p)`: `isPrime(p) ∧ 0<a<p ⟹ mod(p,a)≠0`.
- **E4** `assertSubStepDivDb(a,b,p)`: the hard step — `p|a*b, d=mod(p,a) ⟹ p|d*b`
  (via `d*b = (p-q*a)*b = p*b - q*(a*b) = p*(b - q*k)`).
- **E5** `euclidLemmaPrime(a,b,p)`: composes E2-E4 + IH, `decreases(a)`.
- **E6** `euclidLemmaPrimeContrapositive(k,h,p)`: `isPrime(p) ∧ mod(k,p)≠0 ∧ mod(h,p)≠0 ⟹ mod(k*h,p)≠0`
  (the exact form A2 needs; by contradiction via E5).

### Phase 2 — Density counting (on top of Euclid)

- **D1** Intersection: `p1,p2 distinct primes ⟹ (p1|n ∧ p2|n ⟺ p1*p2|n)` (Euclid corollary).
- **D2** Survivor count in a period = |residues| (forward divisibility, no Euclid).
- **D3** "1/head" uniformity = corollary of E6.
- **D4** Closed form: `|filtered_next| = |residues|*(h-1)`; if Fact B `|residues|=|G|` lands, `|G'|=|G|*(h-1)`.

### Phase 3 — Article §7.3 rewrite (density framing) + OBJECTS.md + ticket outcomes.

## Phase 1 PROGRESS (2026-07-09): Euclid's lemma — 6 of 7 lemmas verified, 1 wrapper timed out

New object `EuclidLemma` (`src/main/scala/v1/chapter5/prime/properties/EuclidLemma.scala`).
Full verify **11655/0/0** (+124 over the 11531 baseline). Built bottom-up, one lemma per cycle:

| Lemma | Proves | Status |
|---|---|---|
| E1 `assertDivModReconstruct` | `div(a,b)*b + mod(a,b) == a` | 11/11 DONE |
| E2 `assertRemainderLessThanDivisor` | `0 <= mod(a,b) < b` (for decreases) | 2/2 DONE |
| E3 `assertPrimeNotDividedBySmaller` | `isPrime(p) ∧ 2<=a<p ⟹ mod(p,a)≠0` | 14/14 DONE |
| E4 `assertSubStepDivDb` | the hard step: `p\|a*b, d=mod(p,a) ⟹ p\|d*b` | 27/27 DONE (first attempt, no timeout — the step-by-step substitution chain worked, LEARNINGS §6.1) |
| E5 `euclidLemmaPrime` | `isPrime(p) ∧ p\|a*b ∧ a<p ⟹ (p\|a ∨ p\|b)` via well-founded induction on a | 39/39 DONE (needed an explicit `a==1` base case; the `a>=2` guard for E3 was the one invalid VC, fixed by splitting) |
| — `euclidConsequence` | `isPrime(p) ∧ p\|k*h ∧ p∤k ⟹ p\|h` (the useful direction, via E5 + mod-reduction of k) | 31/31 DONE |
| E6 `euclidLemmaPrimeContrapositive` | `isPrime(p) ∧ p∤k ∧ p∤h ⟹ p∤k*h` (exact form A2 needs) | **3 TIMEOUTS, reverted** |

### E6 timeout detail (stop-and-ask, 3 attempts)

The contrapositive wrapper `euclidLemmaPrimeContrapositive` — `isPrime(p) ∧ mod(k,p)≠0 ∧ mod(h,p)≠0 ⟹ mod(k*h,p)≠0` —
timed out 3 times (300s each, `U:smt-z3`, postcondition VC):
1. Original combined form (mod-reduction bridge + conditional contradiction + E5 call in one body).
2. Split: `euclidConsequence` (the implication `p|k*h ∧ p∤k ⟹ p|h`, which verified 31/31) + a thin `if(mod==0){assert consequence; false} else {true}` wrapper.
3. Restructured wrapper with `val productMod` + conditional asserting the consequence.

The implication (`euclidConsequence`) verifies cleanly; the **contrapositive wrapping** — turning
"mod==0 ⟹ contradiction with mod(h,p)≠0" into the postcondition `mod(k*h,p)≠0` — is what the solver
cannot close in 300s. This matches LEARNINGS §1.2/§1.3: the derived fact (the contradiction) is not
visible at the postcondition.

**Key observation:** `euclidConsequence` (verified) already proves the mathematically substantive
direction: "if p divides k*h and p doesn't divide k, then p divides h." The contrapositive
(`p∤k ∧ p∤h ⟹ p∤k*h`) is logically equivalent and is what A2's "1/head" step wants, but Stainless
cannot derive the contrapositive from the implication within one VC.

### Options for the user (E6)

1. **Use euclidConsequence directly in A2.** A2 needs "k*h coprime to p ⟺ k coprime to p (given h coprime to p)". The (⇐) direction is: assume `mod(k*h,p)≠0` is what we want to show, given `mod(k,p)≠0 ∧ mod(h,p)≠0`. By euclidConsequence, if `mod(k*h,p)==0` then `mod(h,p)==0` — contradicting `mod(h,p)≠0`. A2's own lemma can call euclidConsequence and structure the contradiction *locally* in A2's context (where the surrounding facts may make it easier than the standalone wrapper). Try this before more E6 attempts.
2. **Prove E6 as a `.ensuring` postcondition** (LEARNINGS §1.2): make euclidConsequence's postcondition include the contrapositive, so callers see it directly.
3. **Accept euclidConsequence as the verified result** and state A2's "1/head" step using the implication form rather than the contrapositive (reframe A2's proof to use "if a survivor were divisible by h, then..." contradiction locally).

Recommend option 1 (try euclidConsequence in A2's context first) — the standalone contrapositive
wrapper may be harder than the in-context use.

**User decision (2026-07-09):** Option 1 — skip standalone E6, use euclidConsequence in A2's context.

## Phase 2 — A2 route refined (2026-07-09), using euclidConsequence

The cleanest A2 route avoids the per-residue CRT bijection (which needs both existence AND
uniqueness, each needing gcd(M,h)=1 ⟹ Euclid-on-product). Instead use the **value-domain
density** directly:

- `expanded` = the values in `[0, h*M)` coprime to Pbar (assertResiduesComplete + offset structure).
- `removed` = those coprime-to-Pbar values ALSO divisible by h.
- A value `v` in `[0, h*M)` divisible by h has form `v = j*h`, `j in [0, M)`.
- `v = j*h` coprime to tail prime p  <=>  mod(j*h, p) != 0  <=>  (by euclidConsequence, since
  mod(h,p)!=0) mod(j, p) != 0.
- So `j*h` coprime to Pbar  <=>  `j` coprime to Pbar  <=>  `j in residues`.
- Hence |removed| = |{j in [0,M) : j coprime to Pbar}| = |residues|.

This reduces the h-multiple-coprime count to the residue count via per-prime euclidConsequence —
no bijection/existence/uniqueness needed. The remaining bridge is connecting the LIST
`filterList(expandResidues(...), h)` to this value-domain count (the "expanded == coprime values
in [0, h*M)" characterization as a size fact). That bridge is Phase 2's main work.

### Checkpoint (2026-07-09)

Euclid foundation DELIVERED and green (11655/0/0). Phase 2 (density counting + A2 + closed form)
is a fresh intricate sub-effort. Pausing here to confirm scope before continuing — the verified
Euclid lemma is a meaningful standalone result that unblocks multiple downstream proofs
(primorial-not-divisible-by-new-prime, the 1/head uniformity, and the closed form).

## Deep audit of div/mod lemma surface (2026-07-09) — done before Phase 2

Exhaustive re-read of all div/mod + coprimality lemmas (per `<search-primacy>` rule, which I
should have done before E1-E5). Findings:

**Reinventions (minor, keep):**
- E1 `assertDivModReconstruct` — NO named `.holds` existed for `div*b+mod==a` (only DivMod's
  constructor require + solve.ensuring). Fills a real gap; arguably belongs in ch2 not ch5.
- E2 `assertRemainderLessThanDivisor` — fact free from Calc.mod.ensuring; thin wrapper, ok.
- E3 — could simplify to a direct `Prime.noDivisorInRangeExcludesValue` call (already used internally).

**Missed existing lemmas (use in Phase 2, don't reinvent):**
- **`SieveUtils.assertDivTransitive(c,b,a)`** (SieveUtils.scala:227): `a|b ∧ b|c ⟹ a|c`. NAMED public
  lemma — I had incorrectly claimed transitivity only existed inlined. Use for divisibility chaining.
- `ConsecutiveIntegers.densityForPrimeList` / `densityPreservedAfterFiltering` / `countModZeroEqualsM`:
  the interval-density scaffolding. Confirmed they're consistency-checks on assumed counts (the
  intersection "div by both p1,p2 ⟺ div by p1*p2" is comment-only, unproven) — BUT they exist and
  are the right scaffolding. Phase 2's job is the list-vs-interval bridge.
- `SieveUtils.assertExpandResiduesSize` (A1, banked): gives `|expanded| = |residues|*h` directly.

**Confirmed novel (no prior art):**
- `euclidConsequence` is genuinely new; it's what unblocks `h ∤ product(tailPrimes)` (no prior lemma
  established coprime-to-product, only coprime-to-each-prime via `primeIsCoprimeWithSmallerList`).

**OBJECTS.md gaps to fix later:** add EuclidLemma as section 5.7; catalog `assertDivTransitive` and
`assertMultiplePreservesDivisible` in 6.4 (currently missing).

### Phase 2 A2 strategy (post-audit)

Two candidate shapes for `|filterList(expandResidues(residues,M,h), h)| = |residues|*(h-1)`:

- **(S1) Per-block recursive count** over expandSingleResidue's block structure: count elements
  divisible by h in each addOffset block, sum. Needs per-block "count of r+i*M divisible by h" —
  not obviously uniform per block.

- **(S2) Value-domain count**: expanded == {coprime values in [0,h*M)} as a SIZE fact (needs
  completeness proof), then removed = |{v=j*h : j coprime to Pbar}| = |residues| via euclidConsequence.
  Cleaner math; harder bridge (completeness of expanded as a count).

S2 is mathematically cleaner; S1 matches the existing list structure better. Decision pending.

### A2 exploration result (2026-07-09): both S1 and S2 route through ONE crux

Read the actual structure of assertExpandResiduesSize (the verified A1 recursion), assertExpandedCoprime
(S2 soundness), assertResiduesComplete (S2 one-period completeness). Finding:

- **S1** (per-block count, mirrors A1's `expandSingleResidue` induction): recursion shape is proven
  to work, BUT per-block content ("how many r satisfy mod(r+i*M, h)==0 for fixed i") is non-uniform
  across blocks. Getting the total |removed|=|residues| needs the per-residue bijection
  (for each r, exactly one i in [0,h) makes mod(r+i*M,h)==0).
- **S2** (value-domain): soundness (assertExpandedCoprime) + one-period completeness
  (assertResiduesComplete) exist, but lifting to "expanded as a counted set = coprime values in
  [0,h*M)" still needs the bijection to convert "h-multiples that are coprime" into "residues".

**Both converge on the SAME crux: the CRT/permutation fact**
`gcd(h, M) = 1  ==>  for each r, the map i -> mod(r + i*M, h) hits 0 exactly once for i in [0,h)`.
Two halves:
- **Uniqueness**: two i's working => h | (i1-i2)*M => (gcd=1) h | (i1-i2) => i1==i2.
- **Existence**: surjectivity of i -> mod(i*M, h).

So `euclidConsequence` (verified) is NECESSARY but NOT SUFFICIENT. Also needed:
1. `gcd(h, M) = 1` for `M = product(tailPrimes)` -- needs Euclid applied to the PRODUCT
   (h prime, h > each tail prime => h does not divide product). This is the "h ∤ product(tailPrimes)"
   fact the audit confirmed is missing. Build from euclidConsequence + primeIsCoprimeWithSmallerList.
2. Existence + uniqueness of the modular solution (the CRT halves).
3. Counting composition (sum over blocks / set-size).

**Honest assessment:** Euclid foundation is solid and banked. A2 is real work with an identifiable
but nontrivial path -- a product-coprimality lemma + existence + uniqueness + counting composition.
Risk of a composition timeout (as E6 showed) at the assembly step. Each individual link is likely
verifiable; the composition is the unknown.

## Stage 1 BLOCKED — contrapositive wall (2026-07-09), 3 timeouts, STOPPED

Attempted `assertPrimeNotDivideProduct` (h does not divide product of smaller primes) — stage 1
of the A2 chain. The math routes through euclidConsequence's CONTRAPOSITIVE:

  mod(head,h)!=0 && mod(tailProduct,h)!=0  ==>  mod(head*tailProduct, h)!=0

which is exactly the E6 contrapositive that already timed out 3x. Three attempts on
assertPrimeNotDivideProduct, all timed out:
1. euclidConsequence called directly inside the recursive if/else contradiction.
2. Extracted flat `assertPeelDividesTail` helper (verifies 12/12 in isolation), called inside the
   recursive if/else. Timed out on the helper's precondition discharge inside the recursive context.
3. Restructured to avoid if/else, asserting the peel step then stating the postcondition as the
   negation. FAILS TO COMPILE/VERIFY: calling assertPeelDividesTail requires its precondition
   mod(head*tailProduct,h)==0, which is exactly what we're proving is FALSE -- the contrapositive
   cannot be obtained by calling the implication.

**Root cause (now definitive):** Stainless does not derive contrapositives from verified
implications within one VC. `euclidConsequence` (p|k*h ∧ p∤k ⟹ p|h) is verified, but every
downstream use that needs the reverse direction (p∤k ∧ p∤h ⟹ p∤k*h) -- E6, stage 1, and by
extension A2's CRT step -- hits the same wall. This is NOT solver weakness on a single lemma; it's
a structural limitation: the contrapositive must be proved DIRECTLY (its own induction), not derived.

`assertPeelDividesTail` (the flat implication form) is verified 12/12 and KEPT. The recursive
`assertPrimeNotDivideProduct` is parked as a draft comment.

**Full verify green: 11667/0/0** (+12 for assertPeelDividesTail over the 11655 Euclid baseline).

### Verified this session (banked, green):
- EuclidLemma object: E1-E5, euclidConsequence, assertPeelDividesTail. Full 11667/0/0.
- SieveUtils: assertAddOffsetSize, assertAppendSize, assertExpandSingleResidueSize,
  assertExpandResiduesSize (the A1 expansion-size half).

### What A2 needs that we DON'T have:
- A DIRECT (non-contrapositive) proof of "p∤k ∧ p∤h ⟹ p∤k*h". This is E6 done as its own
  well-founded induction (not derived from euclidConsequence). The minimal-counterexample
  structure for the contrapositive: assume mod(k*h,p)==0, derive mod(k,p)==0 OR mod(h,p)==0.
  euclidLemmaPrime ALMOST does this but concludes mod(b,p)==0 only in the non-trivial branch
  (it returns `true` vacuously when mod(a,p)==0). Refactoring euclidLemmaPrime to conclude the
  disjunction directly (rather than vacuously) may yield the contrapositive as a corollary.

### Options for the user:
1. **Refactor euclidLemmaPrime** to conclude `mod(a,p)==0 || mod(b,p)==0` (disjunction) instead of
   vacuously returning true in the mod(a,p)==0 branch. Then the contrapositive
   (mod(a,p)!=0 && mod(h,p)... ) follows as a direct case-split, not a derived contrapositive.
   This is the most promising untried angle -- changes E5's conclusion shape.
2. **Accept the Euclid-only deliverable** (euclidConsequence is the verified result; the closed form
   remains blocked on the contrapositive). Document honestly in the article.
3. **Axiomatize the contrapositive** (like Bertrand in §8) to unblock A2, with the Euclid proof as
   strong justification.

## UPDATE (2026-07-09): disjunction refactor attempted, contrapositive STILL walls (5 total)

Per user decision, refactored `euclidLemmaPrime` (E5) to conclude the DISJUNCTION
`mod(a,p)==0 || mod(b,p)==0` instead of returning `true` vacuously in the `mod(a,p)==0` branch.
**The refactor itself verified** (E5: 50/50; euclidConsequence updated to thread the disjunction:
38/38). This is strictly stronger than before -- the disjunction is a usable boolean value.

Then attempted `euclidContrapositive` (p∤k ∧ p∤h ⟹ p∤k·h) as a DIRECT case-split on the disjunction.
**5 presentations, ALL timed out at 300s:**
1. Call euclidLemmaPrime unconditionally (fails: can't assert its mod==0 premise -- that's the conclusion).
2. if(mod==0){call euclidLemmaPrime; assert disjunction false; false} else {true}; bare postcondition.
3. .ensuring postcondition instead of bare expression.
4. (earlier) combined form; (earlier) split wrapper.

**Definitive finding:** the contrapositive of Euclid's lemma is beyond this Stainless/Z3 setup
(300s/VC) regardless of presentation -- combined, split, conditional, .ensuring, or via disjunction
case-split. This is NOT presentation fixable; it's a solver-capability wall on this specific fact.

**Banked (green, 11685/0/0):**
- E1-E5 (E5 now disjunction form), euclidConsequence, assertPeelDividesTail.
- SieveUtils A1 expansion-size lemmas.

**The closed form |G'| = |G|·(h-1) remains blocked** on the contrapositive. euclidConsequence
(the implication p|k*h ∧ p∤k ⟹ p|h) IS verified and unblocks primorial-not-divisible-by-new-prime,
but A2's "1/head" step needs the reverse direction, which walls.

### Remaining options (all previously offered):
1. Axiomatize the contrapositive (like §8 Bertrand) -- justified by the verified euclidConsequence
   (logically equivalent), unblocks A2 + closed form, adds one undischarged assumption.
2. Accept Euclid-only deliverable; document the closed form as pending on a stronger solver / SMT
   tactic (e.g. a nonlinear-arithmetic extension or a hand Bézout witness).
3. Try a fundamentally different proof of the contrapositive (e.g. via explicit Bézout coefficients
   a*x + p*y = 1, which gives k*h*(a*x+p*y) = k*h, reducing divisibility -- but this needs the
   extended Euclidean algorithm, a large separate effort, Route A).

## ROUTE A SUCCESS (2026-07-09): Bézout theory breaks the contrapositive wall

User chose Route A (full Bézout theory). **It worked.** The contrapositive is VERIFIED via a direct
linear-combination proof, not a derived implication. Full verify **11966/0/0** (+281 over 11685).

New object `BezoutUtils` (`src/main/scala/v1/chapter5/prime/BezoutUtils.scala`), all green:
- `case class Bezout(a,b,g,x,y)` -- witness record (invariant a*x + b*y == g).
- `subtractiveGcd(a,b)` -- gcd via subtraction (decreases on a+b). 10/10.
- `extendedGcd(a,b): Bezout` -- the witness (g, x, y) with a*x+b*y==g. **13/13 first attempt**
  (the subtractive form's clean algebra + Bezout case-class invariant made the hardest lemma easy).
- `assertBezoutIdentity` -- a*x+b*y==g exposed. 3/3.
- `assertGcdDividesBoth` -- g divides both a and b (needed modAdd explicitly; 67/67).
- `assertCoprimeGcdOne` -- coprime + prime => g==1 (case-split via noDivisorInRangeExcludesValue; 36/36).
- `assertCoprimeLinearCombinationOne` -- h*x + p*y == 1. 16/16.
- `assertDivTimesAnyIsDiv` -- sign-agnostic "p|m => p|m*c" (for negative Bézout coeffs). 18/18.
- `assertPrimeDivProductImpliesDivFactor` (B7) -- **THE DIRECT PROOF**: isPrime(p), 0<h<p, p∤h,
  p|k*h => p|k. Via k = k*h*x + k*p*y, p|k*h => p|k*h*x, p|k*p*y, so p|k. 41/41.
- `assertPrimeDivKhImpliesDivK` -- implication wrapper (h-reduction + B7). 28/28.
- `assertPrimeProductNotDivisible` (B8) -- **THE CONTRAPOSITIVE**: isPrime(p), p∤k, p∤h => p∤k*h.
  Via h-reduction + inline B7 in the contradiction branch + .ensuring postcondition. 31/31.

The key that broke the wall: B7 proves `p|k*h => p|k` DIRECTLY from the Bézout linear combination
(k = k*h*x + k*p*y), so the contrapositive is reached by contradiction with a concrete divisibility
chain -- NOT by deriving a contrapositive from an implication (which Stainless cannot do).

In `EuclidLemma.scala`, added `assertTwoFactorsProductNotDiv` (lightweight two-factor step via B7,
18/18) -- the non-recursive building block for stage 1.

## Stage 1 composition snag (2026-07-09): 3 timeouts, NOT a math wall

`assertPrimeNotDivideProduct` (h does not divide product of smaller primes) -- the stage-1 induction
-- times out at the recursive COMPOSITION, not at the math:
- Base case (product([])==1, mod(1,h)!=0): fine.
- Two-factor step (assertTwoFactorsProductNotDiv): verified standalone 18/18.
- The timeout is connecting the IH conclusion `mod(product(tail), h) != 0` to the wrapper's
  precondition on the local `tailProduct` val, within the recursive VC.

3 attempts (direct B8 call, named binding, B7-in-contradiction-branch) all timed out at this
composition step. Commented out as draft; full verify green 11966/0/0.

**This is a different kind of problem than the contrapositive wall.** The math is sound and every
piece is verified; it's a recursive-precondition-discharge / solver-visibility issue (LEARNINGS §1.2
family). Likely fixable by restructuring the recursion (e.g. make the IH conclusion match the
wrapper precondition exactly, or inline the two-factor step differently, or carry the mod as a
return value). The contrapositive itself is no longer the blocker.

### Options for stage 1:
1. Restructure the recursion so the IH feeds the wrapper cleanly (e.g. return the mod value, or
   prove a specialized "mod(product(tail),h)!=0 holds" form). Genuinely different structure -- not
   a 4th identical attempt.
2. Accept the contrapositive deliverable (B8 verified); treat stage 1 / A2 as the next session's
   work with the wall now removed. Update the article: Euclid + contrapositive verified, closed form
   pending on the (now-ordinary) stage-1 composition.
3. Bypass stage 1: A2 may not strictly need product-non-divisibility -- it needs the per-prime
   contrapositive (B8 directly), not the product form. Re-examine whether A2 can use B8 per-prime
   instead of via the product.
