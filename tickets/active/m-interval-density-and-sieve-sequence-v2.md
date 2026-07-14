# M-Interval Density and Sieve Sequence V2 Article Repair

**Created:** 2026-07-11
**Status:** Planning
**Owner:** article and proof follow-up for `articles/chapter6/sieve-sequence-v2.md`

## Goal

Fix the mathematical framing in `articles/chapter6/sieve-sequence-v2.md` and then attempt the narrow proof that, over one complete current modulus interval, filtering by the current head removes exactly one lifted value per current survivor.

The central theorem should be stated over the current full `M` interval, not as a vague global density claim:

```text
For each current survivor residue r in one M-period, the expanded values
r + i * M for 0 <= i < h cover every residue class modulo h exactly once.
Therefore exactly one lift is divisible by h.
```

If verified, this gives the size step:

```text
|nextFiltered| = |residues| * (h - 1)
```

and can later be composed with a separate cardinality bridge if we still want:

```text
|G'| = |G| * (h - 1)
```

## Current State

- Baseline log is green: `logs/verify.log` reports `12002 valid`, `0 invalid`, `0 unknown`.
- `articles/chapter6/sieve-sequence-v2.md` already defines the current stage over the full interval `[h, h + M)`, where `M = product(Pbar)`.
- The article has interval/framing issues:
  - Section 4.2 says `[h, h * M)`, which likely mixes current-period `[h, h + M)` with expanded next-period length `h * M`.
  - Section 7.3 says filtering removes "every h-th value" and "one per block of h" from the expanded list. That wording is risky because `nextExpanded` is not raw consecutive integers; it is lifted survivor residues.
  - Section 8 claims only Bertrand remains and that no Euclid requirement remains. Current proof notes say that is optimistic: product/coprimality or CRT-style support is still open for the closed-form count.
- `SieveUtils.assertExpandResiduesSize` is already verified and gives the expansion size:
  `expandResidues(residues, M, h).size == residues.size * h`.
- `SieveUtils.assertResiduesComplete` gives one-period containment for coprime values, but does not by itself prove a counted set equality.

## Expected State

1. The article clearly distinguishes:
   - current interval: `[h, h + M)`;
   - expanded next interval: length `h * M`;
   - exact full-period density: one removed lift per current survivor residue.
2. Any unverified size formula is labeled as pending or draft, not presented as verified.
3. A proof attempt starts from the smallest useful lemma, not the whole closed form.
4. If the proof succeeds, update `OBJECTS.md` and then update the article with all three required representations.

## Similar Tickets and Prior Work

- `tickets/active/next-gaps-size-closed-form.md`
  - Prior active proof ticket for `|G'| = |G| * (h - 1)`.
  - Banked `assertExpandResiduesSize`.
  - Records that A2 is the hard step and that previous product-composition attempts timed out.
  - Also records the newer open option: bypass product composition by using per-prime B8 directly.
- `tickets/active/sieve-sequence-article-rewrite.md`
  - Article rewrite guidance: match `PROOF_GUIDE.md`, avoid overclaiming, check every cited source name.
- `docs/proof-dependencies.md`
  - Records that `sieve-sequence-v2.md` is optimistic about "only Bertrand" and that the size closed form still needs list/count or CRT support.
- `tickets/active/sieve-property-landscape.md`
  - Useful distinction: CRT uniformity is exact over full periods; trouble starts in partial windows. This ticket deliberately stays in the full `M` interval.

## Plan

### Phase 1: Article Repair

Keep this markdown-only and do not claim new verification.

1. Fix interval language:
   - Use `[h, h + M)` for the current stage period.
   - Use length `h * M` for the expanded next-stage construction.
2. Replace "every h-th value" with the exact lifted-residue statement:

   ```text
   For each survivor residue r, the h lifts r + i * M cover all residue
   classes modulo h when M is coprime to h, so exactly one lift is removed.
   ```

3. Mark the closed-form size theorem as pending until the Stainless lemma exists.
4. Fix Section 8 so it does not claim that Bertrand is the only remaining external requirement for the whole article if the size theorem still depends on unverified density/counting support.
5. Do not reference tickets in the article. State the boundary directly.

### Phase 2: Proof Attempt, Narrow First Lemma

Before any code change:

1. Confirm green baseline with `grep "total:" logs/verify.log`; run `just verify` only if the log is stale or after a code change.
2. Search existing `.holds` lemmas in:
   - `SieveUtils`
   - `SieveSequenceNextLevel`
   - `SpecCycleSieveEquivalence`
   - `CoprimeUtils`
   - `EuclidLemma`
   - `ConsecutiveIntegers`
   - `SortedList`

Target the smallest proof first:

```text
For fixed r, M, h, if gcd(M, h) = 1 or equivalent coprimality facts are required,
then among r + i * M for 0 <= i < h there is exactly one value divisible by h.
```

Preferred shape:

```text
exists unique i in [0, h) such that Calc.mod(r + i * M, h) == 0
```

This is the direct `M`-interval density kernel.

### Phase 3: Lift to Expansion Count

Only after Phase 2 is green:

1. Prove a block/list bridge for `expandSingleResidue`:

   ```text
   filterList(expandSingleResidue(residues, M, h, 0), h)
   removes exactly one lift per residue.
   ```

2. Keep the proof local to `expandSingleResidue` if possible, because A1 already verifies by induction on that structure.
3. Avoid proving equality of two separately built lists unless necessary; prefer size/count lemmas.

### Phase 4: Composition

Only after Phase 3 is green:

1. Compose with `assertExpandResiduesSize`.
2. Prove:

   ```text
   filterList(expandResidues(residues, M, h), h).size ==
     residues.size * (h - 1)
   ```

3. Decide whether to attempt the separate bridge `residues.size == G.size`.

## Proof Drafts

These are sketches to guide execution, not claims of verified status. Before using any cited helper, re-read the current source body and check its exact postcondition.

### Draft A: Modular Permutation Kernel

Prove the mathematical core directly:

```text
given M > 0, h > 1, 0 <= r < M, and M coprime to h,
there exists exactly one i with 0 <= i < h such that
Calc.mod(r + i * M, h) == 0.
```

Suggested split:

1. Existence: find or construct the zero offset in the sequence `r + i * M`.
2. Uniqueness: if two offsets `i` and `j` both work, then `h` divides `(i - j) * M`; since `M` is coprime to `h`, `h` divides `i - j`; bounded offsets force `i == j`.
3. Only after existence and uniqueness are separate and green, expose a wrapper for "exactly one removed lift".

Why this draft is attractive: it is the cleanest statement of the full `M`-interval density fact.

Risk: existence may require modular inverse or a stronger permutation lemma than the current code has.

### Draft B: Survivor-Lift Count by Structural Recursion

Avoid a global set statement and follow the shape of `expandSingleResidue`.

```text
countRemoved(expandSingleResidue(residues, M, h, 0), h) == residues.size
```

Suggested split:

1. Define or reuse a count helper for values removed by `filterList`.
2. Prove the one-residue version: the list `[r, r + M, ..., r + (h - 1) * M]` has exactly one value divisible by `h`.
3. Lift over `residues` by structural recursion, adding one removed value per head residue.

Why this draft is attractive: it matches the verified `assertExpandResiduesSize` recursion and may avoid proving equality between two separately built lists.

Risk: the current `expandSingleResidue` is block-major (`addOffset(residues, i * M)` for each `i`), while the one-residue proof is residue-major. Bridging those orders may become a list-permutation/count problem.

### Draft C: Value-Domain Count of Removed Multiples

Reframe removed values as `h * j` values in `[0, h * M)`:

```text
removed == { h * j | 0 <= j < M and isCoprime(j, Pbar) }
```

Suggested split:

1. Prove pointwise coprime preservation for the current head:

   ```text
   isCoprime(j * h, Pbar) == isCoprime(j, Pbar)
   ```

   using the per-prime product-not-divisible lemma if available, or B8-style reasoning per prime.
2. Use `assertResiduesComplete` only after checking whether it supplies the exact membership direction needed.
3. Prove a count equality between coprime `j` values and `residues.size`.

Why this draft is attractive: it avoids saying "every h-th value" in the expanded list and expresses the math as the set identity `removed = h * R`.

Risk: it still needs a bridge from `filterList(expandResidues(...), h)` to the value-domain removed set, and that bridge may be as hard as the permutation kernel.

### Draft D: Article-First Mathematical Proof

Before code, write the article proof in a clearly pending form:

```text
For each current residue r, the next stage includes h lifted candidates
r + i * M. Since M is coprime to h, stepping by M permutes residues modulo h.
Therefore exactly one lift is congruent to 0 modulo h and is removed.
```

Use this as the north star for code, but mark the Stainless verification as pending until a `.holds` lemma exists.

Why this draft is attractive: it fixes the reader-facing math immediately and prevents the article from overclaiming.

Risk: article clarity can make the proof look easier than the current list representation actually is. Keep the pending label until code verifies.

### Recommended Execution Order

1. Article wording first, because it is markdown-only and removes the misleading framing.
2. Draft A as the first code micro-goal if a suitable modular-inverse/permutation helper exists or can be introduced narrowly.
3. If Draft A stalls on existence, try Draft B's structural count route.
4. If both routes ask for the same missing bridge, stop and record the precise missing lemma instead of trying variants.

## Plan Evaluation: Concerns and Alternatives

### Overall Assessment

The proposed density theorem is a valid route to the sieve-size step, but the current plan
compresses three independent obligations into the phrase "one removed lift per survivor":

1. **Arithmetic kernel:** for each residue `r`, exactly one `i` in `[0, h)` satisfies
   `Calc.mod(r + i * M, h) == 0`.
2. **Stage precondition:** the current sieve state must establish that `M` and `h` are
   coprime. Since `h` is prime, the code can use the equivalent condition
   `Calc.mod(M, h) != 0`, but that condition still has to come from the stage invariants.
3. **List/count bridge:** the block-major list produced by `expandSingleResidue` must be
   counted as though candidates were grouped by survivor residue.

The route proves `nextFiltered.size == residues.size * (h - 1)` only after all three are
verified. The final gap-cycle formula additionally needs the already separate bridges from
filtered values to gaps and from `residues.size` to the current gap-cycle size.

### Points of Concern

#### 1. Draft A assumes the hardest stage fact

Draft A states `M` coprime to `h` as a precondition. In the actual sieve, `M` is a product of
the previous primes. The current source has a verified two-factor non-divisibility lemma
(`BezoutUtils.assertPrimeProductNotDivisible`), but the prior n-factor composition over a list
timed out. Therefore proving the conditional modular kernel does not by itself close the sieve
theorem.

**Impact:** high. The ticket should distinguish "conditional density kernel verified" from
"sieve stage discharges the kernel precondition".

#### 2. Existing consecutive-integer lemmas do not directly apply

`ConsecutiveIntegers.findZeroOffset` and `atMostOneZero` concern `n + i`, not `r + i * M`.
Using them requires a verified reindexing/permutation or modular-inverse lemma. They are useful
endpoints after reindexing, not direct proofs of Draft A.

**Impact:** medium. Name similarity could lead to an invalid or solver-expensive proof plan.

#### 3. Draft B follows the wrong recursion axis

`expandSingleResidue` is block-major:

```text
addOffset(residues, 0 * M) ++ ... ++ addOffset(residues, (h - 1) * M)
```

The mathematical argument is residue-major:

```text
for each r: [r, r + M, ..., r + (h - 1) * M]
```

Induction over `expandSingleResidue` naturally proves facts per lift index, where the number
removed from one block is not uniform. Structural recursion alone does not remove the need for
an order-insensitive count/transpose argument.

**Impact:** high. Draft B should not be the fallback unless a count-fold bridge is designed first.

#### 4. Draft C may duplicate an existing representation theorem without a cardinality theorem

`SpecCycleSieveEquivalence.assertExpandedResiduesRepresentPeriod` already supplies the important
membership/completeness direction for expanded values. However, membership equivalence does not
imply equal list sizes unless duplicate-freedom or an explicit bijection is also proved. The
value-domain route can therefore move the difficulty into a hidden set-to-list cardinality lemma.

**Impact:** high. Reuse the representation theorem, but do not treat it as a count bridge.

#### 5. "Density" can obscure what is actually exact

The theorem is not an asymptotic or probabilistic density statement. It is an exact finite
cardinality result over `h` lifts of each residue. Calling it density is acceptable exposition,
but proof names and postconditions should use "unique divisible lift" or "filtered lift count".

**Impact:** low mathematically, medium editorially.

#### 6. Article-first needs a narrow boundary

Factual interval corrections and explicit pending labels are safe before the proof. Adding the
full three-representation property section before a verified `.holds` function would conflict
with the project's publication rules unless the Scala form is clearly marked as an unverified
draft. The article edit should not get ahead of the proof status.

**Impact:** medium. Repair framing first; publish the completed property only after verification.

#### 7. The final theorem boundary must remain explicit

Even a successful proof of
`nextFiltered.size == residues.size * (h - 1)` does not automatically establish
`nextGaps.size == currentGaps.size * (h - 1)`. The plan mentions the residue/gap bridge, but it
should be a named acceptance boundary rather than a late optional decision.

**Impact:** high for claims in the article, low for the usefulness of the density lemma itself.

### Proposed Alternatives

#### Alternative 1: Conditional Kernel First

Prove the smallest theorem under the condition already used by the sieve proof surface:

```text
isPrime(h) && Calc.mod(M, h) != 0
  ==> exists unique i in [0, h) with Calc.mod(r + i * M, h) == 0
```

Then treat `Calc.mod(M, h) != 0` as a separate stage theorem. This prevents the product-of-primes
composition problem from being mixed into modular-permutation VCs and still yields a reusable
result if the sieve keeps the condition as an explicit invariant.

**Recommendation:** preferred arithmetic route.

#### Alternative 2: Bezout Witness for the Offset

Given a verified coprimality witness for `M` and `h`, use Bézout coefficients to construct a
modular inverse of `M`, then define the offset from `-r * inverse(M)`. This gives existence by
construction. Use the same inverse or B7/B8 divisibility facts for uniqueness.

This is more explicit than a general permutation theorem and fits the verified `BezoutUtils`
foundation. The main risk is normalizing negative coefficients into `[0, h)` using `Calc.mod`
without creating expensive sign arithmetic.

#### Alternative 3: Predicate Count Fold, Not List Transposition

Introduce or reuse a recursive count of values divisible by `h`, with two generic properties:

```text
countDivisible(xs ++ ys, h) == countDivisible(xs, h) + countDivisible(ys, h)
filterList(xs, h).size == xs.size - countDivisible(xs, h)
```

Then prove an order-insensitive fold theorem for the conceptual matrix
`candidate(r, i) = r + i * M`. The theorem should equate the total count obtained by folding
blocks with the total count obtained by folding residues, without proving equality of the two
list orders. Once each residue contributes one, the total removed count is `residues.size`.

**Recommendation:** preferred list/count route if the necessary append/count lemmas stay small.

#### Alternative 4: Conditional Size Theorem as a Useful Deliverable

If discharging `Calc.mod(M, h) != 0` from `AllPrimesSoFarList` remains expensive, verify:

```text
Calc.mod(M, h) != 0
  ==> filterList(expandResidues(residues, M, h), h).size
        == residues.size * (h - 1)
```

This is not the unconditional sieve-size theorem, but it matches the explicit product
non-divisibility precondition already carried by parts of the current derived sequence. It would
separate a general combinatorial theorem from the prime-prefix invariant that instantiates it.

#### Alternative 5: Value-Domain Route Only If Count Infrastructure Already Exists

Reuse `assertExpandedResiduesRepresentPeriod` and characterize removed values as `h * j`, but
proceed only after finding or proving narrowly scoped no-duplicate/cardinality lemmas. Without
that infrastructure, this route should remain a mathematical explanation rather than the first
Stainless implementation attempt.

### Revised Recommended Order

1. Repair only factual interval wording and pending-status language in the article.
2. Search for a reusable predicate-count/append lemma and for a current caller-visible way to
   obtain `Calc.mod(M, h) != 0`; read their bodies before choosing the proof file.
3. Prove the conditional arithmetic kernel, preferably by a Bézout-derived inverse.
4. Prove the count-fold bridge independently of sieve-stage invariants.
5. Compose them into the conditional filtered-size theorem.
6. Separately attempt to discharge `Calc.mod(M, h) != 0` from `AllPrimesSoFarList` or preserve it
   honestly as an explicit precondition.
7. Only then connect `residues.size` to the current gap-cycle size and promote the article claim.

### Stop Conditions

- If modular-inverse normalization needs more than three failed presentations, stop and record
  the missing signed-modulo helper.
- If the count-fold proof requires proving full list transposition or extensional list equality,
  stop and reassess the representation rather than broadening the ticket silently.
- If the product non-divisibility composition repeats the prior recursive IH-precondition timeout,
  do not retry it inside this ticket; keep the conditional theorem as the deliverable.

## Risks

- The mathematical statement is simple over a full period, but Stainless may still need explicit existence and uniqueness lemmas for the modular permutation.
- Product-coprimality (`Calc.mod(product(Pbar), h) != 0`) has prior timeout history. Prefer a per-prime route if it avoids the product bridge.
- The article must not imply the closed form is verified until a `.holds` function exists.
- Avoid modifying `MemCycle`, `ModCycle`, or `CycleIntegral`.

## Validation

For article-only edits:

1. No `just verify` required if only markdown changes.
2. Check that the article contains no ticket references.
3. Check that any pending proof is clearly labeled as pending.
4. Check that every verified claim cites a real current source function.

For code proof work:

1. Start from green.
2. One lemma or assertion per change.
3. After each code change, run focused verification first.
4. Run full `just verify` after focused verification succeeds.
5. Stop after 3 failed attempts on the same micro-goal.
6. Update `OBJECTS.md` only after verification succeeds.
7. Update the article only after verification succeeds, unless the article text explicitly marks the theorem as pending.

## START HERE

1. Read `articles/chapter6/sieve-sequence-v2.md` Sections 2, 4.2, 7.1, 7.3, and 8.
2. Make the markdown-only interval/framing fixes first.
3. Search existing lemmas before drafting any new proof.
4. If starting code, first target the unique removed lift lemma for a fixed `r`.

## Progress Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-11 | Created ticket after rereading `AGENTS.md`, `LEARNINGS.md`, `PROOF_GUIDE.md`, `docs/architecture.md`, existing proof tickets, and current `sieve-sequence-v2.md` interval claims. The key reframing is that we only need full `M`-interval density: one removed lift per current survivor residue. | Start with article repair. |
| 2026-07-11 | Added proof drafts for the execution phase. Treat prior ticket notes as hypotheses, not authority; each helper claim must be checked against current source before use. | Use Draft A as the preferred first proof micro-goal, with Draft B/C as alternatives. |
| 2026-07-11 | Critical review found three separate obligations: conditional modular uniqueness, discharge of `Calc.mod(M, h) != 0`, and a block-major to residue-major count bridge. Existing consecutive-integer lemmas and expanded-period membership do not close those bridges directly. | Prefer a conditional Bézout-based kernel plus an order-insensitive predicate-count fold. Keep product composition and the residue-to-gap size bridge as explicit later boundaries. |
| 2026-07-11 | Repaired the article framing without changing code: Section 4.2 now uses the current period `[h, h + M)`, Section 7.1 describes lifted residues over length `h * M`, Section 7.3 marks the closed-form count as pending, and Sections 8-9 no longer claim Bertrand is the only remaining obligation. | Search existing lemmas before drafting the first proof micro-goal. |
| 2026-07-11 | Read `CONTRIBUTING.md`. First code attempt added a conditional helper `assertCoprimeStepNonzeroAfterZero`, but focused verification timed out on the assertion calling `BezoutUtils.assertPrimeProductNotDivisible(d, step, p)` (`28 valid`, `1 unknown`). The change was reverted and full verification returned green (`12002 valid`, `0 unknown`). | Before another proof edit, use `just verify-debug` on the failing/timing-out helper shape or choose a lighter helper that avoids unfolding the Bézout product lemma in the caller. |
| 2026-07-11 | Workflow clarification from the user: if a source change is fully reverted and `git diff` shows the code is exactly back to the prior green state, do not spend another full verification run just to reconfirm the same code. | For future failed code attempts, verify the failed focused run, revert exactly, confirm the relevant source diff is empty, and continue from the previous green baseline without an extra full run unless a non-reverted source diff remains. |
| 2026-07-11 | User reminder: before designing new lemmas, study how existing verified lemmas actually work, not just their statements. Their proof structure, precondition shape, recursion axis, and helper-call placement are evidence for what Stainless accepts. | For the next proof attempt, inspect successful nearby lemmas in full and model the new lemma's shape on those patterns before editing Scala. |
| 2026-07-11 | Second code attempt succeeded by following the existing lemma-call pattern: call `.ensuring` helpers directly instead of wrapping them in `assert(helper(...))`. `assertCoprimeStepNonzeroAfterZero` passed focused verification (`28 valid`, `0 unknown`) and full verification (`12030 valid`, `0 invalid`, `0 unknown`). | Treat this as the first verified arithmetic brick for the unique-lift route: if `a` is divisible by prime `p`, `step` is coprime to `p`, and `0 < d < p`, then `a + d * step` is not divisible by `p`. |
| 2026-07-11 | Updated `OBJECTS.md` after verification to add the missing `BezoutUtils` subsection and record the new lemma. The catalog totals were already stale relative to the listed chapter rows, so this update added the verified entries without attempting a broad recount. | Next proof micro-goal can build an at-most-one-zero offset lemma for `r + i * M` and `r + j * M`, reusing the new arithmetic brick and existing consecutive-integer proof shapes. |
| 2026-07-11 | Added the ordered offset helper `assertCoprimeStepOrderedNonzeroAfterZero`. It mirrors `ConsecutiveIntegers.atMostOneZero`: set `d = j - i`, prove `r + j*step == (r + i*step) + d*step`, then reuse `assertCoprimeStepNonzeroAfterZero`. Focused verification passed (`18 valid`, `0 unknown`) and full verification passed (`12048 valid`, `0 invalid`, `0 unknown`). | The next uniqueness micro-goal can be an unordered at-most-one lemma: if two offsets `i,j` in `[0,p)` both hit zero for `r + offset*step`, prove `i == j` by branching on order and calling the ordered helper. Existence and list-count remain separate obligations. |
| 2026-07-11 | Added the unordered uniqueness helper `assertCoprimeStepAtMostOneZero`, branching on `i < j` / `j < i` and reusing the ordered helper to discharge the contradictory branch. Focused verification passed (`27 valid`, `0 unknown`) and full verification passed (`12075 valid`, `0 invalid`, `0 unknown`). | The uniqueness half for a fixed residue and p-window is now verified. Next hard boundary is existence of one zero offset, likely via a Bezout/inverse construction or a carefully adapted `ConsecutiveIntegers.findZeroOffset` route; after that comes list/count bridging. |
| 2026-07-11 | User reminder: `LEARNINGS.md` has useful guidance too. Re-read relevant sections before the next proof choice: `.ensuring`/direct return facts for propagation, `modZeroPlusC` for zero-plus-offset modulo steps, avoid symbolic product-modulo proofs where possible, avoid Bertrand/Jacobsthal/prime-gap routes, and keep list completeness/counting separate from arithmetic facts. | Next existence attempt should start from this guidance and not jump directly to list/count lemmas. |
| 2026-07-11 | Ran `just test` after the green full verification per `LEARNINGS.md` workflow guidance. Result: `133` tests run, `131` succeeded, `2` failed in `v1.div.MainTest`. The failures compare CLI usage text: `src/main/scala/v1/Main.scala` now prints an extra `just show <steps> <count>` usage line, while `src/test/scala/v1/div/MainTest.scala` expects only the old one-line message. This is outside the touched proof files. | Do not treat the proof lemmas as red; verification remains green. If desired, fix the stale CLI tests in a separate small change/ticket. |
| 2026-07-11 | Route concern from user: avoid drifting into signed-number reasoning unless it is truly necessary. A draft complement-offset helper for the signed Bezout inverse route was removed before verification, returning the source to the last full-green proof shape. | Prefer a nonnegative-first existence plan next: either adapt `ConsecutiveIntegers.findZeroOffset` structurally to stepped offsets, or prove a bounded scan over offsets without introducing negative witnesses. |
| 2026-07-11 | User clarified that changing current code or lemma surfaces to accept negative values may affect many existing lemmas. This is a hard constraint for the existence proof route, not just a style preference. | Do not broaden existing arithmetic APIs or proof preconditions to negative domains for this ticket. Keep witnesses and helper lemmas nonnegative-first, and only rely on existing signed behavior if it is already exposed and does not require changing shared lemmas. |
| 2026-07-11 | Added nonnegative bridge lemma `assertSameResidueOffsetPreservesZero`: if `0 <= k < p`, `mod(i*step,p) == k`, and `r+k` is divisible by `p`, then `r+i*step` is divisible by `p`. Focused verification passed (`31 valid`, `0 unknown`) and full verification passed (`12106 valid`, `0 invalid`, `0 unknown`). | This keeps existence modular without negative witnesses: next we can separately seek a nonnegative `i` such that `mod(i*step,p)` equals the ordinary zero offset from `ConsecutiveIntegers.findZeroOffset(r,p)`. |
| 2026-07-11 | Added bridge lemma `assertSteppedOffsetFromOrdinaryZeroOffset`: if a nonnegative stepped offset `i` satisfies `mod(i*step,p) == findZeroOffset(r,p)`, then `r+i*step` is divisible by `p`. Focused verification passed (`19 valid`, `0 unknown`) and full verification passed (`12125 valid`, `0 invalid`, `0 unknown`). | The remaining arithmetic existence gap is now isolated: prove, without broadening APIs to negative domains, that a coprime nonnegative step permutes the residues modulo `p` or otherwise yields such an `i` in `[0,p)`. |
| 2026-07-11 | The inline residue-distinctness proof timed out as `unknown`, even after reshaping it using `AdditionAndMultiplication` and `CycleCheckMod` style. Splitting the transport part succeeded: `assertSameSteppedResiduePreservesZero` focused verification passed (`43 valid`, `0 unknown`) and full verification passed (`12168 valid`, `0 invalid`, `0 unknown`). | Use this helper as the next brick for residue distinctness: first transport zero from offset `i` to offset `j` under equal stepped residues, then call `assertCoprimeStepAtMostOneZero` to derive `i == j`. |
| 2026-07-11 | Added `assertCoprimeStepOrderedResiduesDistinct`. The reduced proof avoids `assert(false)`: it takes the zero offset for `i*step`, transports divisibility from `i` to `j` if stepped residues are equal, then uses `assertCoprimeStepAtMostOneZero` to derive `i == j`, contradicting `i < j`. Focused verification passed (`35 valid`, `0 unknown`) and full verification passed (`12203 valid`, `0 invalid`, `0 unknown`). | The distinctness/injectivity half of the stepped-residue permutation route is now verified for ordered offsets. Next choose the smallest nonnegative-first bridge toward existence, likely an unordered equality-to-index lemma or a bounded/permutation count lemma, before attempting list/count integration. |
| 2026-07-12 | Added `assertCoprimeStepResiduesEqualImpliesOffsetsEqual`, the unordered injectivity form: if `0 <= i,j < p` and `mod(i*step,p) == mod(j*step,p)`, then `i == j` when `step` is coprime to prime `p`. It branches on `i < j` / `j < i` and reuses the ordered distinctness lemma. Focused verification passed (`19 valid`, `0 unknown`) and full verification passed (`12222 valid`, `0 invalid`, `0 unknown`). | The injection fact is now available in the direct equality form needed for counting/permutation arguments. Next proof should still avoid negative witnesses and target the smallest existence/count bridge: either a bounded scan over stepped residues or a list-level finite-domain lemma that turns injectivity over `p` offsets into hitting every residue. |
| 2026-07-12 | Added `assertModRepresentativePreservesScaledResidue`: for any `raw`, nonnegative `scale`, and positive `p`, replacing `raw` by `mod(raw,p)` preserves the residue of the scaled value. The proof uses `DivMod.solve` reconstruction plus `ATimesBSameMod`. Focused verification passed (`27 valid`, `0 unknown`) and full verification passed (`12249 valid`, `0 invalid`, `0 unknown`). | This enables a nonnegative-first Bézout existence witness: use the signed Bézout coefficient only inside `raw = target*x`, then set the offset to `mod(raw,p)` and prove it hits the target residue without changing shared APIs to accept negative domains. |
| 2026-07-12 | Added `assertCoprimeStepHitsResidue`: for prime `p`, nonnegative `step` with `mod(step,p) != 0`, and target residue `0 <= target < p`, the witness `offset = mod(target*x,p)` from the Bezout inverse of `mod(step,p)` satisfies `0 <= offset < p` and `mod(offset*step,p) == target`. Focused verification passed (`59 valid`, `0 unknown`) and full verification passed (`12308 valid`, `0 invalid`, `0 unknown`). | The arithmetic existence half is now verified without broadening shared APIs to negative values. Next proof should expose this witness in the exact shape needed by `assertSteppedOffsetFromOrdinaryZeroOffset`, likely through a witness-returning helper or a dedicated zero-existence lemma for `r + offset*step`. |
| 2026-07-12 | Added `coprimeStepResidueOffset`, a witness-returning version of the coprime stepped-residue existence proof. It returns an offset in `[0,p)` and carries the postcondition `mod(offset*step,p) == target`. Focused verification passed (`59 valid`, `0 unknown`) and full verification passed (`12367 valid`, `0 invalid`, `0 unknown`). | Later lemmas can now call the producer and receive the concrete offset facts directly from `.ensuring`, matching the successful `ConsecutiveIntegers.findZeroOffset` style. Next smallest bridge is a fixed-`r` zero-existence lemma that chooses `target = findZeroOffset(r,p)` and feeds the returned offset into `assertSteppedOffsetFromOrdinaryZeroOffset`. |
| 2026-07-12 | Added `coprimeStepZeroOffset`: for fixed `r`, prime `p`, and nonnegative `step` with `mod(step,p) != 0`, it returns an offset in `[0,p)` such that `mod(r + offset*step,p) == 0`. The proof composes `findZeroOffset`, `coprimeStepResidueOffset`, and `assertSteppedOffsetFromOrdinaryZeroOffset`. Focused verification passed (`27 valid`, `0 unknown`) and full verification passed (`12394 valid`, `0 invalid`, `0 unknown`). | The fixed-residue existence half of "exactly one removed lift" is now verified in witness-returning form. The remaining arithmetic kernel is to package existence plus `assertCoprimeStepAtMostOneZero` into an exactly-one lemma for any two offsets in `[0,p)`. After that, the hard work shifts from arithmetic to list/count bridging over `expandSingleResidue` / `expandResidues`. |
| 2026-07-12 | Added `assertCoprimeStepZeroOffsetUnique`: any offset `i` in `[0,p)` with `mod(r+i*step,p) == 0` equals the witness returned by `coprimeStepZeroOffset(r,step,p)`. Focused verification passed (`24 valid`, `0 unknown`) and full verification passed (`12418 valid`, `0 invalid`, `0 unknown`). | The fixed-residue arithmetic kernel is now packaged as existence plus uniqueness. Next work should move carefully into the structural/list-count layer: connect the offset witness to a member of `expandSingleResidue` and prove the filtered size for one residue before composing across the full residue list. |
| 2026-07-12 | Read the expansion/list side after finishing the arithmetic kernel. `expandSingleResidue` is offset-major: each block is `addOffset(residues, i*mod)`, so values for one fixed residue are distributed one per block rather than contiguous. Existing private membership helpers in `SpecCycleSieveEquivalence` can show that a shifted value occurs in the expanded list, and private filter membership helpers can move nonmultiples through `filterList`, but there is no current public count lemma for "remove exactly one lift per residue." | The next code phase should not attempt the full `filterList(expandResidues(...)).size` theorem directly. Preferred next micro-goal is a small public helper around a single block/offset, or a local counting function/lemma for one fixed `r`, then lift that through `expandSingleResidue`. This is now structural list work, not density arithmetic. |
| 2026-07-12 | Added `SieveUtils.countMultiples`, a recursive producer that counts values divisible by a positive divisor and exposes `0 <= count <= list.size` in its postcondition. Focused verification passed (`14 valid`, `0 unknown`) and full verification passed (`12432 valid`, `0 invalid`, `0 unknown`). | This gives the structural count surface needed to state the filter-size bridge as `filterList(list,divisor).size == list.size - countMultiples(list,divisor)`. Next micro-goal should prove that bridge by induction on `list`, then specialize the count to expanded residue blocks. |
| 2026-07-12 | Added `SieveUtils.assertFilterListSizeByCount`, proving `filterList(list,divisor).size == list.size - countMultiples(list,divisor)` by induction over `list`. Focused verification passed (`37 valid`, `0 unknown`) and full verification passed (`12469 valid`, `0 invalid`, `0 unknown`). | The generic filter-size bridge is now verified. The remaining count obligation is to prove `countMultiples(expandResidues(residues,mod,p), p) == residues.size` under the coprime-step/current-survivor assumptions, or first the one-residue/block equivalent. |
| 2026-07-12 | Added `SieveUtils.assertCountMultiplesAppend`, proving `countMultiples(left ++ right, divisor) == countMultiples(left, divisor) + countMultiples(right, divisor)` by induction on the left list. Focused verification passed (`35 valid`, `0 unknown`) and full verification passed (`12504 valid`, `0 invalid`, `0 unknown`). | Count can now be pushed through the append shape used by `expandSingleResidue`. The next micro-goal should connect one block `addOffset(residues, i*mod)` to its multiple count, or prove a residue-major bridge if block-major counting becomes too awkward. |
| 2026-07-12 | Added `SieveUtils.countZeroOffsets`, a bounded recursive counter for offsets `i..p-1` satisfying `mod(r + i*step, p) == 0`. Focused verification passed (`13 valid`, `0 unknown`) and full verification passed (`12517 valid`, `0 invalid`, `0 unknown`). | This gives an arithmetic-sequence count surface separate from the block-major list shape. The next proof can package the existing Bézout kernel (`coprimeStepZeroOffset` plus uniqueness) into `countZeroOffsets(r, step, p, 0) == 1`, then bridge that count to singleton or full expanded lists. |
| 2026-07-12 | Added `SieveUtils.assertCountZeroOffsetsFromWitness`, proving that if `witness` is a zero offset in `[0,p)`, then `countZeroOffsets(r,step,p,i) == 1` when `i <= witness` and `0` otherwise. Focused verification passed (`75 valid`, `0 unknown`) and full verification passed (`12592 valid`, `0 invalid`, `0 unknown`). | This converts the arithmetic uniqueness lemma into an actual count theorem over the bounded offset scan. The immediate next wrapper should choose `witness = BezoutUtils.coprimeStepZeroOffset(r,step,p)` and prove `countZeroOffsets(r,step,p,0) == 1`; after that, connect this arithmetic sequence count to expanded-list counts. |
| 2026-07-12 | Added `SieveUtils.assertCountZeroOffsetsOne`, choosing the Bézout zero witness and proving `countZeroOffsets(r,step,p,0) == 1` for prime `p`, nonnegative `r/step`, and `mod(step,p) != 0`. Focused verification passed (`25 valid`, `0 unknown`) and full verification passed (`12617 valid`, `0 invalid`, `0 unknown`). | The fixed-residue arithmetic density claim is now verified as an exact count, not just existence/uniqueness. Remaining work is structural: prove that this offset count matches `countMultiples` over the corresponding expanded-list representation, then lift from one residue to the full residue list. |
| 2026-07-12 | Added `SieveUtils.assertCountMultiplesExpandSingleton`, proving `countMultiples(expandSingleResidue(List(r),step,p,i),p) == countZeroOffsets(r,step,p,i)` by following the singleton expansion recursion and using `assertCountMultiplesAppend`. Focused verification passed (`41 valid`, `0 unknown`) and full verification passed (`12658 valid`, `0 invalid`, `0 unknown`). | The one-residue list bridge is now verified. Combining this with `assertCountZeroOffsetsOne` gives the singleton expanded-list count. The next boundary is lifting from singleton residue lists to arbitrary survivor lists without losing the "one per residue" accounting. |
| 2026-07-12 | Added `SieveUtils.assertCountMultiplesExpandSingletonOne`, proving `countMultiples(expandSingleResidue(List(r),step,p,0),p) == 1` by composing the singleton list bridge with the exact offset count. Focused verification passed (`23 valid`, `0 unknown`) and full verification passed (`12681 valid`, `0 invalid`, `0 unknown`). | The singleton expanded-list theorem is now packaged as a single reusable statement. Next lifting work can focus on list decomposition/recomposition, not arithmetic density. |
| 2026-07-12 | Added `SieveUtils.countOffsetHits`, a structural counter for how many residues in a list satisfy `mod(r + i*step,p) == 0` for one fixed offset. Focused verification passed (`16 valid`, `0 unknown`) and full verification passed (`12697 valid`, `0 invalid`, `0 unknown`). | This is the per-block count surface needed for the arbitrary-list lift: prove `countMultiples(addOffset(residues,i*step),p) == countOffsetHits(residues,step,p,i)`, then sum those block counts across the expansion. |
| 2026-07-12 | Added `SieveUtils.assertCountMultiplesAddOffset`, proving `countMultiples(addOffset(list,i*step),p) == countOffsetHits(list,step,p,i)` by induction on the residue list. Focused verification passed (`45 valid`, `0 unknown`) and full verification passed (`12742 valid`, `0 invalid`, `0 unknown`). | Each block in the block-major expansion now has a verified count expression. Next step is to introduce a suffix-sum count over offsets and prove `countMultiples(expandSingleResidue(residues,step,p,i),p)` equals that sum. |
| 2026-07-12 | Added `SieveUtils.countExpandedOffsetHits`, a suffix-sum counter over offsets `i..p-1` that sums `countOffsetHits(list,step,p,i)` and proves the bound `0 <= count <= list.size * (p - i)`. Focused verification passed (`15 valid`, `0 unknown`) and full verification passed (`12757 valid`, `0 invalid`, `0 unknown`). | This creates the exact target expression for the block-major expansion proof. Next micro-goal should prove `countMultiples(expandSingleResidue(list,step,p,i),p) == countExpandedOffsetHits(list,step,p,i)` by recursion on offset `i`, using `assertCountMultiplesAppend` and `assertCountMultiplesAddOffset`. |
| 2026-07-12 | Added `SieveUtils.assertCountMultiplesExpandByOffsetHits`, proving `countMultiples(expandSingleResidue(list,step,p,i),p) == countExpandedOffsetHits(list,step,p,i)` by recursion over expansion offsets. Focused verification passed (`69 valid`, `0 unknown`) and full verification passed (`12826 valid`, `0 invalid`, `0 unknown`). | The block-major expansion is now connected to a counted sum of per-offset hits. The remaining lift is to prove that this suffix-sum is exactly one hit per residue under prime/coprime-step/nonnegative-residue assumptions, likely by relating `countExpandedOffsetHits(list,step,p,0)` to a residue-major sum of `countZeroOffsets(r,step,p,0)`. |
| 2026-07-12 | Added `SieveUtils.assertCountExpandedOffsetHitsCons`, proving the residue-major split `countExpandedOffsetHits(list,step,p,i) == countZeroOffsets(list.head,step,p,i) + countExpandedOffsetHits(list.tail,step,p,i)` for nonempty lists. Focused verification passed (`120 valid`, `0 unknown`) and full verification passed (`12946 valid`, `0 invalid`, `0 unknown`). | The sum-swap bridge is now available one cons cell at a time. The next proof can recurse over the residue list and use `assertCountZeroOffsetsOne` on each nonnegative residue to prove `countExpandedOffsetHits(list,step,p,0) == list.size` under prime/coprime-step/all-nonnegative assumptions. |
| 2026-07-12 | Added `SieveUtils.assertCountExpandedOffsetHitsOnePerResidue`, proving `countExpandedOffsetHits(list,step,p,0) == list.size` for nonnegative residue lists, prime `p`, and `mod(step,p) != 0`. Focused verification passed (`60 valid`, `0 unknown`) and full verification passed (`13006 valid`, `0 invalid`, `0 unknown`). | This is the arbitrary-list exact-density theorem in count form: one multiple of `p` appears per survivor residue across the `p` offsets. Next micro-goal should compose it with `assertCountMultiplesExpandByOffsetHits` to prove `countMultiples(expandSingleResidue(list,step,p,0),p) == list.size`, then with `assertFilterListSizeByCount` for the final size bridge. |
| 2026-07-12 | Added `SieveUtils.assertCountMultiplesExpandOnePerResidue`, proving `countMultiples(expandSingleResidue(list,step,p,0),p) == list.size` by composing the block-major expansion bridge with the exact one-per-residue offset count. Focused verification passed (`27 valid`, `0 unknown`) and full verification passed (`13033 valid`, `0 invalid`, `0 unknown`). | The exact removed-count theorem is now packaged at the expanded-list level. The final SieveUtils bridge can combine this with `assertFilterListSizeByCount` and the existing expansion-size lemma to prove the filtered expanded size is `list.size * (p - 1)`. |
| 2026-07-12 | Added `SieveUtils.assertFilterExpandSingleResidueSizeByDensity`, proving `filterList(expandSingleResidue(list,step,p,0),p).size == list.size * (p - 1)` from the verified removed count, `assertFilterListSizeByCount`, and `assertExpandSingleResidueSize`. Focused verification passed (`26 valid`, `0 unknown`) and full verification passed (`13059 valid`, `0 invalid`, `0 unknown`). | This proves the scoped expanded-interval size bridge: after expanding each survivor across the `p` offsets and filtering multiples of `p`, exactly one lift per survivor is removed. Next wrapper can expose the same statement for `expandResidues(list,step,p)`, whose body delegates to `expandSingleResidue(...,0)`. |
| 2026-07-12 | Added `SieveUtils.assertFilterExpandResiduesSizeByDensity`, proving `filterList(expandResidues(list,step,p),p).size == list.size * (p - 1)` as the public wrapper over the verified `expandSingleResidue(...,0)` theorem. Focused verification passed (`12 valid`, `0 unknown`) and full verification passed (`13071 valid`, `0 invalid`, `0 unknown`). | The SieveUtils-level density/size bridge is now verified for the M-interval expansion helper itself. Remaining integration work is to connect the actual `SieveSequence.nextFiltered` / `nextResidues` preconditions to this theorem, especially showing the relevant `step` is positive, coprime to `p`, and residues are nonnegative in the call path. |
| 2026-07-12 | Added `SieveSequenceNextLevel.assertNextFilteredSizeByDensity`, proving `nextFiltered(seq).size == nextResidues(seq).size * (seq.head - 1)` from the SieveUtils density theorem under explicit sequence-level preconditions: positive modulus/tail values, `seq.head >= 2`, and `Calc.mod(seq.modulus, seq.head) != 0`. Focused verification passed (`21 valid`, `0 unknown`) and full verification passed (`13092 valid`, `0 invalid`, `0 unknown`). | The density theorem is now integrated at the `nextFiltered` stage. Remaining work for strict size increase is separate: prove or assume the relevant residues are nonempty, discharge `Calc.mod(seq.modulus, seq.head) != 0` for real sequences, and bridge filtered/sorted/gap sizes if the final claim is about `nextGaps` or `nextGapCycle`. |
| 2026-07-12 | Added `SieveSequenceNextLevel.assertNextFilteredSizeGreaterThanResiduesByDensity`, proving `nextFiltered(seq).size > nextResidues(seq).size` under the density preconditions plus `seq.head > 2` and `nextResidues(seq).nonEmpty`. Focused verification passed (`20 valid`, `0 unknown`) and full verification passed (`13112 valid`, `0 invalid`, `0 unknown`). | The strict size-increase step itself is now verified conditionally. The nontrivial remaining integration is not the arithmetic; it is discharging the sequence-specific assumptions (`modulus` not divisible by `head`, nonempty residues) and deciding whether the final theorem should target `nextFiltered`, `nextSorted`, `nextGaps`, or the constructed `nextGapCycle`. |
| 2026-07-12 | Attempted `assertResiduesNonEmpty` directly (3 attempts) and hit the 3-attempt circuit-breaker. Failure modes: (1) `checkAllPositive` only -> invalid, counterexample `primes=[1,2]` where `mod(1,1)==0`; (2) `+ allGreaterThan(primes,1)` -> timeout on the recursive-predicate bridge `allGreaterThan(primes,1) ⟹ checkAllPositive(primes)`; (3) both predicates required -> timeout proving the recursive `isCoprime(1,primes)` predicate body from scratch at the call site. Root cause: no existing cached lemma for `isCoprime(1, primes)`, and the recursive predicate does not shortcut. All changes reverted to green baseline before continuing. | The missing piece is an isolated inductive helper that proves `isCoprime(1, primes)` once and caches it, mirroring `assertIsCoprimeForAll` and `primeIsCoprimeWithSmallerList`. Treat that helper as a new micro-goal (different target), not a 4th retry. |
| 2026-07-12 | Added `SieveUtils.assertIsCoprimeOne`, an isolated inductive lemma proving `isCoprime(1, primes)` for every list with `allGreaterThan(primes, 1)`. The induction mirrors `assertIsCoprimeForAll`: each step uses `ModSmallDividend.modSmallDividend(1, primes.head)` to show `mod(1, p) == 1 != 0`. Key fix for the earlier timeout: require BOTH `allGreaterThan(primes, 1)` (for the math) AND `checkAllPositive(primes)` (for `isCoprime`'s contract) to avoid the recursive-predicate bridge between them. Focused verification passed (`27 valid`, `0 unknown`) and full verification passed (`13139 valid`, `0 invalid`, `0 unknown`). | The cached helper unblocks `assertResiduesNonEmpty`. This confirms LEARNINGS 1.1 (same-class lemma reduces VC complexity) and 5.3 (predicate bridges need explicit induction, not solver inference). |
| 2026-07-12 | Added `SieveUtils.assertResiduesNonEmpty`, proving `residues(modulus, primes).nonEmpty` for `modulus >= 2` and `allGreaterThan(primes, 1)`. Composes `assertIsCoprimeOne` with the existing completeness lemma `assertGenerateResiduesContainsCoprime(1, 0, modulus, primes)`. Focused verification passed (`16 valid`, `0 unknown`) and full verification passed (`13155 valid`, `0 invalid`, `0 unknown`). | The SieveUtils-level nonempty-residues fact is verified. Next is the sequence-level wrapper to discharge `nextResidues(seq).nonEmpty` for real `CycleSieveSequence` states. |
| 2026-07-12 | Added `SieveSequenceNextLevel.assertNextResiduesNonEmpty`, proving `nextResidues(seq).nonEmpty` for `seq.modulus >= 2` and `checkAllPositive(seq.primesTailValues)`. Derives `allGreaterThan(seq.primesTailValues, 1)` from the `PrimeUtils.primeValues` ensuring (propagated through the `val` field binding without alias trouble). Focused verification passed (`8 valid`, `0 unknown`) and full verification passed (`13163 valid`, `0 invalid`, `0 unknown`). | The `nextResidues(seq).nonEmpty` precondition of `assertNextFilteredSizeGreaterThanResiduesByDensity` is now discharged at the sequence level. The only remaining open precondition is `Calc.mod(seq.modulus, seq.head) != 0` (the known Euclid/product wall, LEARNINGS 10.2 — kept as a documented explicit precondition per the ticket's stop conditions). Next: bridge size through `nextSorted` -> `nextGaps`. |
| 2026-07-12 | **MAJOR RE-FRAMING (user correction).** The `nextSorted.size == nextFiltered.size` route through `sortFiltered`/ascending-preservation was a wrong turn — that's implementation machinery, not the math. The "size" that matters is the **spec period** `p = indexOfAccepted(head + M)` — the number of accepted values in one modulus interval. The next stage `seq2 = seq1.next` has filter `[h] ++ Pbar`, so `seq2.accepts(v) ⟺ seq1.accepts(v) ∧ mod(v,h)≠0`. This filter-nesting is ALREADY VERIFIED: `assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple` (private, SpecSieveSequence:938) and its companion `assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple` (905) prove the bidirectional bridge; `assertRejectedByNextWhenNewHeadMultiple` (971) proves rejection of `h`-multiples. The size question decomposes cleanly: `seq2 count = seq1 count − (seq1-accepted values that are multiples of h)`. The second term is exactly the modular-permutation density the previous agent's kernel proved. | Do NOT pursue the `sortFiltered`/ascending/`nextFiltered` pipeline route. The right code target is at the SPEC level: compose the verified filter-nesting bridge with the verified density kernel into a period/size statement about `seq1` vs `seq2.next`. The cycle seq can be used as the reference size since spec≡cycle is proven (§6), but the *counting* should go through the spec's acceptance predicate and the filter-nesting lemmas, not through `nextGapsWalk`/`collectGaps`/`sortFiltered`. |
| 2026-07-14 | Rewrote `articles/chapter6/sieve-sequence-v2.md` Section 7.3 as structural mathematics instead of implementation mechanics, then tightened it again after user feedback so the subject is the sieve sequence itself: `S_k`, next-head correctness (`S_k(1) = h'`), primality of the first successor under the Bertrand precondition, lifted fibers, one removed lift per fiber, and next-stage survivors. Removed the confusing modulo-representative framing from the lead. | Markdown-only article repair; no Stainless verification required. Next proof/documentation work should keep the closed-form gap period bridge explicitly separate from the already verified same-head expanded survivor count. |
| 2026-07-14 | User pointed out that period should be part of the main sieve-sequence/spec properties, not introduced later as an additional structural fact. Split old Section 4.5 into `Canonical Period` (§4.5) and `Expanded Same-Head Survivor Count` (§4.6), later renamed to `Next Period from the Current Stage` because the important result is that the current stage determines the candidate next period `T' = T * (h - 1)`. Updated cross-references. | Keep §7.3 as a synthesis/transition section, while §4 carries the core object properties such as period and next-period formation. |
| 2026-07-14 | Cleaned up §4.5 notation after user feedback: removed the code/API name `indexOfAccepted` from math prose and expressed the period as the unique index `n` such that `S_k(n) = h + M`, with uniqueness justified by strict monotonicity. | Keep Scala helper names only in source references, not as mathematical objects. |
| 2026-07-14 | Moved `T` into the sieve-stage object definition after user feedback. The article now defines a stage as `{h, Pbar, T, G}`, uses `T` for the period in formulas, and reserves `|G|` for statements about the gap-list length. | Keep period notation standard and visible in the object definition before using it in §4-§7. |
| 2026-07-14 | Expanded §3.1 examples after user feedback. `S_0` now shows the unfiltered integer stream, `S_1` shows odd values and the `3^2` boundary, and `S_2` shows values not divisible by 2 or 3 and the `5^2` boundary. The prose now states that each stage filters only previous primes, so it is prime-correct below `h^2` while still reducing the search space by exact residue factors. | Use early examples to teach the sieve-stage semantics before the later formal properties. |
| 2026-07-14 | Clarified the core construction point in §3.1: no individual stage generates all primes; each stage is a finite-filtered search space, and the infinite chain of stage heads `h(S_0), h(S_1), ...` is the prime sequence. | Keep the distinction between a single partial-filter stage and the infinite sieve-sequence construction explicit. |
| 2026-07-14 | Added prime-sequence notation in §3.1: explicitly defines `P` as the set of all primes and `p_k` as the kth prime, then states `p_k = h(S_k)` and the ordered sequence of heads produces `2, 3, 5, 7, ...`. | Use standard mathematical notation for the all-primes set/sequence before relying on the infinite chain of heads. |
| 2026-07-14 | Started resolving stage-index vs element-index notation. Defined `A(S) = (a_i)` as the value sequence generated by a stage, `A_j = (a_i^(j))` for stage-indexed values, and explicitly banned `S_j(i)` notation because `S_j` is the stage object. Replaced the period boundary and next-head statements with `a_i^(k)` / `Spec^(k)_1` style as an interim step. | Finish the follow-up by migrating remaining `Spec_k` formulas to the new `A/a_i` notation or explicitly declaring `Spec` as an alias for `A`. |
| 2026-07-14 | Tightened the definition of the stage head after user feedback: `h` is not merely a larger prime than the tail filters; it is the next prime after the primes in `Pbar`, with the empty-tail base case giving `h = 2`. | Keep the stage object definition strong enough to make the head sequence unambiguous. |
| 2026-07-14 | Added symbolic head/tail-prime conditions to §3: `Prime(h)`, all entries of `Pbar` are smaller primes, every prime below `h` is in `Pbar`, and the empty-tail base stage has `h = 2`. | Pair prose definitions with mathematical conditions so reviewers do not have to infer the exact invariant. |
| 2026-07-14 | Replaced the separate `Prime(...)` predicate in article math with membership in the globally defined prime set `P`. Moved `P = {p_k | k >= 0}` and the ordered prime sequence definition into §2.1 before the stage definition, then rewrote the head/tail conditions as `h in P`, `p in P`, and `q in P`. | Avoid two competing prime notations; use the all-primes set consistently. |
| 2026-07-14 | User flagged that using `Cycle_k = CycleIntegral_k` conflates the sieve-stage generated sequence with the lower-level cycle-integral mechanism. Introduced `B(S) = (b_i)` as the gap-integral sequence, with `b_i = CycleIntegral(h,G)_i`, and changed the main theorem to `b_i = a_i`. Removed the false hand proof in §5.2 and left the verified source reference. | Keep article-level sequences distinct from implementation/mechanism names: `A` for scan values, `B` for gap-integral values, `CycleIntegral` only as the evaluator. |
| 2026-07-14 | Migrated the article notation from abstract `A/B` to convention-preserving `L/C`: `L_j = (ell_i^(j))` is the linear scan sequence and `C_j = (c_i^(j))` is the cycle-integral reconstruction. The main equivalence is now `c_i = ell_i`, while `CycleIntegral` remains only the lower-level evaluator. | Preserve uppercase for objects/sequences and lowercase for elements, while keeping the sequence names mnemonic. |
| 2026-07-14 | Added an explicit Chinese Remainder Theorem reference to §4.6. The next-period count now explains that because `M` and `h` are coprime, the `h` lifts of each current-period value cover every residue class modulo `h` exactly once, so exactly one lift is removed. | Use CRT as the mathematical intuition for the exact one-removed-lift count without expanding into a full proof detour. |
| 2026-07-14 | Replaced the cryptic "remaining bridge" wording in §4.6 with the direct statement that the surviving expanded values form one complete period of `S_{k+1}`, so `T' = T * (h - 1)`. | Prefer reader-facing theorem wording over internal proof-stage phrasing when the article is presenting the result. |
| 2026-07-14 | Tightened the construction claim in both the introduction and §7. Replaced overbroad "from structural data" / "`G` alone" framing with the precise point: the next stage's gap cycle is constructed from the current sieve-sequence cycle, using the current head as the new filter, without scanning the integers from scratch. | Avoid implying that `G` alone determines the next cycle; the construction depends on the current stage/cycle and the current head. |
| 2026-07-14 | Removed the sort/ordered-survivors step from the article's §7.1 pipeline and §7.2 correctness bullets. The filtered survivor list now carries scan order directly, and the next gap cycle is taken from adjacent differences between consecutive filtered survivors. | The pipeline should not imply a separate sort or ordering operation; order is inherited by the filtered mathematical list. |
| 2026-07-14 | Clarified the expansion step in §7.1: after expansion, before filtering by the current head, the expanded list is still exactly the current sieve-sequence cycle repeated over the longer interval. | Expansion is a representation change of the current cycle; the next-stage change begins at the head-filter step. |
| 2026-07-14 | Tightened the expansion notation in §7.1. Introduced `E = (e_i)` for the expanded sequence, changed residues to use the current `C = (c_i)` notation, and stated the pointwise preservation law `e_i = c_i` for `0 <= i < T`. | Make clear that the original cycle is embedded unchanged in the expanded sequence before any head filtering happens. |
| 2026-07-14 | Added a friendly repeated-list display to §7.1's expansion step, following the style used in `cycle.md`: `[c_0, ..., c_{T-1}, c_0+M, ..., c_{T-1}+M, ..., c_0+(h-1)M, ...]` before the indexed definition. | Show the shape of the expanded cycle before asking the reader to parse the `e_{qT+r}` formula. |
| 2026-07-14 | Corrected the expansion emphasis in §7.1: the key invariant is that the expanded sieve sequence has the same gap cycle repeated, `G_E = repeat(G, h)`, before the new head filter is applied. | Expansion preserves the current gap structure; filtering is the first step that changes the gap pattern. |
| 2026-07-14 | Refined the expansion notation in §7.1 after user feedback: the expanded sequence `E = (e_i)` is pointwise equal to the current cycle sequence `C = (c_i)` for all indices, `e_i = c_i`; only the finite window `E_h = [e_i | 0 <= i < hT]` is longer for the next-head filtering step. | Avoid suggesting equality only holds for the first copy; expansion is the same infinite sequence viewed through a longer window. |
| 2026-07-14 | Tightened the expansion wording in §7.1 to avoid saying the expanded object is the "same sequence." The article now says the expanded representation has different internals but emits the same values and gaps before the new head filter is applied. | Distinguish object/representation identity from equality of emitted results. |
| 2026-07-14 | Removed the alternate mini-pipeline from §7.3 ("next prime -> lifted fibers -> one removed lift -> survivors"). Replaced it with prose saying the structural properties justify the actual §7.1 pipeline. | Avoid presenting two different transition descriptions that could confuse readers. |
| 2026-07-14 | Added a transformation overview to the start of §7 using the actual pipeline names: `C -> E_h -> F -> nextGaps -> G'`. | Preserve the helpful transformation narrative while keeping it aligned with the formal pipeline in §7.1. |
| 2026-07-14 | Renamed §8 from `Unproven Axioms` to `Proof Boundary` and clarified that only Bertrand's postulate is an external assumption; the coprime invariant and next-period count are verified facts. Also fixed the conclusion's stale "`G` alone" claim. | Avoid grouping proved conditional lemmas and verified invariants under an "unproven axioms" heading. |
| 2026-07-14 | Added a practical computation tradeoff to the conclusion: although a built gap cycle makes generation cheap, each new head expands the construction by `h` lifts and the period by `h - 1` while removing only `1/h` of candidates. | Keep the article honest that managing very large sieve-sequence cycles eventually outweighs the local candidate-testing savings. |
| 2026-07-14 | Reframed the article's motivation around finite analytical objects rather than only computation. The abstract/introduction and conclusion now say sieve-sequence stages expose finite gap cycles whose copy/merge behavior can constrain later prime candidates; absence of gap `2` is presented as a candidate-level obstruction for future twin-prime pairs. | Make the main benefit structural analysis of future behavior, while avoiding an overclaim before the gap-filtering subsection is added. |
| 2026-07-14 | Softened the introduction/conclusion gap-analysis claims because the article body does not yet present the gap-copy/gap-merge theorem. Moved the gap-2/twin-prime-candidate example to the dedicated future ticket. | Do not introduce important new properties only in the conclusion; first add a body subsection with the gap behavior proof. |
| 2026-07-14 | Rewrote the conclusion's computational paragraph to avoid drifting back into cycle-mechanics framing (`static state machine`, single-addition formula). It now frames the benefit and tradeoff in terms of finite sieve stages/search spaces. | Keep the article centered on sieve-sequence properties rather than low-level cycle generation mechanics. |
| 2026-07-14 | Fixed §4.1 soundness proof by removing the false small-dividend claim `mod(h,p)=h` for tail primes `p<h`. The proof now relies on the stage invariant that the head is accepted by the tail filters. | Tail primes are smaller than the head, so small-dividend does not apply; acceptance comes from the sieve-stage invariant/filter definition. |
| 2026-07-14 | Added the article-level mathematical proof that the counted expanded survivors form the first canonical period of `S_{k+1}`. The abstract, §6, §7.3, §8, and conclusion now distinguish verified properties from the remaining Stainless packaging boundary: Bertrand is an external precondition, and `period(S_{k+1}) = T * (h - 1)` still needs a final wrapper theorem carrying the §4.7 proof into Stainless and then to the constructed next gap cycle. | The article should no longer describe the period identification as mathematically open; it is a math proof with Stainless wrapper verification pending. |
| 2026-07-14 | Cleaned up the remaining article issues while leaving proof code untouched for the other developer: renamed §4 to linear scan properties, migrated remaining mathematical `Spec_k` notation to `ell_k`, added the missing `v >= h` domain to completeness, removed the stale `|Spec|` period notation, replaced a vague survivor-exactness reference in §7.2, and corrected the false implication that current-stage survivors are never divisible by the current head. | Keep source references to `SpecSieveSequence::*` as code references only; article math should use `L`, `C`, `ell_i`, and `c_i` consistently. |
| 2026-07-14 | Applied the follow-up inspection fixes accepted by the user: the abstract now says "next-period count" instead of "expected next period" and groups the pending period wrapper plus transfer to constructed next gap cycle as one Stainless packaging boundary; §4.6 now shows the finite per-fiber count before the closed form; §5.1 names the source-backed period/reconstruction facts; §7.2 is explicitly conditional on the next-period boundary. Preserved and clarified the expansion invariant that the expanded object has the same `apply` results as the current cycle while exposing the lifted finite window. | Future article review should treat §7.2 as conditional packaging until the proof developer lands the wrapper theorem. Do not weaken the `e_i = c_i` / same-apply invariant; explain it through periodic indexing instead. |
