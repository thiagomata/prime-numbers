# Review — `articles/chapter3/list.md`

**Date:** 2026-08-31
**Reviewed against:** `PROOF_GUIDE.md`, `CONTRIBUTING.md` (26-point checklist), `AGENTS.md`.
**Status:** No changes made — analysis only.

## Overall assessment

`list.md` is one of the five articles PROOF_GUIDE.md names as the source of
its own Voice-and-Style conventions, and §§2–9 largely earn that: every
section opens with a framing sentence and bullet summary, most properties
carry a real induction (explicit base case / inductive step, `\blacksquare`,
`[Q.E.D.]`), and appendix numbering stays in sync with the body throughout
24 entries. The article visibly drifts in its two newest-looking sections —
§10 (Shifted List) and §11 (Rotation) — and in its Conclusion math recap,
where three of five blocks merge unrelated property groups together and the
recap silently drops three properties the introduction promised. §8 (Bound
and Order) is the one older section that already shares the newer sections'
weakness: none of its seven subsections carries any derivation at all.

## Strengths

- §§3–9 open with a framing sentence plus bullet list every time (checklist
  rule 2), and most properties follow the full explain → state → derive →
  cite pattern with `\blacksquare`/`[Q.E.D.]` closers (17/15 occurrences).
- Appendix A's 24 entries stay numbered in lockstep with their body
  citations — every `Appendix A.N` reference checked resolves to the
  matching lemma.
- §7's use of the chapter-2 shift law (`mod(a + m·b, b) = mod(a, b)`) is
  introduced with an explicit forward citation to `modulo.md` and states the
  reused fact inline — a correct application of the "restate a prior
  theorem's statement" rule in PROOF_GUIDE.md.
- §13 Future Work explicitly names `SortedList`, `MinBoundList`, and
  `MaxBoundList` as verified-but-out-of-scope, and §11's closing paragraph
  names the four rotation helper lemmas it deliberately excludes as
  structural plumbing — both are correct, checklist-rule-9-compliant
  disclosures of intentional scope gaps.
- List cons/concatenation notation (`x :: L`, `A \mathbin{\texttt{++}} B`)
  is used correctly and consistently; no singleton-list constructions found.

## Issues

### 1. Conclusion math blocks merge unrelated property groups (major)

CONTRIBUTING rule 19 requires each conclusion math block to stay "scoped to
one property group rather than merging unrelated properties into a single
shared `\begin{aligned}` environment," specifically because KaTeX sizes
every row in a block to the widest row. Three of the conclusion's five
blocks violate this:

- Block 1 (lines 1315–1328) merges §3.2 Last Element Identity, §3.1 Tail
  Access Shift, and §4.4 Slice Append Consistency — three different
  sections' property groups in one block.
- Block 4 (lines 1384–1406) merges the five §8 Bound-and-Order rows with
  §9's Slice Equivalence — a different chapter's property group appended
  as a sixth row with no heading break.
- Block 5 (lines 1408–1427) merges §10 Shifted List (Adjacent Difference,
  Gap Translation) with §11 Rotation (Same Elements, Same Size, Same Sum) —
  again, two distinct property groups sharing one environment.

**Fix:** split each of these three blocks along the same section boundaries
the body already uses (§3/§4, §8/§9, §10/§11).

### 2. Conclusion recap silently drops three properties the intro promised (major)

CONTRIBUTING rule 6: "Every property from the intro group list appears in
the conclusion math block." Checking each intro bullet (§1, lines 43–53)
against the conclusion blocks:

- Intro promises "Shifted list: period, gap identity, gap translation"
  (§10). The conclusion recap (block 5) has Adjacent Difference and Gap
  Translation but **no Same Period row** — §10.1 is missing entirely.
- Intro promises "Rotation: permutation invariants (size, sum, **bounds**,
  membership)" (§11). The conclusion recap has Same Elements, Same Size,
  Same Sum, but **no bound-preservation row** (upper or lower) and **no
  Index Shift Under Rotation by One** (§11.2) — half of §11's stated
  content is missing from its own recap.

**Fix:** add the missing rows (Same Period; both bound-preservation
directions; Index Shift by One) to the split-out §10 and §11 blocks from
issue 1.

### 3. Several §10/§11 properties restate the claim, tag `[Q.E.D.]`, and derive nothing (major)

This is PROOF_GUIDE's own worked anti-pattern ("A Q.E.D. Label Is Not a
Proof") reproduced almost verbatim:

- §10.1 Same Period (lines 1111–1115): the math block is
  `\text{period}(\text{shifted}) = \text{period}(\text{original}) \quad
  \text{[Q.E.D.]}` — the claim, with a label, and no step. (One sentence of
  prose above it does give a reason — the case-class invariant — which
  softens this one somewhat.)
- §10.2 Adjacent Difference Equals Gap (lines 1132–1137): same shape — the
  goal restated with `[Q.E.D.]` appended, no substitution from the
  `value_{h,G}(i+1) = value_{h,G}(i) + G_i` definition given three
  paragraphs earlier, even though that substitution is one line.
- §11.1's "Membership" bullet (lines 1227–1232) and §11.2 Index Shift Under
  Rotation by One (lines 1260–1265) do the same: state the claim, append
  `[Q.E.D.]`, derive nothing.
- §11.1's "Size and sum" and "Bound preservation" bullets go a step further
  and drop the `[Q.E.D.]` too — they are bare assertions with one clause of
  prose ("Sum over append is additive and commutative") and no math step at
  all for bound preservation.

Compare with §5.1–§6.4 in the same article, where every inductive step is
spelled out with a labeled substitution chain — the derivation discipline
clearly exists in this article, it just wasn't applied to §10–§11.

**Fix:** each of these is a one- or two-line derivation from a definition
already stated earlier in the article (the `value_{h,G}` recursion for
§10.1/§10.2, the `rotateAt = back ++ front` definition for §11.1/§11.2).
Write the step instead of the bare restatement.

### 4. §8 (Bound and Order) has no derivation in any of its seven subsections (moderate)

Unlike §3–§7, none of §8.1 through §8.7 has a proof paragraph, an induction
sketch, or even a one-sentence reason — each is a math statement followed
directly by "This property is verified in [link]." Under PROOF_GUIDE's
print-only test, a reader without repository access cannot verify any of
the seven Bound-and-Order properties from the article text alone. This is
the same failure mode as `modulo.md`'s under-proved subsections, and
notably it predates §10/§11 in the file, so it is not purely a "later
sections drifted" story — this gap already existed in the chapter that
PROOF_GUIDE names as a style reference.

**Fix:** add a short inductive sketch to each of §8.1–§8.7 (most are
one-line "peel the head, apply the inductive hypothesis" arguments, per the
style already used in §5.5 and §6.5's brief-but-present proof sketches).

## Minor observations

- §3.3 (Indexed Access Under Concatenation) is never named in the intro's
  compact group list (§1 bullet for §3 says only "tail shift, last
  element") and never appears in the conclusion recap either. It has a real
  prose proof sketch in the body, so this looks like an intentional
  "headline vs. building-stone" omission rather than an oversight, but
  nothing in the article says so explicitly the way §11's closing paragraph
  does for the rotation helpers.
- §10 and §11 embed Scala directly in the body (with a source link
  immediately after, correctly per rule 10) instead of routing to Appendix
  A the way every property in §3–§9 does. Both patterns are individually
  allowed by CONTRIBUTING rule 10, but using one convention for 24
  properties and switching conventions for the last 6 reads as if the
  article picked up a different author's habit partway through.
- The chapter-2 dependency (`modulo.md`) is not mentioned until §7; there
  is no `## 2. Preliminaries`-style acknowledgment of it near the top of
  the article the way CONTRIBUTING's example structure suggests. Not a
  hard violation — §7 does restate the reused fact inline — but a reader
  skimming the introduction would not learn this article depends on
  chapter 2 until two-thirds of the way through.
- §11.1 repeats the three-bolded-topic-sentence pattern ("**Membership.**",
  "**Size and sum.**", "**Bound preservation.**") also seen in
  `modulo.md` §6.14 — each is followed by real prose, so it isn't the
  labeled-block anti-pattern, but it's the same author habit recurring in a
  second article and worth watching if a fourth bolded opener is ever
  added to either section.

## Not an issue (checked, compliant)

- Section numbering, nesting depth, no letter suffixes — compliant.
- No ticket references, no status columns, no coding-strategy sections —
  compliant.
- `:=`/`=` usage, inline math spans, comparison spacing — compliant.
- First-person-plural voice throughout — compliant.
- No forward references to chapters 4–6 — compliant.

## Suggested priority

1. Split the three merged conclusion blocks and restore the three missing
   rows (issues 1–2) — these are the most visible, most mechanical fixes.
2. Add real derivations to §10.1, §10.2, §11.1's bound-preservation bullet,
   and §11.2 (issue 3).
3. Add derivation sketches to §8.1–§8.7 (issue 4) — larger but same shape
   as the fix already applied elsewhere in the article.
4. Minor observations are optional polish.
