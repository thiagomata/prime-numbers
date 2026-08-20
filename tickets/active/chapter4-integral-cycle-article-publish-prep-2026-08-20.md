# Chapter 4 `integral-cycle.md` — Article Quality Checklist Pass (Publish Prep)

**Created:** 2026-08-20
**Updated:** 2026-08-20
**Status:** In progress — mechanical fixes committed, content gaps pending owner decision
**Depends on:** none — fourth article in the publish-prep sequence
  (`modulo.md`, `list.md`, `cycle.md` already done)

## Related Tickets

- `chapter4-cycle-article-publish-prep-2026-08-19.md` (deleted, folded
  into commit `c79d605c`) — established pattern: full read, rule-by-rule
  audit, present findings for confirmation before editing.

## Related Articles

- `articles/chapter4/integral-cycle.md` — under review.

## Done (committed)

Mechanical/structural fixes applied and confirmed by the article owner:
- Dot-notation-in-math leak in §5.8 (`GapList(...).apply(i)`) rewritten
  to proper function/subscript notation.
- 10 unnumbered `###`/`####` headings folded into bold text or removed
  (2x "Sum/Step Property" in §3.2, "Proof" in §5.1, 4x "Base Case"/
  "Induction Step" in §5.3/§5.4, 7x "Stainless Verification" scattered
  through §5).
- Redundant `**Status**:` meta-label removed (§5.4) — fact was already
  stated once at §5's intro.
- Heading-embedded `[Finite-Period Verified]` status tag dropped from
  `### 5.3 Right Index Shift`'s title; its one internal link updated.
- "Unpublished manuscript" removed from all 4 References entries,
  matching the format every other article in the repo uses for the same
  cited files.
- Conclusion's 2-item numbered list converted to prose, with its two
  bare "Section 3.1"/"Section 3.2" mentions converted to real §N links.
- Structural: §5.9 "Modularity and Survivor Filtering" (had two real
  children, 5.9.1/5.9.2, nested three heading-levels deep) promoted to
  its own whole-number chapter (now §6, children 6.1/6.2), mirroring the
  gap-dynamics.md §5.3/§6.5 fix from earlier this session. Old §5.10
  (no children of its own) renumbered down to fill the gap at §5.9; old
  §6 Conclusion -> §7, old §7 Future Work -> §8. The content block for
  the promoted section had to be physically moved in the file, not just
  have its heading renamed -- caught and fixed a first-pass mistake
  where the heading rename left the content in the wrong reading-order
  position. The verification-status summary sentence referencing the
  old "properties 5.5-5.10" range was also updated since that range no
  longer exists as one contiguous span after the split.

Verified false positives, correctly NOT touched: the "later sieve
arguments" phrase in §8 Future Work (protected by the same rule-14.4
reasoning as cycle.md's Future Work finding); the Hardy & Wright
citation's `§5.4`/`§15.1` (cites the external book's sections, not this
article's own, despite the numeric coincidence).

## Open — needs owner decision before continuing

1. **Two clear OBJECTS.md parity gaps** in `CycleIntegralProperties`
   (§4.8): `assertCycleIntegralIncreasing` (CI strictly increasing under
   positive gaps) and `assertCycleIntegralPositive` (CI positive given
   non-negative init/values) are verified in source but never mentioned
   in the article, even though `integral.md`/`cycle.md` both have
   analogous sections for their own types.
2. **One large, ambiguous OBJECTS.md gap**: `CycleIntegralFilterProperties`
   (§4.11, ~22 lemmas about merge/filter-reconstruction semantics --
   `newCI`, `findFirstMultiple`, `assertShiftAtMerge`, etc.) is almost
   entirely uncited anywhere in the repo (1 of 22 lemmas gets a passing
   internal-helper citation in this article; confirmed via grep that
   `sieve-sequence.md` doesn't cover it either, despite sounding like
   "copy-or-merge" territory). Real gap or belongs to a future article --
   undecided.
3. **Conclusion completeness (rule 6)**: math recap is missing standalone
   representation for §4.2 (Same Difference After Full Cycle), §5.7
   (Cycle-Period Shifts -- distinct from Modulo Periodicity, which IS
   represented), and §6.2 (Survivor Structure -- only 6.1 Survivor
   Exactness appears). §5.3/§5.4 (index shifts) absence may be
   deliberate since those two are mathematically-proved-but-not-yet-
   Stainless-verified, unlike everything else in the recap.

None of the three are mechanical fixes -- #1 and #3 need real math
writing, #2 is a scope question (new content vs. flag-as-known-gap vs.
belongs elsewhere). Awaiting direction before continuing.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-20 | First-pass heading rename for a promoted section (mirroring gap-dynamics.md) renamed the heading text but left content in the wrong physical file position -- renaming and moving are two separate steps, don't assume a text-substitution script handles reordering. | Caught during self-review before presenting to article owner; content block physically relocated as a second step. |
| 2026-08-20 | OBJECTS.md parity checks on a dense proof article can surface real gaps (2 confirmed) alongside much larger, more ambiguous ones (22-lemma class almost entirely uncited anywhere in the repo) -- don't conflate the two when reporting; they need different kinds of decisions. | Findings split into "clear gaps" vs. "ambiguous scope question" in this ticket and in the turn presented to the user. |
