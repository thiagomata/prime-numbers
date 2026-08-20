# Chapter 4 `integral-cycle.md` — Article Quality Checklist Pass (Publish Prep)

**Created:** 2026-08-20
**Updated:** 2026-08-21
**Status:** In progress — chapters 5/6 restructured, several proofs newly
  written and one real gap-in-proof-rigor cleaned up per-section; a
  systematic pass for the same class of issue (thin/missing proofs, vague
  backward references, implementation-vocabulary-as-notation leaks) has
  not yet been run across the rest of the article. §6.9 Direct
  Construction from Survivors is a known remaining thin proof.
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

## Resolved (this session, not yet committed)

1. **OBJECTS.md parity gaps in `CycleIntegralProperties`** — added
   `§4.4 Cycle Integral Strictly Increasing` and `§4.5 Cycle Integral
   Positivity`, matching the analogous sections already present in
   `integral.md`/`cycle.md`.
2. **`CycleIntegralFilterProperties` merge/filter cluster** — after
   discussion, decided these are valid, Stainless-verified properties
   that deserve documentation independent of whether other code calls
   them (CONTRIBUTING.md rule 14.18). Added as a full 4-subsection group
   covering the merge shift law, removing a multiple, direct
   construction from survivors, and the filtered result having no
   multiples, plus 4 new Appendix A entries.
3. **Conclusion completeness (rule 6)** — recap now includes Cycle-Period
   Shift and Survivor Structure (both previously missing), plus the two
   new Persistent Non-Zero/Zero Residue corollaries.

## Structural restructuring (this session, not yet committed)

The article's chapters 5–7 were reorganized around a conceptual
distinction the owner drew out during review: properties of a *fixed*
cycle integral versus properties for *deriving a new* cycle integral from
an existing one.

- New **§5 Persistent and Periodic Properties** (fixed CI): general
  residue periodicity, persistent non-zero/zero residue (the two
  corollaries, new content), gap telescoping, cycle-period shifts, and
  residue classification.
- New **§6 Deriving New Cycle Integrals**: x-fold expansion, right/left
  index shift, gap rotation, survivor filtering (exactness + structure),
  and the filter-merge reconstruction group. Old chapters 6 and 7
  dissolved into this one chapter; §5.3/§5.8 (both index-shift-adjacent)
  were deliberately kept as separate sections rather than merged, per
  owner instruction.
- Old §8 Conclusion → §7, old §9 Future Work → §8. All in-document
  cross-references, the intro bullet list, and the Conclusion's prose
  and math recap were updated to match. Verified with a full anchor-link
  sweep (53 links, all resolve) and `git diff --check`.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-20 | First-pass heading rename for a promoted section (mirroring gap-dynamics.md) renamed the heading text but left content in the wrong physical file position -- renaming and moving are two separate steps, don't assume a text-substitution script handles reordering. | Caught during self-review before presenting to article owner; content block physically relocated as a second step. |
| 2026-08-20 | OBJECTS.md parity checks on a dense proof article can surface real gaps (2 confirmed) alongside much larger, more ambiguous ones (22-lemma class almost entirely uncited anywhere in the repo) -- don't conflate the two when reporting; they need different kinds of decisions. | Findings split into "clear gaps" vs. "ambiguous scope question" in this ticket and in the turn presented to the user. |
| 2026-08-21 | Splicing large verbatim blocks of existing content into a new order (reusing exact ranges via a script) is far more reliable than retyping sections by hand -- but concatenating extracted blocks that each already end in a blank line, next to new hand-written blocks that also start with one, silently produces double-blank-line seams. | Ran a regex pass collapsing 3+ consecutive newlines down to one blank line immediately after the splice, before presenting the result. |
| 2026-08-21 | A "Proof." paragraph that only names the Scala lemma being invoked, with no worked math, can hide a real ordering/dependency bug -- expanding §5.1's proof for real surfaced that it secretly depended on a fact (§5.5's full-cycle shift) that had no proof of its own and, worse, came later in reading order. | Wrote a real proof for the dependency first, then reordered chapter 5 so proof order matches logical dependency order, instead of leaving a forward-reference disguised as a citation-free assertion. |
| 2026-08-21 | Naming a math quantity after its Scala field (`sum(ci)`, mirroring `ci.sum`) can be actively misleading when the object it's attached to (`ci`, an unbounded strictly-increasing stream) makes the name read as "sum over infinitely many terms." The notation was also never formally defined anywhere in the article -- just used as if inherited from the source. | Renamed to `periodSum(ci)`, added a real definition where first used, and registered both `period(ci)`/`periodSum(ci)` in `VOCABULARY.md` so future articles reuse the same disambiguated names. |
| 2026-08-21 | A "connecting sentence" reconciling two similarly-named claims (`assertPeriodicShift` vs `assertFullCycleShift`) was itself a symptom: both Scala lemmas are thin wrappers around the exact same underlying call, so the article had manufactured a "difference form vs. sum form" distinction that doesn't actually exist in the source. | Collapsed the claim, subsection name, and every citation down to one identity ("Full-cycle shift"); removed the reconciling sentence entirely instead of keeping it as a patch. |
