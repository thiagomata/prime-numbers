# Chapter 4 `cycle.md` / `integral.md` — Proof Rigor Audit

**Created:** 2026-08-21
**Updated:** 2026-08-21
**Status:** In progress — all 4 `cycle.md` findings fixed, plus a new
  §5.10-5.12 addition (below), not yet committed; `integral.md`'s 2
  findings and 5 minor checklist items still open
**Depends on:** none, but uses the same audit lens developed while fixing
  `articles/chapter4/integral-cycle.md` this session

## Related Tickets

- `chapter4-integral-cycle-article-publish-prep-2026-08-20.md` (in
  progress) — the sibling article where this audit lens was developed:
  thin/missing proofs, vague backward references, notation borrowed
  unformalized from Scala field names, and — the recurring one — claims
  framed as two independent verified facts that turn out to be thin
  Scala wrapper aliases around one shared lemma (found there as
  `GapProperties.assertPeriodicShift`/`assertFullCycleShift`, both
  delegating to `CycleIntegralFilterProperties.assertCIShiftEqualsSum`).
- `chapter4-cycle-article-publish-prep-2026-08-19.md` (deleted, folded
  into commit `c79d605c`) — the prior full checklist pass on `cycle.md`.
  That pass covered CONTRIBUTING.md mechanics (headings, dot-notation,
  References formatting); it did not audit proof *substance*, which is
  what this ticket's findings are about — the two are complementary, not
  contradictory.

## Related Articles

- `articles/chapter4/cycle.md` — 4 substantive findings (below).
- `articles/chapter4/integral.md` — 2 substantive findings, plus 5 minor
  CONTRIBUTING.md checklist items (this article has only had the
  mechanical `§N` anchor-link sweep so far, no full pass).

## Method

Two background agents independently read each full article and, for
every Scala lemma the article cites, opened and read the actual function
body in source (not the docstring or the article's paraphrase). Checked
for: (1) thin or missing proofs, (2) vague backward references, (3)
undefined or misleading notation, (4) manufactured/redundant
distinctions between claims that share one underlying Scala lemma, (5)
forward references, (6) dot-notation-in-math leaks, (7) citation
mismatches between what's proved and what's cited.

## Findings — `articles/chapter4/cycle.md` (FIXED, not yet committed)

1. **Thin proofs, §5.7 Cycle Value Positivity and §5.8 Cycle Rotation.**
   Both math blocks just restate the theorem and append `[Q.E.D.]` with
   no derivation — and are the *only* two Q.E.D. lines in the whole
   document missing the `\blacksquare` mark that every other proved
   section has (confirmed: lines 382/407/446/469/494/518/546/587 all
   have it; 624/641 don't). The real Scala proofs are non-trivial:
   `rotateAtValue` (behind §5.8) chains `collectRotatedValueAt`, two
   `ModOperations.modAdd` calls, and `ModIdempotence.modIdempotence` —
   none of which is reflected in the article math.

2. **Manufactured distinction, §5.9.** Claims five `MemCycleProperties`
   lemmas are "independently re-proved directly against `MemCycle`
   rather than derived from the `ModCycle` result by delegation." Source
   check: `MemCycle.apply` is an unconditional one-line delegation to
   `ModCycle`, so `MemCycle(pos) == ModCycle(pos)` holds for every
   position (already established generally in the article's own §3.3).
   The five cited `MemCycleProperties` lemmas are byte-for-byte identical
   proof bodies to their `CycleProperties` (ModCycle) counterparts — only
   the type annotation differs. None actually uses the §3.3 equivalence
   to derive the MemCycle result by substitution; they redundantly
   re-derive from scratch. Same class of issue as the
   `assertPeriodicShift`/`assertFullCycleShift` case in
   `integral-cycle.md`.

3. **Forward references — 1 real, 1 false positive.** §3.3's own
   equality chain cited `[By §4]` for a result not yet proved at that
   point — a real issue, since it was a formal proof-step citation, not
   an overview. The Mermaid class diagram's own "§4.1-4.2"/"§3.3" edge
   labels were originally flagged too, but that was a false positive:
   CONTRIBUTING.md rule 20 explicitly requires "section references on
   the arrows" for this kind of overview diagram, and forward-pointing
   labels are exactly what an overview sitting before the detailed
   proofs is expected to do — corrected after the article owner pointed
   out the diagram is effectively part of the chapter intro.

4. **Undefined notation.** `\text{repeat}(V, t)` (§5.6, Conclusion) and
   `\text{rotateAt}(\text{Cycle}, k)_i` (§5.8, Conclusion) are introduced
   directly in math fences with only prose gloss — never a formal
   case-based definition, unlike `sum`/`slice`/`last`, which all get one
   in §2 Preliminaries. Lower severity than a *misleading* name (neither
   name misdescribes its own behavior), but the same underlying gap:
   notation borrowed from Scala method names without being formally
   anchored before first use.

**Clean:** no vague backward references, no dot-notation-in-math leaks,
no citation mismatches — every cited lemma matches what the article
claims it proves.

### Additional finding (not from the original agent audit): §5.1-5.5 proof presentation

Caught by the article owner after the original 4 findings were fixed:
§5.1-5.5 each crammed the shared setup (`L := [...]`, `Cycle := [...]`,
`n := |L|` — identical, copy-pasted five times verbatim), the claim, and
the derivation into one undifferentiated `math` block with no
`**Proof.**` label — unlike §5.6-5.8, which all separate claim from
proof. The math itself was valid in all five cases (real 2-3 step
substitution chains using Cycle Equivalence and the ModCycle/RecCycle
definitions, not circular or vacuous) — this was purely a presentation
defect, not a missing-derivation one, but it's exactly why §5.1 "didn't
look like a proof" on inspection. Fixed by hoisting the shared setup to
the §5 chapter intro (stated once) and restructuring each of §5.1-5.5
into Claim → `**Proof.**` → derivation → `∴...∎`, matching the style
already used by §5.6-5.8. No math content changed, only its structure.

### Fixes applied

1. §5.7 now has a real induction proof (base case: list head is
   non-negative by hypothesis; inductive step: `Access Tail Shift Left`
   plus the induction hypothesis on the tail). §5.8 now has a real
   4-step derivation using `rotateAt`'s new formal definition plus
   Modulo Idempotence + Distributivity over Addition
   (`articles/chapter2/modulo.md` §6.8/§6.9). Both now carry
   `\blacksquare`.
2. §5.9 reframed honestly: states plainly that `MemCycle(L)_i =
   ModCycle(L)_i` at every position (established at the close of §4)
   means these five results carry over by pure substitution and the
   section adds no new mathematical content; the five separate
   `MemCycleProperties` lemmas exist only because Stainless can't
   transfer a lemma proved for one concrete type to a different wrapper
   type, not because independent re-derivation was mathematically
   necessary.
3. The real forward reference is fixed: §3.3's premature
   three-way-equality math block (tagged `[By §4]`) was removed and
   reassembled at the close of §4.2, the first point where both
   dependencies (§3.3's MemCycle≡ModCycle and §4's RecCycle≡ModCycle)
   are actually established. The Mermaid diagram went through two
   revisions before landing: first removed entirely (it wasn't earning
   its place — see below), then restored with its relationship edges
   corrected once a redesign showed the diagram itself could be fixed
   rather than dropped. Precise reason for the original problem, not
   "computing diagrams are inherently non-mathematical" — when a type's
   computing shape *is* its math shape (as with `List`, `ModDiv`,
   `Cycle` here), a structure diagram can genuinely help a reader see
   relationships. This one failed because both relationship edges used
   the same generic arrow (`-->`) with a text label for two different
   kinds of facts: `RecursiveCycle`≡`ModCycle` is two independent
   definitions related by a proof (induction, §4.1-4.2), while
   `MemCycle` literally contains a `ModCycle` field (real composition).
   Collapsing both into one arrow style is what made the relationships
   read as thin, undifferentiated assertions. Fixed by using Mermaid's
   actual UML vocabulary — `..>` (dashed dependency) for the proven
   equivalence, `*--` (solid composition diamond) for the structural
   wrap — with every field kept at full fidelity to the original (an
   earlier attempt to also trim "identical across classes" fields like
   `values`/`period` was corrected by the article owner: shared fields
   aren't the same as non-meaningful fields — `values` is the common
   substrate that makes the equivalence claim comprehensible at all,
   and `period` is the `n` every formula in the article depends on).
4. Added formal case-based definitions for `repeat(V,t)` (§5.6, matching
   `ListRepeatProperties.repeat`'s real recursive definition) and
   `rotateAt(L,k)`/`rotateAt(Cycle,k)` (§5.8, matching `ModCycle.rotateAt`
   + `CycleUtils.collectRotated`'s real semantics), each right before
   first use.

Validated: `git diff --check` clean, 106 fence markers (even), all 36
in-document anchor links resolve, no dot-notation-in-math leaks
introduced, both new `modulo.md` §6.8/§6.9 external links confirmed
against that article's actual headings.

### New content — §5.10-5.12 Residue Classification Transfer

Article owner flagged (during proof-simplification review) that
`MemCycle`'s divisor-classification predicates —
`allModValuesAreZero`/`noModValuesAreZero`/`someModValuesAreZero`
(`MemCycle.scala:74-88`) — were never written up in `cycle.md`, even
though `integral-cycle.md` §5.6 already states the corresponding claim
("∀k, mod(cycle(k), d) = 0" etc.) as if it were established. Source
check confirmed the gap is real: those three `MemCycle` predicates are
defined purely by counting over the finite base list `L`
(`countModZero(L,d) == n` / `== 0` / strictly between); no Stainless
lemma anywhere states or proves the universal-over-cycle-positions
version `integral-cycle.md` actually uses. `CycleCheckMod.scala`'s ten
lemmas are a different, adjacent thing — they verify the classification
bookkeeping (mutual exclusivity, exhaustiveness, persistence across
independent `checkMod` calls), not this base-list-to-cycle transfer.

Added three new subsections, §5.10 (all-zero), §5.11 (none-zero), §5.12
(some-zero), each proving the transfer as a direct corollary of results
already in the article: §5.10/§5.11 substitute into §5.1's `Cycle_k =
L[k mod n]` (a cycle value is always some value of `L`, so a property
true of every value of `L` is true of every cycle position); §5.12 is
materially different — `someZero` is an existence claim, not universal,
so its proof instead produces two concrete witness positions via §5.2
(`Small Value in Cycle`) rather than substituting into a for-all. Kept
as three separate subsections per article-owner preference (confirmed:
"separated is better"), since §5.12's proof shape genuinely differs from
§5.10/§5.11's, not just its predicate name. Each subsection is explicit
that the transfer step itself is this article's corollary, not a
separate Stainless lemma — avoiding the citation-mismatch anti-pattern
this same audit has been hunting elsewhere. Wired into the §1 and §5
overview bullet lists and the §6 Conclusion's prose count (eight →
eleven properties) and recap math block.

Still open: `integral-cycle.md` §5.6 itself has not been updated yet to
cite these new `cycle.md` sections in place of its current hand-wave
("Ten lemmas in `CycleCheckMod.scala` prove the classification is
correct..." with no derivation) — see Open items below.

## Findings — `articles/chapter4/integral.md`

1. **Manufactured distinction, §4.3 vs §5.3.** "Incremental Change
   Matches List Value" (§4.3) and "Accumulated Delta Consistency" (§5.3)
   present two separately-labeled proofs but cite the identical Scala
   lemma, `IntegralProperties::assertAccDiffMatchesList`, which proves
   both deltas together in one lemma body. The article's own Appendix
   A.6 admits this ("the same function as Appendix A.3 ... used for both
   ... Section 4.3 ... and ... Section 5.3") — but that admission is
   buried in the appendix and never surfaces in the §4.3/§5.3 prose
   itself, so a reader following the main body sees two apparently
   independent verified facts.

2. **Citation mismatch, §4.4 Final Element Equals Full Sum.** The
   article frames this as a trivial corollary of §4.2 (substitute
   `k = n-1` into the §4.2 result). The actually-cited lemma,
   `assertLastEqualsSum`, doesn't call the §4.2 lemma
   (`assertIntegralEqualsSum`) at all — it's proven by a completely
   separate induction on `list.size`. The two-line "proof" shown in the
   article isn't the proof that was actually verified.

**Minor CONTRIBUTING.md checklist items** (not yet given a full pass,
only the mechanical `§N` sweep so far):
- Two bare, unnumbered `### Stainless Verification` headers (after §4.5
  and §4.6), breaking the section-numbering scheme used everywhere else.
- "Unpublished manuscript" in the References section.
- `## 4. Core Integral Properties` opens directly on a bare bullet list
  with no framing sentence (rule 2), unlike §3 and §5 which both open
  with a framing sentence first.
- No Mermaid `classDiagram` — rule 20 explicitly names "integral"
  articles as needing one for their multi-variant definitions
  (Mathematical vs. Recursive in §3, Integral vs. Accumulated-list in
  §5); `grep` confirmed zero `mermaid` blocks in the file.
- Minor: `=` used instead of `:=` in definitional blocks (§3.1, §3.2,
  §5.1), inconsistent with `integral-cycle.md`'s `:=` convention.

**Clean:** no thin/missing proofs otherwise (all Q.E.D. claims have real
worked derivations), no vague backward references, no undefined or
misleading notation, no forward references, no dot-notation leaks,
OBJECTS.md parity is fine.

## Cross-Article Pattern

The "manufactured distinction" finding (two article claims, citing two
differently-named Scala lemmas that are actually thin wrapper aliases
around one shared proof) now shows up in all three chapter-4 articles
audited this session (`integral-cycle.md` §5.1, `cycle.md` §5.9,
`integral.md` §4.3/§5.3). This looks like a recurring habit in how the
codebase names Stainless lemmas — a type-specific or call-site-specific
wrapper around one proof, given its own name — rather than a one-off
mistake. Worth checking chapter 3, 5, and 6 articles for the same
pattern before assuming it's isolated to chapter 4.

## Open — needs prioritization before continuing

`cycle.md` done (see Fixes applied above), not yet committed. Still
awaiting direction on:
1. `integral.md`'s §4.3/§5.3 merge-or-cross-reference, `integral.md`'s
   §4.4 real-proof-vs-claimed-proof fix, and the 5 minor `integral.md`
   checklist items.
2. Whether to sweep chapters 3/5/6 articles for the same
   manufactured-distinction pattern before or after fixing `integral.md`.
3. `integral-cycle.md` §5.6 (Cycle Residue Classification) needs its
   citation updated to point at `cycle.md`'s new §5.10-5.12 instead of
   its current unsupported "Ten lemmas ... prove the classification is
   correct" line — the proof those three sections needed now exists,
   it's just not wired into the article that actually uses it yet.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-21 | Running the same rigor-audit lens (developed live while fixing `integral-cycle.md`) against sibling articles via two parallel background agents, each required to actually open cited Scala source rather than trust docstrings, surfaced the same "manufactured distinction" pattern in both — meaning it's a repo-wide habit, not one article's mistake. | Recorded findings here rather than fixing inline, so fix order and cross-chapter sweep scope can be decided deliberately instead of ad hoc. |
| 2026-08-21 | Before fixing, generalized the 5 anti-patterns into `PROOF_GUIDE.md`'s new "Common Rigor Failures" checklist -- first draft cited the specific files/sections being fixed as examples, which would have gone stale the moment those sections were fixed (caught by the article owner immediately). | Rewrote every anti-pattern with an invented, generic illustrative snippet instead of a live citation, matching the existing "Labeled Blocks Are Not Prose" anti-pattern's style. Durable guide content should never cite specific current article content as its own example. |
| 2026-08-21 | Fixing `cycle.md`'s §3.3 forward reference required more than deleting the bad citation -- the three-way equality claim it was making genuinely needed both dependencies (§3.3's MemCycle≡ModCycle, §4's RecCycle≡ModCycle) to exist first, so the claim itself had to move to the first point in the document where both are actually established (end of §4.2), not just get its citation reworded. | Moved the claim rather than patching its citation, mirroring the `integral-cycle.md` §5.1/§5.5 reorder precedent: a forward reference is often a sign content is in the wrong place, not just wrongly labeled. |
| 2026-08-21 | The "no forward references" lens over-applied to the Mermaid diagram: it sits right after the chapter intro as a structural overview of what's coming, and CONTRIBUTING.md rule 20 explicitly requires "section references on the arrows" for exactly this diagram type -- a forward-pointing label there is the intended design, not a defect. Conflated "formal proof-step citation to unestablished content" (real problem, §3.3's `[By §4]`) with "overview diagram previewing what's ahead" (not a problem) as the same category. | Reverted the diagram labels to their original section numbers. General rule going forward: a checklist item's *purpose* matters, not just its surface pattern -- an anti-pattern check needs to distinguish where a rule requires the exact thing being flagged. |
| 2026-08-21 | Went straight from "this diagram isn't earning its place" to "remove it," when the actual defect was narrower and fixable: both relationship edges used one generic arrow style for two different kinds of facts (proof-based equivalence vs. structural composition). When redesigning the fix, over-trimmed fields using "differs across classes" as the test for "meaningful" -- corrected by the article owner: `values`/`period` are identical across all three classes precisely because they're the shared substrate that makes comparing the classes meaningful in the first place. | Restored the diagram with full field fidelity to the original, changing only the two relationship arrows (`..>` dependency for proven equivalence, `*--` composition for structural wrapping). Lesson for future diagram/content trims: "shared across items" and "not meaningful" are not the same test -- check whether removing something breaks the reader's ability to understand what's being compared, not whether it's repeated. |
