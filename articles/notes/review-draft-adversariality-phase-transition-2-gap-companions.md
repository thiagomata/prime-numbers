# Review — `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md`

**Date:** 2026-09-01
**Reviewed against:** `PROOF_GUIDE.md`, `CONTRIBUTING.md` (26-point checklist), `AGENTS.md`.
**Status:** No changes made — analysis only. This is the largest document
reviewed (2982 lines) and was already assessed for mathematical rigor,
premise load, and statistical soundness by the 2026-08-15 review ("Most
substantial; heavy premise load, duplicated results, unstated
Poisson/negative-association step"); this review focuses on what that pass
didn't specifically check — the repository's own house-style checklist —
rather than re-deriving the probability theory.

## Overall assessment

On the mechanics this checklist cares about, this draft is in noticeably
better shape than `gap-dynamics.md` or the relaxed almost-prime draft: it
never cites `properties/` or `candidates/` notes as mathematical authority
(the two `candidates/` hits found are data-file paths, not citations to
`.md` notes), it uses fenced ` ```math ` blocks exclusively with zero raw
`$$`, and its Limitations (§9) and Conclusion (§10) sections are among the
most carefully scoped in the whole set — §10 closes with an explicit,
named "Deterministic Discrepancy Bound" stating exactly what would need to
be proved for the real sieve to inherit the companion-process result, and
states plainly "This discrepancy condition... is not proved here for the
real CRT sieve." The one systemic mechanical gap is the same one found in
`sieve-sequence.md`, at larger scale: every internal section reference in
this 2982-line document is bare text, never a Markdown link.

## Strengths

- Zero citations to `properties/` or `candidates/` as mathematical
  authority — every theorem's proof lives in the article body itself,
  correctly matching PROOF_GUIDE's "Mathematical Authority and Article
  Boundaries" rule.
- §9 (Limitations) is unusually thorough and specific: it names exactly
  which premise each of the four major theorems needs (spatial uniformity,
  quadratic protective supply, cumulative quota conditions, group-
  exchangeable allocation), rather than a generic disclaimer.
- §10's closing "Deterministic Discrepancy Bound" gives a precise, falsifiable
  transfer criterion to the real sieve and states its own unproved status in
  one sentence — a model instance of `framing-integrity` for a document this
  large.
- All math uses fenced ` ```math ` blocks; zero raw `$$` — fully compliant
  with the house convention, unlike `integral.md` and
  `draft-empirical-g-local-analysis.md`.
- View A/View B's figure discussion (§1) states explicitly what each
  visualization does and does not support ("These figures provide
  empirical context for the placement problem; neither is evidence for the
  companion-model survival thresholds derived below") before showing
  either image — evidence framed correctly ahead of the reader seeing it.

## Issues

### 1. No internal section reference is a Markdown link (major)

The same gap found in `sieve-sequence.md` recurs here at much larger
scale: a count finds 32 occurrences of `§N`/`§N.M` in running prose (e.g.
"defined fully in §5.2," "the same caveat as §9 applies," "the theorem in
§5 isolates," "governed by §5.1 instead," "the empirical comparison in
§8.1 is finite") and zero occurrences of the `[§N](#anchor)` link form —
checklist rule 26's exact requirement. The article's cross-*article*
citations (e.g. "[Gap Dynamics §6.1](https://github.com/...)") are
correctly formatted as full links; only the internal, same-document
references are bare text. §1's own "We establish:" bullet list (the
intro's compact group list, checklist rule 1) also carries no section
numbers or links at all on any of its five items.

**Fix:** convert all 32 internal `§N` references to `[§N](#anchor)`, and
add section pointers to §1's five-item bullet list.

## Minor observations

- Reference `[2]` (line 2593–2595) titles `gap-dynamics.md` as "Structural
  Properties and **Open** Boundaries of 2-Gaps in Sieve Sequences." The
  article's current title (confirmed by reading `gap-dynamics.md` directly)
  is "Structural Properties and **Signed** Boundaries of 2-Gaps in Sieve
  Sequences." This reads as a stale citation left over from an earlier
  title of the target article, the same kind of drift found as a dead link
  in `draft-sieve-gap-survival-math.md`'s reference to `gap-dynamics-v2.md`.
- `\blacksquare` appears only twice against 19 `[Q.E.D.]` occurrences —
  not the total absence found in several other articles/drafts, but still
  overwhelmingly `[Q.E.D.]`-only.

## Not an issue (checked, compliant)

- No citations to `properties/` or `candidates/` as authority — compliant,
  a contrast with `gap-dynamics.md` and the relaxed almost-prime draft.
- All math in fenced ` ```math ` blocks, zero raw `$$` — compliant.
- No ticket references — compliant.
- No labeled-block anti-pattern (`**Population:**`, `**Status:**`, etc.
  used as a repeated per-claim template) — the one `**Status:**` line is
  the front-matter status declaration, not a repeated in-body pattern.
- §9 and §10 both state limitations and open premises precisely rather
  than apologizing after every claim — compliant with VOCABULARY.md's
  "state status once" guidance.

## Suggested priority

1. Link the 32 internal section references and the intro's bullet list
   (issue 1) — mechanical, the same fix already recommended for
   `sieve-sequence.md`.
2. Fix reference `[2]`'s stale title (minor observation) — one-line edit.
3. For the deeper mathematical concerns (premise load, duplicated results,
   the unstated Poisson/negative-association step), see the 2026-08-15
   review, which covers that ground and was not re-derived here.

## Property and Model Coverage Audit (2026-09-01)

Cross-checked the draft against the `companions/` model family and the
`properties/sieve-sequence/` catalog.

1. **Required cross-references (companions/properties).** The six proved
   companion lemmas in `companions/properties/` —
   `cumulative-local-hazard-law.md`, `fixed-factor-survival.md`,
   `global-persistence-independence.md`,
   `local-survivor-allocation-range.md`,
   `logarithmic-worsening-thresholds.md`, and
   `position-blind-index-spectrum.md` — all appear to correspond to results
   proved in the draft's prose and Appendix A records (§3.1 global
   persistence independent of allocation; §3.3/§3.4 hazard law and
   fixed-factor frontier; §3.5 logarithmic thresholds; §5 allocation
   range; §6 position-blind spectrum). The draft cites none of them by
   path. Each appendix proof record should carry an explicit
   "also recorded in `companions/properties/...`" pointer so the two
   bodies cannot drift apart silently — same fix pattern as the relaxed
   almost-prime draft's issue 1. The open shared transfer obligation
   `companions/candidates/crt-coupled-real-sieve-transfer.md` should
   likewise be cited from §10 (Relation to the Real Sieve), which states
   the same gap in different words.
2. **Flag (unindexed model).** A fifth companion folder,
   `companions/uniform-digit-2-gap/`, exists on disk but is indexed in
   neither `companions/README.md` (which lists four models) nor this
   draft. Either it is work-in-progress that should be indexed when
   ready, or it should not exist unindexed — this review takes no
   position, but the discrepancy should be resolved before publication.
3. **Optional synthesis.** §8.1's measured adversariality (`w ≤ 0.0523`,
   ratio 0.967 to random) is the empirical counterpart of
   `properties/sieve-sequence/realized-filter-adversariality-score.md`
   (empirical/finite-population, 186 audited populations, explicitly "not
   a deterministic-randomness theorem"). A cross-reference would let the
   reader see the real-sieve measurement behind the companion-model
   `w_r` parameter; keep it as Related-Work context, not as support for
   any theorem.

### Source-Check Adjudication (2026-09-01)

**Confirmed:** the draft already covers the relevant shared, balanced,
protective, and exact-quota companion results. The body and Appendix A supply
the mathematics, so companion-note links are optional provenance, not missing
mathematical authority; they must not replace the article's derivations.

**Suggested optional negative-control model:** add a short limitation or
related-work paragraph about the proved
`companions/uniform-digit-2-gap/properties/digit-dust-collapse-and-clustering.md`.
It gives a deterministic countermodel with balanced-style count laws but
period-fraction gaps, demonstrating that global counts and collapse do not
force local occupancy. Keep it outside the balanced companion phase diagram:
it is a separate, mathematically proved model and is not a theorem about the
real sieve.

**Optional empirical method:** the position-blind index-spectrum result can
be mentioned only as a proposed diagnostic for §8's real-sieve comparison. Its
flat-spectrum conclusion is an expectation over position-blind placements, not
evidence that CRT strikes are random.
