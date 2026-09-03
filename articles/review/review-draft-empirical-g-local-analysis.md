# Review — `articles/draft/draft-empirical-g-local-analysis.md`

**Date:** 2026-09-01
**Reviewed against:** `PROOF_GUIDE.md`, `CONTRIBUTING.md` (26-point checklist), `AGENTS.md`.
**Status:** No changes made — analysis only. This document is a self-declared
superseded empirical audit record, not a proof article; several checklist
items don't map cleanly onto that genre, which this review notes rather than
forcing.

## Overall assessment

This document is unusually honest about its own obsolescence — "superseded"
appears in the title, the status line, and repeatedly through the body, and
§5.3 states in bold that "this historical evidence is not a formal proof and
does not apply to the canonical `[q,q^2)` experiment." That labeling
discipline is real and worth preserving. Against the repository's own
house-style checklist, though, two things stand out: its two summary tables
carry a `Status` column of bracketed `[Empirical]` markers, which is
exactly the pattern checklist rule 24 prohibits, and — now that the content
is permanently superseded rather than actively drafted — it sits in
`articles/draft/` even though `CONTRIBUTING.md`'s own documented directory
structure names an `articles/deprecated/` location for exactly this kind of
material, a folder that does not currently exist in the repository.

## Strengths

- The status line, abstract, and §5.3 all independently state the same
  scope boundary — this data doesn't transfer to the canonical experiment —
  so a reader can't miss it by skipping any one section.
- §4.3 documents its own past mistake in the open: "An earlier version of
  this section compared `G_local` against the per-coprime density... that
  comparison used the wrong denominator... and the excess was an artifact
  of the error." Leaving a corrected error visible, rather than silently
  fixing it, is unusually good research hygiene.
- §4.6's cross-validation against an independently generated Spark dataset
  gives an exact-match sanity check (`G_2(31) = 214,708,725` predicted and
  counted) before drawing any conclusion from it — real, checkable
  evidence rather than an assertion.

## Issues

### 1. Both summary tables use a `Status` column of bracketed markers (moderate)

Checklist rule 24: "Property summary tables contain only verified facts...
Do not include `[Verified]`, `[Open]`, or `[Unverified]` markers in table
columns." The "Property Index" table (lines 29–38) and the "Empirical
Findings" table (§5.1, lines 304–308) both carry a `Status` column filled
with `[Empirical — ...]` markers on every row — the literal pattern the
rule names. The genre here is different from a theorem-summary table (this
is explicitly an audit record, and the bracketed status is arguably the
whole point of the table), but the rule as written doesn't carve out an
exception for that, and the repeated bracket-per-row format is visually
identical to what the rule is written to prevent elsewhere in the series.

**Fix:** if this document is kept, either drop the `Status` column (the
surrounding prose and the document-level status line already establish
that everything here is empirical/superseded) or replace the per-row
bracket with a single sentence above the table stating the blanket status
once, matching how VOCABULARY.md's Evidence and Proof Status guidance asks
other articles to state status once rather than per line.

### 2. Superseded content sits in `articles/draft/`, not `articles/deprecated/` (moderate, structural)

CONTRIBUTING.md's Directory Structure section lists `articles/deprecated/`
as a sibling of `articles/chapter2/` through `chapter6/` and
`articles/learnings/`. That folder does not currently exist anywhere in
the repository (`ls articles/deprecated` finds nothing), so the documented
convention has never actually been used — but this file, which
self-identifies as `[Superseded Draft]` in its own title and status line,
is the clearest candidate for it that exists today. Leaving it in
`articles/draft/` groups it with material that is still active and
evolving (`draft-relaxed-almost-prime-sieve-sequence.md`,
`draft-sieve-gap-survival-math.md`), which is a different status than
"superseded and pending physical removal."

**Fix:** create `articles/deprecated/` and move this file there (updating
the two other drafts and any learnings notes that link to it), or, if the
maintainers decide the old runner and dataset really are headed for
deletion soon per the "pending physical removal" note already in the file,
skip the move and delete both together instead.

### 3. Math is written as `$...$`/`$$...$$`, not fenced ` ```math ` blocks (minor)

Six `$$...$$` display blocks and numerous inline `$...$` spans appear
throughout; there are no fenced ` ```math ` blocks. This is the same
formatting inconsistency flagged as cross-cutting issue C5 in the
2026-08-15 review and confirmed unresolved in this pass — consistent with
the pattern found in `integral.md` (46 `$$` blocks) and
`draft-empirical-g-local-analysis.md`'s sibling drafts.

**Fix:** low priority given issue 2 may make this file's location, not its
formatting, moot — but if the file is kept and edited again, convert to
` ```math ` for consistency with the rest of the series.

## Not an issue (checked, compliant)

- No ticket references — compliant.
- Framing integrity — the document consistently under-claims rather than
  over-claims its own evidentiary weight.
- `@extern`, not-Stainless-verified status of the historical Scala
  functions is stated plainly (§2.1, §2.2, §5.3) rather than glossed over.

## Suggested priority

1. Resolve the directory question (issue 2) first — it affects whether
   issues 1 and 3 are worth fixing in place at all.
2. If the file stays, drop or simplify the two `Status` columns (issue 1).
3. Formatting conversion (issue 3) is lowest priority given the file's
   likely disposition.

## Property and Model Coverage Audit (2026-09-01)

Superseded draft — recommendation is **archival notes only**, no new
sections.

- The document's central inequality `G_local(p) > p−1` is exactly item 10
  of the ten-property snapshot in
  `articles/learnings/learnings-capacity-argument.md` §16 — the single
  *open* property among the ten (empirically holding from `p = 37`
  onward, which is this draft's crossover finding). An archival note
  should state that this draft is the empirical record of that open item,
  linking both ways.
- The successor empirical body is
  `properties/sieve-sequence/realized-filter-adversariality-score.md`
  (186 audited populations, proved ceilings plus finite-population
  observations). If the draft is kept as a historical record rather than
  deleted with its runner, it should point readers there as the current
  empirical work.
- No proved property note is missing from this draft's *claims*: its
  statements are all `[Empirical]` by design, so there is nothing proved
  elsewhere that it silently omits. The audit found no false-positive
  additions.
