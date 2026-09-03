# Review — `articles/draft/exercise-local-safe-window-capacity.md`

**Date:** 2026-09-01
**Reviewed against:** `PROOF_GUIDE.md`, `CONTRIBUTING.md` (26-point checklist), `AGENTS.md`.
**Status:** No changes made — analysis only. This document is a pedagogical
exercise (tasks + solution sketches), not a theorem-presentation article, so
several checklist items built around the three-representation proof format
don't apply the same way; this review notes that explicitly rather than
forcing the comparison.

## Overall assessment

This is a well-posed problem set: four scaffolded tasks build a correct
pigeonhole capacity argument, an optional stronger variant is clearly
separated from the base result, and — unlike when the 2026-08-15 review
assessed this document ("needs solutions") — an Appendix now supplies a
full solution sketch for every task. The one real house-style gap is
mechanical and total: every piece of math in the document is written in
plain ` ```text ` code blocks instead of the ` ```math ` LaTeX blocks
PROOF_GUIDE.md specifies, so none of it renders as math.

## Strengths

- The Appendix ("Solution Sketches") now answers all four tasks plus the
  optional variant — the gap the prior review flagged as the document's
  main weakness appears resolved.
- §5's "Optional Stronger Variant" is clearly marked as requiring an
  additional endpoint-disjointness assumption, and §6 restates the exact
  scope in one sentence ("It does not prove that the local window always
  contains that many 2-gaps. That is a separate abundance question.") —
  honest, precise scope framing.
- §7's "Suggested Final Write-Up" checklist gives a student a concrete
  definition of done, including explicitly asking for "a short note
  explaining why this is a capacity theorem, not a proof of local 2-gap
  abundance" — good instructional design that also reinforces the article
  series' framing-integrity habit.

## Issues

### 1. All math is written in plain ` ```text ` blocks instead of ` ```math ` LaTeX (major, for this genre)

PROOF_GUIDE's "Mathematical Proofs → Format" section specifies LaTeX
notation in ` ```math ` blocks. This document uses ` ```text ` for every
formula — the interval-counting formula, the survival condition, the
notation table in §1, all of §2–§6's definitions and claims, and the
entire Appendix. A `grep` count confirms zero ` ```math ` blocks and zero
`$...$` inline spans anywhere in the file. This was flagged as
cross-cutting issue C5 in the 2026-08-15 review ("draft 2 uses plain
` ```text ` blocks") and has not been addressed since.

**Fix:** convert the formulas to LaTeX in ` ```math ` blocks — e.g.
`R(p, q) = \left\lfloor\frac{q^2-1}{p}\right\rfloor -
\left\lfloor\frac{q-1}{p}\right\rfloor` instead of the current plain-text
`floor((q^2 - 1) / p) - floor((q - 1) / p)`.

### 2. Filename prefix doesn't match either documented draft convention (minor)

CONTRIBUTING's "Draft Articles" section only documents one prefix
(`draft-`). This file uses `exercise-` instead, which is not a documented
category. This is a reasonable genre distinction in practice (the
document is visibly not trying to be a "same structure as formal
articles" draft-article), but nothing in `CONTRIBUTING.md` currently
sanctions a second naming convention, so a reader relying on the written
rule wouldn't know this file exists or what to expect from its name.

**Fix:** either document an `exercise-` naming convention in
`CONTRIBUTING.md` (a couple of sentences describing this genre, its
expected structure, and that AGENTS.md's `three-representations` rule
does not apply to it), or rename the file to fit the existing `draft-`
convention if it's meant to eventually graduate the same way.

## Not an issue for this genre (three-representations rule doesn't apply as written)

This document has no Scala code and no Stainless verification anywhere —
normally a `three-representations` gap, but appropriate here since the
document's stated purpose is a worked exercise for a human reader, not a
formalization target. AGENTS.md's `three-representations` rule is written
for "articles" in the proof-presentation sense; nothing currently carves
out pedagogical exercises, which ties back to issue 2 above (documenting
the genre would also resolve this ambiguity).

## Not an issue (checked, compliant)

- No ticket references — compliant.
- First-person-plural voice ("we will use a capacity bound") — compliant.
- No forward-referencing overclaim; §6 and §7 both state the result's
  limits plainly.

## Suggested priority

1. Convert all math to ` ```math ` LaTeX blocks (issue 1) — the only
   change that materially affects how this document reads next to the
   rest of the series.
2. Decide on and document the `exercise-` genre (issue 2) — a
   `CONTRIBUTING.md` update, not a change to this file itself.

## Property and Model Coverage Audit (2026-09-01)

Useful synthesis suggestions for the eventual instructor's copy — the
exercise's own claims are self-contained and nothing proved is missing
from them.

- The exercise's main bound `G_local > 2·R(p,q)` (and the sharper
  endpoint-disjoint variant `G_local > R(p,q)`) counts **all** multiples
  of `p` in `W` as strikes. The project catalog contains a strictly
  sharper, proved companion:
  `properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md`
  proves `G_local > A(p,q)` with `A(p,q) = π(⌊(q²−1)/p⌋) − π(p−1)` — the
  exact *accepted* strikes, i.e. only multiples whose coprime residue
  actually deletes. Status: proved conditional implication; Stainless
  verification not claimed. The supporting count is
  `properties/sieve-sequence/exact-accepted-local-filter-strikes.md`.
  A short "where this exercise sits" note (in the write-up guidance of
  §8) would let a strong student discover that the pigeonhole bound they
  just proved is not the best known, and see the next rung.
- The endpoint-disjoint optional variant corresponds to the
  strike/destroy bookkeeping in
  `properties/sieve-sequence/endpoint-observable-joint-capacity-envelope.md`
  and the negative result
  `endpoint-capacity-cannot-certify-collision-budget.md`; the latter is a
  good cautionary pointer that endpoint counting alone cannot certify
  survival in general — worth one sentence so students do not
  over-generalize the exercise's conclusion.
