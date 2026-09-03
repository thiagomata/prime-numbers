# Review — `articles/draft/draft-relaxed-almost-prime-sieve-sequence.md`

**Date:** 2026-09-01
**Reviewed against:** `PROOF_GUIDE.md`, `CONTRIBUTING.md` (26-point checklist), `AGENTS.md`.
**Status:** No changes made — analysis only. This draft was reviewed twice
before: the 2026-08-15 scientific-quality review and a further pass recorded
in `articles/learnings/reviewer-notes-aug-2026.md`. This review checks it
against the repository's own house-style checklist and notes what those
earlier passes already fixed.

## Overall assessment

This is the most mature of the six drafts reviewed. Two of the 2026-08-15
review's headline complaints are visibly resolved: §1.2 ("Relation to
Known Results") now cites Chen, Halberstam–Richert, Iwaniec–Kowalski, and
Friedlander–Iwaniec and states precisely what is standard sieve theory
versus project-specific, closing the "zero external citations" gap that
review called the field's single largest weakness; and all five theorems
are now numbered ("Theorem 1" through "Theorem 5"), closing the
"no theorem numbering" gap. Against the repository's own checklist, two
things remain: the same "mathematical proof is maintained in
`properties/`/`candidates/`" citation pattern found in `gap-dynamics.md`
recurs here at smaller scale, and every one of the five theorems restates
its own quantifier scope twice in a row — once in the bold theorem
statement, once in the paragraph immediately after — which reads like
duplicated drafting history rather than an intentional structure.

## Strengths

- §1.2 distinguishes "what is standard" (the Type-I/Type-II framework,
  Chen's theorem) from "what is project-specific" (the square-safe
  interval, the nested wheels, the modulo-3 obstruction) in one paragraph
  — a real literature-positioning section, not a citation dump.
- §9 (Claim Boundary) gives a clean two-list accounting of what is and
  isn't proved, and §7's refutation is explicit that it "does not refute
  relaxed-weight positivity... only the proof shortcut" — precise,
  non-overclaiming scope statements throughout.
- Appendix A's Stainless-status column is honest and consistent
  ("Pending" for every open item, "Not applicable to a false statement"
  for the refuted one) — no property is described as verified when it
  isn't.
- The refutation in §7 is a real counterexample with an exact computation
  (the modulo-3 character correlation), not an appeal to intuition.

## Issues

### 1. `properties/`/`candidates/` notes are cited as "where the proof is maintained" (moderate)

The same pattern flagged as a major issue in `gap-dynamics.md` recurs here,
at much smaller scale (roughly six instances rather than 120): each of the
five theorems closes with a sentence like "The complete mathematical proof
is maintained in [Relaxed Almost-Prime Weight Has An Exact Divisor Local
Factor](properties/sieve-sequence/...)" (§4, similarly §3, §5, §6, §7), and
Appendix A's "Canonical evidence" column points to `candidates/` and
`properties/` notes as the authority for each result. PROOF_GUIDE's
"Mathematical Authority and Article Boundaries" section does not permit
`properties/` or `candidates/` to be cited as authority even when, as here,
the full derivation is also present in the article body — the citation
should point there as supplementary provenance, not as where the proof
"is maintained."

**Fix:** reword the five closing citations from "is maintained in" to
something like "is also recorded, with the same derivation, in," and
adjust Appendix A's column header from "Canonical evidence" to something
that doesn't imply the linked note is the authority (e.g. "Cross-reference").

### 2. Every theorem restates its own quantifier scope twice in a row (minor, but systemic)

For each of the five theorems, the bold theorem statement's opening clause
and the very next paragraph's opening sentence say nearly the same thing
about the theorem's scope, word for word:

> **Theorem 1 (Relaxed positivity implies prime-plus-$P_2$ production).**
> For every fixed exponent $1/3<\alpha<1/2$ and every sufficiently large
> prime future head $Q$, over the integers in that head's square-safe
> interval weighted by $a_Q$: [...]
>
> We prove this for every fixed exponent $1/3<\alpha<1/2$ and every
> sufficiently large prime future head $Q$, over the integers in that
> head's square-safe interval weighted by $a_Q$. [...]

The same doubled pattern recurs for Theorem 2 (§4), Theorem 3 (§5), and
Theorem 4 (§6). This reads like a population/scope/quantifier drafting
checklist (per VOCABULARY.md's "Minimum Complete Statement") that got
written once as the formal theorem statement and then written again as
connecting prose, without the second copy being trimmed once the first was
finalized — the same kind of duplicated-drafting-history PROOF_GUIDE's
Voice-and-Style section asks authors to remove ("Preserve depth without
preserving drafting history... Remove duplicated status notes").

**Fix:** in each theorem's follow-up paragraph, drop the repeated scope
clause and start directly with the proof's first substantive step (most of
these paragraphs already transition into real content — "Suppose
$a_Q(n)=1$...", "Before studying divisor averages..." — right after the
redundant sentence).

## Minor observations

- `\blacksquare` is never used (all closings are `[Q.E.D.]` only) — the
  same gap found in four other articles/drafts reviewed so far.
- The References section splits into an unnumbered internal list (repo
  cross-references, items 1–6, linked directly rather than cited by
  bracket number) and a properly bracket-cited external list (items
  7–10). This two-tier structure is coherent and each half is internally
  consistent, so it isn't flagged as a defect — noted here only because a
  reader skimming the numbered list might expect items 1–6 to be cited
  the same way 7–10 are.

## Not an issue (checked, compliant)

- Theorem numbering (issue from the 2026-08-15 review) — fixed.
- External literature engagement (issue from the 2026-08-15 review) —
  fixed.
- Notation consistency (`$[Q,Q^2)$` throughout, no drift) — compliant.
- All math in fenced ` ```math ` blocks — compliant.
- Appendix A's status table is a dedicated verification-status audit, the
  same genre judged compliant in the `gap-dynamics.md` review — not a
  rule-24 violation.
- No ticket references — compliant.

## Suggested priority

1. Reword the `properties/`/`candidates/` citations (issue 1) — the same
   fix pattern as `gap-dynamics.md`, much smaller scope here.
2. Trim the five duplicated scope-restatement paragraphs (issue 2) —
   mechanical, improves readability without touching the mathematics.
3. Minor observations are optional polish.

## Property and Model Coverage Audit (2026-09-01)

Cross-checked the five theorems against the `properties/sieve-sequence/`
catalog, `candidates/`, and `articles/learnings/learnings-capacity-argument.md`.

- **Parity is adequate — no required additions.** The draft already cites
  the exact property notes that carry its mathematics
  (`relaxed-almost-prime-divisor-local-factor.md`,
  `relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md`,
  `relaxed-almost-prime-bilinear-character-obstruction.md`), the refuted
  route (`candidates/refuted/relaxed-weight-scalar-density-type-ii.md`),
  and candidate #25 (`candidates/chen-type-almost-prime-survivor.md`,
  correctly tagged EXTERNALLY KNOWN; METHOD-SPECIFIC PROOF OPEN).
  Appendix A preserves the mathematically-proved / not-Stainless-verified
  status of every theorem.
- **Optional boundary synthesis.** §8 ("The Correct Remaining Program")
  describes the remaining Type-I/Type-II cancellation work. This is the
  same boundary `learnings-capacity-argument.md` §15 records as the
  recommendation to "stop optimizing the unsigned capacity envelope; go
  signed," and §9 documents four discarded approaches that motivate it. A
  single cross-reference in §8 would anchor the draft's program in the
  project's recorded proved/open boundary — Related-Work context only,
  not proof authority (and wording must stay "also recorded in," per
  issue 1).
- Confirmed the draft's honest negative: it correctly does **not** cite
  any unsigned capacity-envelope note as support, since those envelopes
  are the analysis family §15 recommends moving away from.

### Source-Check Adjudication (2026-09-01)

**Confirmed:** no additional proved property or model needs to be added for
the draft's stated relaxed almost-prime program. Its four relevant property
notes, Chen-type conditional implication, and refuted scalar Type-II route
are already represented with their non-Stainless status preserved.

**Required exact-case completion:** in the divisor-local-factor theorem, the
statement quantifies over every $m \ge 1$, but the density/remainder notation
is introduced only after the coprime branch. Add the convention
$\rho(m)=E_m=0$ whenever $\gcd(m,W)>1$, immediately after the vanishing case.
That is the convention proved in the cited divisor-local-factor record and
makes the theorem globally exact rather than branch-dependent.
