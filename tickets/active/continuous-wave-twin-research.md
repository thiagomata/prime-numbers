# Continuous-wave twin research: first investigation

Created: 2026-10-21
Status: In progress

## START HERE

Save and commit the five new wave-based directions, then perform a first
mathematical investigation of each. Work on feature/imaginay_function and
update existing PR64 with normal pushes. Preserve unrelated working changes.
Mathematical proofs, rather than Stainless implementations, are the deliverable.
User steering: audit attribution in this draft and the earlier continuous-sieve
notes before adding further results. Credit established ingredients at their
point of use; distinguish historical sources from modern expositions.

## Goal

Preserve the proposed research program and produce reviewed exact identities,
useful alternative constructions, and explicit limitations for all five routes.
No claim of a new twin-prime distribution theorem is part of this milestone.

## Strategy

First save an unnumbered candidate note and discovery link in a scoped commit.
Then add one mathematical result at a time to a separate research analysis:
wave folding, activated boundary correction, bounded twin amplitude,
quadratic divisor height, sixfold coordinate reduction, and the boundary
between continuous averages and integer-contact counts. Review every result
before adding the next. Keep proved identities distinct from open estimates.
Current phase: pause further results after the bounded-amplitude proof and
audit the uniform property note, both candidate notes, original construction
notes and animation explanations. Create a claim-by-claim attribution ledger.
Inventory wider article gaps separately; published/article-arXiv edits require
their own scoped parity/build gates and are not silently included here.

## Related Tickets and Sources

- [Continuous construction](../future/continuous-complex-sieve.md): definitions,
  sine equivalence, recurrence/infinite sum, and PR64 history.
- [Uniform animation](uniform-prime-twin-animation.md): finite-window checks and
  narration; no renderer changes planned here.
- [Spectral positional analysis](spectral-positional-filter-analysis-2026-08-18.md):
  existing Fourier and focused-separator program; avoid novelty by name alone.
- [Survival-frontiers article review](survival-frontiers-article-review-2026-09-13.md):
  earlier source/claim-scope audit and persistent review boundaries.
- [Earlier draft review](../../articles/notes/review-draft-articles-2026-08-15.md):
  already called for bibliography and literature positioning; follow through
  claim by claim rather than treating a reference list as sufficient.
- candidates/continuous-contact-research-directions.md: previous four directions.
- properties/sieve-sequence/uniform-continuous-divisor-sieve.md: current math.
- properties/sieve-sequence/fourier-two-gap-correlation-prefix-bound.md and
  localized-two-gap-correlation-fourier-boundary.md: global/local distinction.
- properties/sieve-sequence/weighted-deletion-conservation-law.md: equivalent
  terminal counts do not supply an independent survival estimate.

## Current State

Existing math and candidate notes searched. Five-direction note saved at
candidates/continuous-wave-twin-research.md and linked from candidates/README.md.
Actual text passed mathematical and mechanical review; whitespace checks pass.
Starting-point commit b684c0f7 is pushed to PR64. Research analysis now contains
the folding theorem, exact filter4 activation correction and bounded-amplitude
construction, with independent proof review and whitespace checks passing.
User requested proper credit across drafts; attribution audit is now active.
Attribution ledger saved in properties/sieve-sequence/research/continuous-sieve-attribution.md.
Ledger, uniform note, both candidate notes, wave analysis, original notes,
animation README and narration credits have passed independent source/framing
review. Earlier Holt-Rudd gap-cycle/count research is credited beside the
focused animation and in the ledger. The wider article review is explicitly
queued, not claimed complete. Nine-file documentation checks passed: local
links resolve, fences/whitespace are clean, tracked math/bash blocks are
unchanged, and timed narration is unchanged. The analysis contains
the three reviewed proofs, not a claim of historically new theorems.
The nine-file package is committed and pushed as2bd35cd6. PR64's description
was updated and its exact readback verified; it remains an open draft on
feature/imaginay_function with the inherited-article disclosure preserved.
No runtime gates apply.
Branch is feature/imaginay_function.
Unrelated OBJECTS/index/Scala/Python/cluster/article changes remain untouched.

## Assumptions and Validation

- W_m is the continuous squared roots-of-unity sum; use its finite Fourier
  coefficients to prove folding, including removable points by continuity.
- Keep m>=2 in folding, or explicitly define W_1=1 when needed; shift count
  is a positive integer.
- Activation means raw-wave identities may need boundary corrections. Check
  V_4=W_2 throughout t>=5 and derive the exact defect below that threshold;
  isolated earlier equalities are possible.
- Bounded product uses factors in [0,1]; prove exact binary integer values,
  noninteger exclusion, local finiteness and continuity separately.
- Quadratic height requires odd integer n>=3 for coprime endpoints.
- Sixfold reduction preserves integer pair heights for k>=1; its off-grid
  interpolation is different and omits exceptional twin pair (3,5).
- Quantitative proposals require independent estimates, not positivity of a
  continuous integral or a renamed terminal survivor count.
- Validation is independent Critic proof review, Monitor mechanical review,
  whitespace/link/scope inspection and exact staged-file inspection. No code
  changes or executable instructions are planned; runtime gates do not apply.

## Alternatives and Risks

Numerical sweeps could help falsify conjectures but are unnecessary for exact
finite-sum identities. Begin with proofs. A more attractive continuous curve
can have the same hard arithmetic content. Do not infer integer-contact
existence from continuous area, or claim unrestricted compression from one
translated-wave identity. Do not modify the dirty property registry.

## What is Learned

Exact translated folding is proved by filtering Fourier frequencies; surviving
coefficient normalization is precisely the lower-period wave. This does not
compress every filter in a fixed twin shift. Initial algebra checks support
all five directions' basic constructions.
The filter4 correction is nonnegative, bounded by the coarser wave and zero
throughout t>=5; initial values require it even though isolated early equalities
can occur. The bounded-product direction also has a promising exact local
connection: its vanishing exponent may encode the additive pair-divisor count;
derive this only after establishing the product construction itself.
The bounded-amplitude route has an immediate risk: it is positive at generic
noninteger inputs even in integer windows containing no surviving pair.
This is a research limitation to prove, not a runtime failure.
The wave is a normalized Fejer kernel. Its name and historical source must
appear where it is defined, rather than only citing generic Fourier notes.
A proof derived in this project does not establish historical priority.
Classical divisor and sieve properties need references, while first-discoverer
claims require evidence beyond a modern textbook citation.
Holt and Rudd2014 explicitly give gap-cycle expansion/closure and the
complete-period 2-gap recurrence with factor(q-2). Cite this earlier work
without claiming it covers every custom separator result or proves local
survival. A bibliography's presence alone is not claim-level attribution.

## Failed Paths

No mathematical strategy has failed in this investigation. Known shortcuts requiring audit:
continuous positive area does not automatically imply an integer contact;
unactivated folding cannot be substituted through activation boundaries.
Record exact counterexamples and reopening conditions if these are established.
- Narration-credit append: initial placeholder patch used a nonexistent anchor
  and failed atomically. Read the actual final paragraph and retried only that
  same file with exact context; the approved append succeeded. Retry only with
  freshly read anchors, not guessed prose.
- Source viewing: the web screenshot service could not render the historical
  Fejer PDF, and some other PDF screenshots were unavailable. Historical
  metadata/text and the modern MIT normalization were checked separately.
  Do not claim visual inspection of the original formula. Retry raster
  inspection only with a working PDF viewer; source text remains usable.
- Closure checkpoint: another placeholder patch used a partial line rather
  than the actual wrapped line and failed atomically. Read the exact current
  sections before applying the same-file correction. Do not send placeholder
  patches; retry only with inspected full-line context.

## Open Concerns

No global novelty claim is made. Exact representations may not improve
short-window estimates. Candidate5 remains an independent-bound research
target. The branch contains inherited article commits disclosed in PR64;
this work changes no articles and does not revalidate those inherited edits.
The wider inventory flags gap-dynamics for a targeted Holt-Rudd/source review;
it does not establish that every article or custom lemma lacks attribution.
First discovery of several elementary facts, and priority of the exact folding
form and activated interpolation, remain unassigned.

## Next Action

Continue the broader claim-level article audit, starting with Gap Dynamics'
complete-period counts/recursion versus Holt-Rudd. Any article corrections must
also update its arXiv edition and pass the required build/parity gates.
The original research program remains pending beyond the three proved
sections: local vanishing law, quadratic height, sixfold reduction and
continuous-versus-integer counting. Apply source/priority checks before
presenting these as contributions.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-21 | User authorized saving, committing and investigating five wave-based directions. | Established first-pass milestone and searched existing Fourier/contact research; ticket created before implementation. |
| 2026-10-21 | Saved formulas require explicit domains and activation qualifications; no short-window bound follows yet. | Candidate and discovery link saved/reviewed, whitespace green; exact three-file starting-point commit next. |
| 2026-10-21 | Fourier grouping proves exact wave folding, with no activation assumption hidden in the theorem. | Starting-point commit b684c0f7 pushed; section1 proof saved/reviewed; activation correction next. |
| 2026-10-21 | Activated filter4 folds only after retaining an explicit nonnegative boundary correction. | Section2 proof saved/reviewed; proceed to bounded amplitude before analyzing its local shape. |
| 2026-10-21 | Bounded amplitude has exact binary integer values and locally finite continuation; a proof does not establish novelty. | Section3 passed independent review. User requested attribution across drafts; paused new results for source audit and inline citations. |
| 2026-10-21 | Verified earlier sources include Fejer1900 for the kernel and Holt-Rudd2014 for gap-cycle recursion/counts. Modern references do not establish original discovery. | Saved/reviewed claim-level attribution ledger and uniform-note inline sources; remaining conversation notes next, broader articles queued. |
| 2026-10-21 | Classical ingredients now have point-of-use credit across the current conversation notes; first discovery is not inferred from our proofs. | Updated both candidate notes, analysis, original notes, README and untimed narration credits; independent review and nine-file documentation checks passed. Timed script, formulas, commands and rendered media preserved; exact scoped commit/push next. |
| 2026-10-21 | Note-level attribution pass delivered; wider article attribution and remaining research are distinct unfinished obligations. | Commit2bd35cd6 pushed with matching upstream hash; PR64 exact description readback passed, still an open draft. Recorded source-viewing/atomic-patch limitations; broader claim-level audit is next. |
