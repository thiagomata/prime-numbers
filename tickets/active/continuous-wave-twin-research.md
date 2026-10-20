# Continuous-wave twin research: first investigation

Created: 2026-10-21
Status: In progress

## START HERE

Save and commit the five new wave-based directions, then perform a first
mathematical investigation of each. Work on feature/imaginay_function and
update existing PR64 with normal pushes. Preserve unrelated working changes.
Mathematical proofs, rather than Stainless implementations, are the deliverable.

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

## Related Tickets and Sources

- [Continuous construction](../future/continuous-complex-sieve.md): definitions,
  sine equivalence, recurrence/infinite sum, and PR64 history.
- [Uniform animation](uniform-prime-twin-animation.md): finite-window checks and
  narration; no renderer changes planned here.
- [Spectral positional analysis](spectral-positional-filter-analysis-2026-08-18.md):
  existing Fourier and focused-separator program; avoid novelty by name alone.
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
No runtime gates apply. Branch is feature/imaginay_function, PR64 already exists.
Unrelated OBJECTS/index/Scala/Python/cluster/article changes remain untouched.

## Assumptions and Validation

- W_m is the continuous squared roots-of-unity sum; use its finite Fourier
  coefficients to prove folding, including removable points by continuity.
- Keep m>=2 in folding, or explicitly define W_1=1 when needed; shift count
  is a positive integer.
- Activation means raw-wave identities may need boundary corrections. Check
  V_4=W_2 only at t>=5 and derive the exact defect below that threshold.
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

Initial algebra checks support all five directions' basic constructions.
The bounded-amplitude route has an immediate risk: it is positive at generic
noninteger inputs even in integer windows containing no surviving pair.
This is a research limitation to prove, not a runtime failure.

## Failed Paths

None attempted in this investigation. Known shortcuts requiring audit:
continuous positive area does not automatically imply an integer contact;
unactivated folding cannot be substituted through activation boundaries.
Record exact counterexamples and reopening conditions if these are established.

## Open Concerns

No global novelty claim is made. Exact representations may not improve
short-window estimates. Candidate5 remains an independent-bound research
target. The branch contains inherited article commits disclosed in PR64;
this work changes no articles and does not revalidate those inherited edits.

## Next Action

Commit only candidates/continuous-wave-twin-research.md, candidates/README.md
and this ticket after inspecting the staged paths. Then start the wave-folding
proof in a separate research note. Push normally to update existing PR64.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-21 | User authorized saving, committing and investigating five wave-based directions. | Established first-pass milestone and searched existing Fourier/contact research; ticket created before implementation. |
| 2026-10-21 | Saved formulas require explicit domains and activation qualifications; no short-window bound follows yet. | Candidate and discovery link saved/reviewed, whitespace green; exact three-file starting-point commit next. |
