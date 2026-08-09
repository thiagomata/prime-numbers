# Refutation-First Audit for Candidates 20 and 22

**Created:** 2026-08-03
**Updated:** 2026-08-03
**Status:** In progress
**Depends on:** `verify-19-21-escape-wall-2026-07-27.md` (active, algebraic route classification) and `algebraic-conditioned-survival-2026-07-27.md` (active, candidate construction history)

## START HERE

Audit candidate #20 first. Preserve its actual quantifier: it asks for every
layer to satisfy two premises for infinitely many future heads. One failing
layer refutes a universal-all-heads strengthening and disqualifies that head,
but it does not refute the stated infinitely-many-heads candidate. The first
micro-goal is to construct the smallest exact residue histogram violating
`C_r<=N_r+N_r^2/r`, then determine whether that histogram occurs in an actual
conditioned layer. Label an abstract histogram only as an insufficiency
countermodel.

## Related Tickets

- `verify-19-21-escape-wall-2026-07-27.md` — classifies #20 as a noncircular collision component plus a terminal population premise; records prior proof-route failures.
- `algebraic-conditioned-survival-2026-07-27.md` — contains the exact collision identity and the origin of candidates #20--#22.

## Goal

Apply a refutation-first strategy to the strongest remaining algebraic
candidates, starting with #20 and then #22. Produce either a correctly scoped
counterexample, an eventual obstruction that refutes the stated candidate, or
a precise proof that the attempted counterexample only defeats a stronger
universal form or an inference from existing properties.

## Strategy

1. Parse and preserve each candidate's quantifiers before searching.
2. Derive the smallest algebraic violating histogram from the exact residue
   formulas.
3. Test realizability against proved sieve constraints before calling it an
   actual counterexample.
4. If realizable, seek one exact conditioned layer and record which quantified
   form it refutes.
5. To refute an infinitely-many-heads statement, require an eventual
   obstruction covering every sufficiently large head; finite failures are
   evidence only.
6. Move a file to `candidates/refuted/` only after its stated quantifier is
   actually contradicted.

This strategy is preferred over further proof construction because the recent
work exhausted several upper-envelope routes without testing the candidate
statements themselves aggressively enough.

## Current State

- Candidate #20's hypothesis at a successful head is
  `C_r<=N_r+N_r^2/r` and `N_r>2r^2/(r-2)^2` at every layer.
- Its outer quantifier is “for infinitely many future heads,” not “for every
  head.”
- The exact identity `C_r=sum_a c_a^2` makes algebraic countermodels easy, but
  arbitrary histograms need not be realized by conditioned sieve windows.
- A dependency-free exact targeted search found no violating layer for prime
  heads through `Q<=251`. This finite non-witness does not support the
  infinitely-many-heads hypothesis and should not be expanded into a broad
  data campaign.
- The minimal algebraic failures are classified but not yet realized:
  `3+2+1` at `(r,N)=(5,6)`, `2+2` at `(7,4)`, and any repeated class at
  `r>=11,N=3`.
- Candidate #22's main aggregate hypothesis is also quantified over
  infinitely many heads. Its stronger pointwise benchmark already has no
  violation in 1,035 recorded exact layers, so it is not a better immediate
  one-counterexample target.
- Stainless baseline: 30 valid, 0 invalid, 0 unknown. This ticket is initially
  Markdown/algebra only.

## What is Learned

For residue multiplicities `(c_a)`,

```math
C_r-N_r
=
2\sum_a\binom{c_a}{2}.
```

Candidate #20 permits at most `N_r^2/(2r)` unordered same-class pairs. Hence:

- at `(r,N)=(5,6)`, at most three pairs are allowed; partition `3+2+1` has
  four and is the first violation;
- at `(7,4)`, at most one pair is allowed; partition `2+2` has two and
  violates;
- at `r>=11,N=3`, fewer than one pair is allowed; any repeated residue
  violates.

Same-residue starts are separated by multiples of `6r`, so basic spacing does
not prohibit these patterns inside the square window. This is not yet an
actual conditioned-layer counterexample because the full survivor set cannot
be chosen arbitrarily.

The first refutation ranking was too optimistic: neither #20 as stated nor
#22's main aggregate candidate is refuted by one failed head. A finite witness
would still be useful against an all-heads strengthening, but full refutation
requires an eventual obstruction. The next refutation target should therefore
be chosen by screening the remaining candidates for genuinely universal
quantifiers.

## Expected State

Candidate #20 and then #22 have explicit refutation verdicts with one of these
labels:

1. **Refuted as stated** — its full quantifier is contradicted.
2. **Universal strengthening refuted** — an exact actual layer fails, but the
   infinitely-many-heads form remains viable.
3. **Known-properties implication refuted** — an algebraic countermodel
   satisfies the retained constraints but is not known realizable.
4. **Survives audit** — no sound negative construction was found; the exact
   remaining falsifier is stated.

Every failed construction records why it failed and what would make it
relevant.

## Approaches Considered

### Minimal Collision Histogram

**Status:** RECOMMENDED

Use `C_r=sum_a c_a^2`. For the candidate's smallest allowed populations,
classify all collision partitions and identify the first violation. Then test
the proved spacing and nested-survivor constraints.

**Strengths:** Exact, algebraic, and immediately falsifiable.
**Risks:** The violating histogram may not be realizable by an actual sieve
layer.
**Fallback:** Search an exact finite conditioned layer only after the
realizability constraints are understood.

### Broad Data Sweep

**Status:** DEFERRED

Search many heads for failures.

**Strengths:** May quickly find an actual failing head.
**Risks:** Cannot refute an infinitely-many-heads claim and can obscure the
structural reason for failure.
**Fallback:** Use only as a targeted witness search for an algebraically
identified pattern.

### Eventual Obstruction

**Status:** UNTESTED

Prove that every sufficiently large head contains at least one layer whose
collision histogram violates #20.

**Strengths:** Would refute candidate #20 as stated.
**Risks:** Likely requires new distribution information at least as difficult
as the original candidate.
**Fallback:** Preserve exact universal-form counterexamples without
overclaiming.

## Assumptions

- `C_r=sum_a c_a^2` counts ordered same-residue pairs.
- Residue counts are nonnegative integers summing to `N_r`.
- Actual-layer claims must use the repository's exact conditioned-window
definitions, including complete 2-gap endpoints.
- A finite failed head does not refute an infinitely-many-heads statement.

## Risks

- Confusing a countermodel to known constraints with an actual sieve
  counterexample.
- Repeating the earlier mistake that one failure refutes an existential
  infinitely-many statement.
- Quietly changing the candidate to a universal form because that form is
  easier to falsify.
- Collecting broad empirical evidence that cannot settle the quantifier.

## Validation

- Check every claimed histogram directly in `C_r=sum_a c_a^2`.
- For an actual witness, independently recompute `N_r`, all residue counts,
  and `C_r` from the exact survivor set.
- State the exact quantified form contradicted.
- Markdown-only work needs `git diff --check`; code changes, if any, require
  the chapter-by-chapter verification sequence.

## Failed Paths

- **Reuse `lib_lineage.py` from the system Python:** the targeted witness
  search did not start because that interpreter lacks NumPy. No candidate
  result was produced. Retry with a standard-library exact implementation or
  the configured bundled Python runtime; do not treat this as a mathematical
  failure.
- **Expand finite #20/#22 witness searches as a route to full refutation:**
  blocked by quantifier. Any finite collection of failed heads is compatible
  with “infinitely many successful heads.” Retry only for a targeted witness
  to a separately named universal strengthening, not as a refutation of the
  stated candidates.

## Open Concerns

- Candidate #20's stated outer quantifier makes full refutation substantially
  harder than refuting a universal strengthening.
- Candidate #22 likely has a similar outer quantifier and must be parsed
  independently before transferring any conclusion.

## Next Action

Stop and surface the quantifier correction. Recommended next ticket: screen
all remaining candidates by outer quantifier and select the strongest
genuinely universal statement for an algebraic counterexample attack. Keep
#20's eventual-obstruction route open, but do not spend more effort on finite
witness searches unless a universal strengthening is explicitly selected.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-03 | Ticket created after the user requested more effort on candidate refutation. Candidate #20 is quantified over infinitely many successful heads, so one failed layer refutes only a universal strengthening or one head. | Derive the minimal violating histograms algebraically before seeking actual witnesses. |
| 2026-08-03 | Minimal violations are `3+2+1` for `(5,6)`, `2+2` for `(7,4)`, and any repeated class for `r>=11,N=3`. Basic `6r` spacing does not exclude them, but arbitrary histograms are not actual sieve layers. | Search exact conditioned layers for a targeted witness and independently verify its histogram. |
| 2026-08-03 | The first targeted search did not execute because system Python lacks NumPy; no layer was tested and no file changed. | Retry once with a dependency-free exact implementation. |
| 2026-08-03 | A dependency-free exact search found no #20 violation through prime heads `Q<=251`. Candidate #22 is likewise infinitely quantified and its pointwise strengthening already has 1,035 recorded nonviolating layers. Finite searches cannot refute either main candidate. | Stop at the quantifier boundary and recommend screening the remaining candidates for genuinely universal, one-counterexample-falsifiable statements. |
