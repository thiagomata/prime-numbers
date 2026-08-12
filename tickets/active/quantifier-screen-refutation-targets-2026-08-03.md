# Quantifier Screen for Refutation Targets

**Created:** 2026-08-03
**Updated:** 2026-08-05
**Status:** Complete
**Depends on:** `refute-candidates-20-22-2026-08-03.md` (active, quantifier correction)

## START HERE

Classify each non-refuted numbered candidate by its outer quantifier before
attempting a counterexample. Prefer a genuinely universal arithmetic subclaim,
where one exact witness is decisive. The completed screen finds no live
numbered candidate whose main stated hypothesis is both concrete and
refutable by one finite witness. Refutation-first work should therefore target
explicitly stated universal auxiliary laws, without silently strengthening a
numbered candidate's quantifier.

## Related Tickets

- `refute-candidates-20-22-2026-08-03.md` — proves that finite failed heads
  cannot refute #20 or #22 because their main claims are infinitely quantified.
- `develop-admissible-shot-spacing-candidate-2026-07-27.md` — develops
  candidate #15 and records its verified finite spacing values.
- `prove-hereditary-shot-spacing-2026-07-23.md` — contains the earlier exact
  shot-spacing program and its recurrence history.
- `verify-19-21-escape-wall-2026-07-27.md` — classifies candidates #19--#24 and
  their proof-route boundaries.

## Goal

Produce a quantifier-accurate ranking of the remaining candidate statements
for refutation work, then complete a candidate-by-candidate closure audit for
a stable research handoff. For every live candidate, identify the strongest
important route already investigated, the decisive obstruction or surviving
lemma, and the exact new ingredient needed for further progress. Do not relabel
an infinitely-often candidate as universal merely to make it falsifiable, and
do not call the investigation complete while a materially distinct algebraic
route remains unexamined without being named.

## Strategy

1. Read each candidate's actual hypothesis and outer quantifier.
2. Classify it as universal, eventual, infinitely-often, existential per head,
   or a compound of these.
3. Separate the numbered candidate from stronger universal subclaims in the
   same file.
4. Rank universal statements by exact computability and counterexample cost.
5. Attack the highest-ranked statement algebraically or by an exact finite
   certificate.
6. Move a numbered candidate to `candidates/refuted/` only if its stated outer
   quantifier is contradicted; otherwise archive the refuted subclaim with an
   explicit scope label.
7. Build a closure matrix for every live candidate: status, best established
   result, failed/exhausted routes, missing ingredient, and priority for more
   investigation.
8. Cross-check the matrix against active/done tickets, permanent properties,
   and the catalog. Promote any load-bearing conclusion that currently lives
   only in a ticket.

## Current State

- The numbered catalog has 25 candidates; most prime-producing hypotheses ask
  for success at infinitely many heads or transitions.
- Candidate #20 and #22 are not suitable one-witness targets in their main
  forms.
- The `candidates/refuted/` directory now stores four refuted auxiliary
  laws/strategies, not four refuted numbered candidates. Together with
  candidate #3's all-transitions failure, the repository has five scoped
  negative results.
- Candidate #15 proves exact finite spacing values through `k=14`, but
  explicitly asserts no recurrence equality or asymptotic formula. Refuting a
  guessed next value would revise the research program, not refute #15.
- Candidates #1--#11, #14, and #16--#25 use infinitely-often main forms in the
  catalog. Some files contain stronger auxiliary targets, but a finite failure
  of one such target does not refute the numbered main hypothesis.
- Candidates #12 and #13 quantify over all transitions only through unspecified
  error terms `E_p(J,w)` and `eta_p`. Until a numerical bound or fixed error
  family is stated, neither is a concrete one-counterexample target.
- Consequently, no live numbered candidate's main stated hypothesis is
  presently refutable by one finite counterexample.
- The closure audit found an unpromoted exact refutation around candidate #4:
  at `Q=101`, filter `r=23`, the full-period cyclic destroyed-start run is `3`
  (`M_r=9699690`, `T_r=1658880`). Thus the concrete universal shortcut
  `R<=2` is false even though #4's infinitely-many combined condition remains
  open.
- Candidate #25 had conflated two claims and is now corrected. Its bare
  existence statement follows externally from Chen's theorem plus Bertrand's
  postulate: for each
  sufficiently large Chen prime `p`, choose a prime head
  `sqrt(p)<Q<2sqrt(p)<p`, giving `p in [Q,Q^2)`. The genuinely open project
  claim is positivity proved through the specified relaxed/sieve-sequence
  weights, not existence of Chen pairs itself.
- The permanent `candidates/INVESTIGATION_STATUS.md` closure matrix now
  classifies all 25 candidates by completed investigation, failed or exhausted
  routes, remaining theorem, and reopen trigger.
- The top twin-prime frontier is candidate #23's signed accepted-boundary
  discrepancy feeding candidate #24's terminal harmful-excess energy. The
  existing capacity, native-period, Bessel, fixed/moving-cut, and stability-gap
  routes are explicitly exhausted; continuing needs new signed mean-square or
  cross-layer cancellation.
- Candidate #25 is the only important genuinely distinct program. Its weight,
  Type-I model, arbitrary-coefficient Type-II obligation, scale conflict, and
  go/no-go criteria are already investigated in the analytic deep-dive.
  Proving those estimates is future theorem work, not missing candidate audit.
- The user accepted the stable handoff on 2026-08-05. `candidates/README.md`
  now presents `candidates/INVESTIGATION_STATUS.md` as authoritative for
  current classifications and reopen triggers, and preserves the former
  next-step queue as historical/supporting guidance. This closes broad
  candidate exploration and prioritization, not the open mathematical
  hypotheses themselves.
- Stainless baseline: 30 valid, 0 invalid, 0 unknown. Initial work is
  Markdown/read-only arithmetic.

## What is Learned

- “One failure is enough” applies only after the target's outer quantifier is
  confirmed universal.
- A failure of one head can refute an all-heads strengthening while leaving an
  infinitely-many-heads candidate unchanged.
- Refuted auxiliary laws must be saved, but must not inflate the count of
  refuted numbered candidates.
- A finite exact program is not automatically a universal conjecture. Candidate
  #15 intentionally separates its proved finite table from any unasserted
  recurrence or asymptotic extrapolation.
- A universally quantified inequality is not a concrete falsifier when its
  controlling error function is left free. Candidates #12 and #13 need a fixed
  quantitative specialization before exact counterexample work is decisive.
- Full refutation of an infinitely-often main hypothesis requires an eventual
  obstruction, not an isolated failed transition. That task can be comparable
  in strength to disproving the intended prime-producing conclusion itself.
- Stored exact measurements can contain refutations not propagated into the
  candidate/refuted catalogs. Candidate #4's cyclic-run value `3` is such a
  case and defeats the previously suggested constant `R=2` route.
- A classical theorem establishing the target objects does not establish that
  this project's weights prove their existence. Candidate #25 must make the
  method-specific positivity statement primary and label the bare existence
  conclusion as externally known.
- “Open” does not mean “under-investigated.” The closure test is whether the
  strongest established reduction, failed routes, missing ingredient, and
  retry condition are recorded. All 25 candidates now meet that test.

## Expected State

- A table maps every live numbered candidate to its exact outer quantifier and
  one-counterexample status.
- Universal subclaims are named separately from their parent candidates.
- Every live candidate has a closure classification: investigated enough for
  handoff, important unresolved investigation, or intentionally deferred with
  a precise prerequisite.
- Every important unresolved investigation has one concrete algebraic next
  question rather than a request for more undirected data.
- Catalog and refuted-route records use the same scope.

## Approaches Considered

### Candidate #15 Universal Recurrence Audit

**Status:** PRE-EMPTED

Candidate #15 does not assert a recurrence equality or asymptotic formula.
Inventing one and refuting it would not refute the candidate.

**Retry condition:** Candidate #15 is amended with one explicit, canonical
recurrence or numerical extremal conjecture.

### Universal Auxiliary-Statement Audit

**Status:** RECOMMENDED

Inspect the live candidate files for already-stated universal arithmetic laws
whose failure would remove a genuine proof route. For each target, preserve an
exact counterexample in `candidates/refuted/` and state explicitly that the
parent numbered candidate remains open when its main quantifier survives.

**Strengths:** One witness is logically decisive, negative results prevent
future repetition, and no artificial strengthening is introduced.
**Risks:** This refutes proof routes rather than the infinitely-often main
hypotheses.
**Fallback:** Fix a numerical `E_p(J,w)` or `eta_p` specialization for #12 or
#13, then treat that specialization as a separately named conjecture.

### Eventual Obstruction to a Main Candidate

**Status:** OPEN, HIGH COST

Prove that a candidate fails for every head beyond an explicit threshold, or
that only finitely many successful heads can exist. This would genuinely
contradict an infinitely-often main hypothesis.

**Risk:** For the prime-producing candidates, such an obstruction may be as
hard as the central arithmetic question and cannot be inferred from finite
search.

### Finite Failure Search for Infinitely-Often Candidates

**Status:** BLOCKED AS FULL REFUTATION

Useful only for refuting an explicitly named universal strengthening or
disqualifying individual heads.

**Retry condition:** An eventual obstruction is derived, or the candidate is
formally restated with a universal quantifier.

## Assumptions

- Candidate files, not catalog shorthand, define the authoritative
  quantifiers.
- Exact finite computation may certify a universal counterexample when its
  definitions and witness are independently checkable.
- Empirical non-witnesses do not establish a universal theorem.

## Risks

- Confusing auxiliary universal lemmas with the numbered candidate.
- Treating “eventually for every prime” as refuted by a small exceptional
  prime when no threshold was specified.
- Reusing catalog summaries without reading the actual candidate body.
- Creating duplicate refuted files for a route already preserved elsewhere.

## Validation

- Quote or paraphrase each candidate's exact quantifier with a source line.
- For every proposed one-witness target, state why the quantifier makes the
  witness decisive.
- For every live candidate, cite the candidate file and any property or ticket
  supporting its closure classification.
- Search active and completed tickets for unpromoted findings or abandoned
  routes whose retry conditions have changed because of newer properties.
- Treat “blocked” and “twin-prime-strength” as claims to be checked against the
  current algebra, not inherited conclusions.
- Verify exact arithmetic witnesses independently.
- Markdown-only changes require `git diff --check`; code changes require the
  chapter-by-chapter verification sequence.

## Failed Paths

- **#20/#22 finite head search as full refutation:** blocked by their
  infinitely-many-heads quantifiers. Retry only with an eventual obstruction
  or an explicitly universal strengthening.
- **#15 guessed recurrence as candidate refutation:** pre-empted because #15
  explicitly asserts no recurrence or asymptotic formula. Retry only after a
  concrete conjecture is actually stated.
- **#12/#13 one-witness search without fixed error bounds:** underdetermined
  because `E_p(J,w)` and `eta_p` are unspecified. Retry only for a named
  quantitative specialization.
- **#4 constant cyclic-run bound `R<=2`:** refuted exactly at `Q=101`, `r=23`,
  where the full-period run is `3`. Retry only with a larger or variable bound,
  and still prove the separate local-block premise.
- **#25 bare Chen-pair existence as an open project theorem:** mis-scoped
  because Chen plus Bertrand already supplies that existence. Retry only as a
  method-specific theorem about positivity of the project's relaxed weights.

## Open Concerns

- The practical negative-work target is now an auxiliary universal law, not a
  numbered main hypothesis. Its scope must remain visible in filenames,
  headings, and catalog counts.
- Several early candidates are near-restatements of desired outcomes rather
  than arithmetic laws, so their universal subclaims may not be strategically
  meaningful.
- Candidate #4's variable `R_p` is tautologically available as a finite-period
  maximum unless an independent useful upper bound is imposed; the meaningful
  mechanism must specify a bound small enough to combine with local population.
- Candidate #25 now has the required precise quantifier and positivity formula;
  the remaining concern is proving its Type-I and Type-II estimates from the
  project-specific weights.
- No unclassified candidate-level concern remains. The remaining concerns are
  the named mathematical frontiers themselves: #23/#24 signed cancellation,
  a useful replacement bound for #4 only if one is proposed, and #25's
  method-specific Type-I/Type-II estimates.

## Next Action

None for the closure audit. The stable handoff choices are:

1. continue the current twin-prime line only with new signed cancellation for
   #23 sufficient to discharge #24;
2. open a separate almost-prime proof program for #25's already-specified
   Type-I and Type-II obligations; or
3. revisit #4 only after stating a useful cyclic-run bound that survives the
   exact run-three counterexample and composes with a local-block theorem.

Do not resume undirected data collection or capacity-only optimization.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-03 | Ticket created after #20/#22 finite refutation was blocked by outer quantifiers. Preliminary catalog scan identifies #15 as the strongest exact universal target. | Read #15 and related tickets; test its proposed recurrences against proved values. |
| 2026-08-03 | Full screen overturns the preliminary #15 ranking: #15 asserts no recurrence; #12/#13 leave their error controls unspecified; the remaining main claims are predominantly infinitely-often. No live numbered main hypothesis is currently a concrete one-witness target. | Preserve #15/#12/#13 as pre-empted paths and redirect exact counterexample work to already-stated universal auxiliary laws. |
| 2026-08-03 | Stable handoff requires more than selecting a refutation target: every live candidate needs an evidence-backed closure classification, and any materially distinct unexamined route must be surfaced. | Expand the ticket to a candidate-by-candidate closure audit before declaring the investigation phase complete. |
| 2026-08-03 | Closure audit found two material record defects: #4's exact Q101/r23 cyclic run `3` already refutes `R<=2`, and #25's bare existence claim is externally implied by Chen plus Bertrand rather than being an open project theorem. | Promote #4's refuted shortcut and restate #25 around the genuinely open weight-specific positivity theorem before continuing the matrix. |
| 2026-08-03 | The #4 refutation is now preserved with an explicit three-start certificate and propagated to both catalogs; #25 now makes relaxed-weight positivity primary and labels bare existence externally known. | Resume the closure matrix and determine whether #25's distinct Type-I/bilinear route has a sufficiently precise handoff boundary. |
| 2026-08-03 | The 25-row closure matrix confirms that the principal twin-prime investigation is reduced to #23 -> #24 signed cancellation, while #25's genuinely distinct almost-prime program is already scoped through explicit Type-I/Type-II go/no-go criteria. #20's ticket-only falsifier findings were promoted during the audit. | Mark the audit complete. Future work must select one of the three named mathematical fronts rather than reopen the broad candidate search. |
| 2026-08-05 | The user directed that the completed handoff be made operational. Preserving candidate notes does not require presenting their historical targets as an active queue. | Aligned `candidates/README.md` with the closure matrix while retaining formulas, evidence, limitations, and explicit reopen triggers. |
