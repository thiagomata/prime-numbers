# Save primorial-neighbor twin research

Created: 2026-10-25
Status: Save complete; mathematical conjecture remains open

## START HERE

Save the discussion of (m-1,m+1), m a primorial, as an unnumbered candidate
research note. Keep elementary deductions distinct from the concluding open
conjecture. User requests saving, not proving the conjecture or editing articles.

## Goal

A discoverable candidate note with proofs, counterexample, finite functional
test, future-prime absorption argument, and precise infinitude conjecture.

## Strategy

Use candidates/ because its README reserves properties/ for established
results. Add links in the exploratory index and related wave-research note.
Do not move existing notes or change publication Markdown/LaTeX/PDF.

## Related Work

- [Wave research](../../candidates/continuous-wave-twin-research.md).
- [Existing wave ticket](continuous-wave-twin-research.md).
- [Primorial algebra ticket](../blocked/primorial-not-divisible-by-new-prime.md):
  relates to product/new-prime coprimality, not primorial twin infinitude.
- [Earlier capacity proposal](cumulative-max-shot-survival-proposal-2026-10-23.md):
  this direction intentionally studies a particular pair instead of counts.

## Current State

Repository structure and related notes inspected. Critic PASS and Monitor
conditional content PASS received. Saved the candidate note and additive
discovery links. All four files pass link, fence and whitespace validation.
Monitor independently read the saved scope and returned post-execution PASS.

## What is Learned

For m=P#, both neighbors avoid primes through P and are coprime. A rejecting
prime for a composite endpoint can be chosen in (P,sqrt(m+1)]. Absorption
protects a later pair and never repairs the original composite endpoint.

## Failed Paths

The discussion's implication that absorption itself forces a later twin pair
is unsupported: the later pair can acquire another rejecting prime. Reopen
that implication only with an argument excluding the new obstructions.
The claim that every proper divisor is at most the square root is false;
only existence of a small prime divisor of a composite is used.
The first link-check helper failed on whitespace in an existing multiline
Markdown link. Trimming link targets corrected the helper; all four files
then passed without changing the linked content.

## Open Concerns

Infinitely many primorial twins is stronger than infinitely many arbitrary
twins. No historical-priority claim or Stainless verification is justified.
Avoid treating the integer divisibility-indicator identity as an identity
between the wave interpolations at every real argument.

## Assumptions and Validation

Require k>=2, P=p_k>=3, m_k=product of the first k primes. Validate residue
proofs and finite cutoff; use 209=11*19 as a counterexample to automatic
primality. Check every added relative link, math fence balance, and whitespace.
Markdown-only prose requires no Scala, Python or PDF runtime gates.

## Next Action

Save task complete. Any future proof work should address whether new rejecting
primes can persist indefinitely; no such theorem is claimed here.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-25 | Mixed proved identities and open conjecture belong in candidates/, not the established-property catalog. | Opened the scoped save ticket; requested Critic and Monitor review. |
| 2026-10-25 | Critic confirmed the finite-band test and absorption qualifications. | Saved elementary proofs, a counterexample, the conditional last-pair consequences and the concluding conjecture. |
| 2026-10-25 | All four Markdown files pass link, fence and whitespace checks; Monitor independently approved the saved scope. | Completed the save and placed discovery links in their context sections. |
