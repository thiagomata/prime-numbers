# <Short Descriptive Title>

**Created:** YYYY-MM-DD
**Updated:** YYYY-MM-DD
**Status:** Plan phase / In progress / Complete / Open / Blocked
**Depends on:** `<ticket-name>.md` (<status>, <verification count>)

> Use `tickets/TEMPLATE.md` to create new tickets. Delete these instructions
> and all instructional comments before saving.

## Related Tickets

<!--
Search tickets/ for related work. Link each and extract relevant lessons.
Use this format:
- `<ticket-name>.md` — <what it's about> (<status>). <key lesson relevant to this ticket>.
-->

- `<ticket-name>.md` — description. key lesson.

<!--
If the ticket references articles, add a Related Articles section.
-->

## Goal

<!--
Short description of what needs to be proved or built. What is the
desired outcome? What changes are expected?
-->

## Current State

<!--
Verification count (valid/invalid/unknown). Key existing lemmas.
What is already true that this ticket builds on. What invariants
are already established.
-->

## Expected State

<!--
What the verification should look like after completion.
What lemmas will be added, where, and what they prove.
-->

## Approaches Considered

<!--
For each approach: what it is, why it might work, what risks it has.
Mark one as RECOMMENDED or list them in priority order.

For complex tickets, use named paths (Path A/B/C). For simpler
tickets, use numbered alternatives (A1/A2/B1).
-->

### <Approach Name>

**Status:** RECOMMENDED / UNTESTED / BLOCKED / FAILED

<approach description>

**Strengths:** <what makes this approach viable>
**Risks:** <what could go wrong, timeout risks>
**Fallback:** <what to try if this fails>

## Assumptions

<!--
Things taken as given: preconditions, invariants, lemma availability.
-->

## Risks

<!--
Timeout risks, missing lemmas, VC explosion, Euclid's lemma wall,
cascading VCs from @extern removal, etc.
-->

## Validation

<!--
How to verify success: green-to-green, verify count targets,
specific tests to run.
-->

## Implementation Plan

<!--
Numbered steps for execution. One per verify cycle.
Include the file where each change goes.
-->

1. <Step 1 description> — `<file.scala>`
2. <Step 2 description> — `<file.scala>`

## Fallback Options

<!--
What to do if the main approach fails. Document exit strategies
and alternative paths.
-->

## Learning Log

<!--
Each row documents one interaction loop. Keep a running log of
what was attempted, what failed/succeeded, and what was learned.

| Date | Learning | Action |
|------|----------|--------|
| YYYY-MM-DD | <what happened, verification counts, root cause of failures, key insight> | <next step or "done"> |
-->

| Date | Learning | Action |
|------|----------|--------|
| YYYY-MM-DD | Ticket created. Goal identified. Related tickets reviewed. | Start implementation. |
