# Tickets

Ticket files are grouped by lifecycle to keep search results focused.

## Search Order

Start with:

```text
tickets/active/
```

Only expand into the other folders when you need historical context,
verification logs, failed attempts, or completed implementation notes.

## Folders

- `active/` — current work and canonical planning tickets.
- `blocked/` — real open problems that are not current work because they need
  substantial new mathematics or a new solver strategy.
- `done/` — completed tickets with useful final state or implementation notes.
- `superseded/` — older tickets replaced by a newer canonical plan.
- `archived/` — historical notes, article reviews, summaries, and stale planning
  records that should not drive new implementation work.

## Current Sieve-Sequence Proof Ticket

The canonical active ticket for the Spec/Canonical/Cycle sieve-sequence proof is
`active/sieve-sequence-proof.md`.

Older plans for the same proof have been moved out of `active/`:

- `done/canonical-spec-to-cycle-alignment.md` — current-stage Spec-to-Canonical
  alignment was completed and remains useful background.
- `superseded/v0-v2-apply-equivalence.md` — replaced by the canonical strategy.
- `superseded/remove-extern-from-next.md` — old `next()` removal framing; the
  remaining issue is now tracked as the survival-walk correctness gap in the
  canonical ticket.

## Completed Canonical Gap Ticket

V0 gap-list and gap-cycle formalization was completed in
`done/v0-gap-list-cycle-formalization.md` (7755 valid, all open work resolved).
Older gap tickets remain in `superseded/` for proof logs and breadcrumbs.
