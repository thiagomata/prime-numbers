# Tickets

Ticket files are grouped by lifecycle to keep search results focused.

## Search Order

Start with:

```text
tickets/active/
```

Then expand to `tickets/blocked/` for open problems blocked on new math or tooling.
Completed tickets are in `tickets/done/`.

Stale tickets (superseded approaches, old planning docs, article reviews) have been
moved to `tickets/trash/` — do not use them as a source of current strategy.

## Folders

- `active/` — current work and canonical planning tickets.
- `blocked/` — real open problems that are not current work because they need
  substantial new mathematics or a new solver strategy.
- `done/` — completed tickets with useful final state or implementation notes.
- `future/` — low-priority tickets, reference documents, and deferred work.
  Not blocking current progress; revisit when priorities shift.
- `trash/` — superseded approaches, old planning records, and article reviews.
  Kept for historical reference only; do NOT drive new work from them.

## Current Sieve-Sequence Proof Ticket

The canonical active ticket for the Spec/Canonical/Cycle sieve-sequence proof is
`active/sieve-sequence-proof.md`.

The A = B = C equivalence (Spec ≡ Canonical ≡ Cycle for both current and next
stages) is fully proven. The remaining open work is Leg 4 (survival walk
correctness) tracked in the proof ticket.
