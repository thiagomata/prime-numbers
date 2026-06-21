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
- `done/` — completed tickets with useful final state or implementation notes.
- `superseded/` — older tickets replaced by a newer canonical plan.
- `archived/` — historical notes, article reviews, summaries, and stale planning
  records that should not drive new implementation work.

## Current Canonical Gap Ticket

Use `active/v0-gap-list-cycle-formalization.md` for V0 gap-list and gap-cycle
formalization work.

Older gap tickets remain in `superseded/` for proof logs and breadcrumbs.
