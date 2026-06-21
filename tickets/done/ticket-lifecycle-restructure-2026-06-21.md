# Ticket Lifecycle Restructure

**Status:** Done
**Date:** 2026-06-21

## Goal

Reduce ticket-search noise by moving historical tickets out of the default
search path.

## Result

Created the lifecycle folders:

- `tickets/active/`
- `tickets/done/`
- `tickets/superseded/`
- `tickets/archived/`

Added `tickets/README.md` with the new search order:

1. Search `tickets/active/` first.
2. Expand to `done/`, `superseded/`, or `archived/` only when historical
   context is needed.

Created the active canonical ticket:

- `tickets/active/v0-gap-list-cycle-formalization.md`

Moved older gap tickets to `tickets/superseded/` so they remain available as
proof logs without polluting active searches.

## Validation

This was a markdown-only restructure. Per AGENTS.md, Stainless verification was
not required.
