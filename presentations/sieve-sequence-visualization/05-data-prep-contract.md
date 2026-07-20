# Proposal 05: Data Prep Contract

## Purpose

The video and interactive concepts should not read huge raw stage files
directly. Spark should produce exact small-stage data and aggregated large-stage
data tuned for the views.

This file defines the visual-facing datasets that would make the proposals
practical.

## Stage Summary

One row per stage.

```text
stage
head
period
modulus
gap_count
two_gap_count
two_gap_density
safe_zone_end
```

Used by every proposal.

## Exact Gap Sample

Exact rows for small stages and selected windows of larger stages.

```text
stage
gidx
position_value
gap
origin
age
merge_count
ancestor_values
is_two_gap
inside_safe_zone
```

Used by the merge theater, film close-ups, and atlas inspection.

## Transition Events

One row per visible transition event.

```text
from_stage
to_stage
event_index
event_type
old_start_value
old_end_value
new_start_value
new_end_value
deleted_values
old_gap_values
new_gap_value
inside_safe_zone
```

`event_type` should include at least:

- `copy`
- `merge`
- `rotation`
- `safe_zone_crossing`

Used by the merge theater and semantic zoom film.

## Composite Revelation

One row per value whose first rejecting filter is known.

```text
value
first_seen_stage
first_rejected_stage
rejecting_head
last_stage_where_accepted
inside_safe_zone_when_rejected
```

This is the dataset that lets the visual distinguish:

- currently accepted candidate;
- later-revealed composite;
- certified prime inside the safe zone.

## 2-Gap Windows

One row per 2-gap with compact local context.

```text
stage
gidx
left_values
right_values
pattern_key
position_value
inside_safe_zone
distance_to_safe_zone_end
```

Example `pattern_key`:

```text
4|2|6
10|2|4
```

Used by the 2-gap neighborhood lab.

## Multiresolution Tiles

One row per stage, zoom level, and bucket.

```text
stage
zoom_level
bucket_index
bucket_start
bucket_end
gap_count
two_gap_count
merge_count
copy_count
dominant_gap
mean_gap
max_gap
entropy
```

Used by the interactive atlas and large-stage film shots.

## Recommended Build Order

1. Use existing small-stage `gaps` and `values` files to build the merge theater.
2. Add `stage_summary` if it is not already exported as a single table.
3. Add `transition_events` for stages 2 through 6.
4. Add `2_gap_windows` for the neighborhood lab.
5. Add `multiresolution_tiles` before attempting stage 8 or later in a browser.

## Guardrails

- Do not load stage 9 raw gaps into a browser.
- Do not imply that a full-period 2-gap count proves safe-zone occupancy.
- Do not label a candidate as prime unless it is inside the relevant safe zone.
- Keep exact views exact and aggregate views visibly aggregate.

