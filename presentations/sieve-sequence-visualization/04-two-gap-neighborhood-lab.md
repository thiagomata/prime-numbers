# Proposal 04: 2-Gap Neighborhood Lab

## Format

A focused analytical tool for 2-gap spacing, neighborhoods, and safe-zone
behavior.

This is the research-facing concept. It cares less about cinematic motion and
more about giving the eye useful invariants.

## Core Idea

A 2-gap is not just a count. It has a neighborhood, a lineage, a position, and a
relationship to the safe zone.

Instead of showing every gap equally, collapse or summarize the non-2 material
around 2-gaps:

```text
... D_left, 2, D_right ...
```

where `D_left` and `D_right` are either exact neighboring gaps, windows of
neighboring gaps, or compressed non-2 distances between consecutive 2-gaps.

## Main Views

### Neighborhood Heatmap

Rows are stages. Columns are pattern keys.

Example pattern keys:

```text
4|2|4
6|2|4
10|2|4
10|2|10
```

The color is frequency. This shows which local 2-gap environments dominate or
disappear.

### 2-Gap Spacing Strip

Use the `gaps-2` compressed view:

```text
D_0, 2, D_1, 2, D_2, 2, ...
```

This shows distance between twin-prime candidates more directly than the full
gap cycle.

### Safe-Zone Occupancy

Track how many 2-gaps lie before `head^2`, near `head^2`, and after `head^2`.

This should not be phrased as proof of twin primes. It is an empirical lens on
where full-period survival does or does not reach the local certification
window.

### Descendant Fan

Select one 2-gap ancestor and show its descendants under the next stages.

Expected full-period behavior: each 2-gap has `q - 2` surviving descendants
when adding a new prime `q > 2`. The view should make clear that full-period
survival and safe-zone landing are different questions.

## Data Needed

- 2-gap compressed files;
- per-stage 2-gap counts;
- 2-gap positions;
- fixed-width windows around each 2-gap;
- lineage or parent identifiers where available;
- safe-zone boundary per stage.

## Strengths

- Directly targets the twin-candidate question.
- Helps separate global survival from local safe-zone presence.
- Good for finding patterns worth turning into conjectures or proof tickets.
- Naturally uses Spark aggregation.

## Weaknesses

- Less intuitive for a first-time viewer.
- Needs careful wording to avoid overclaiming.
- The most interesting views require derived datasets not yet guaranteed by the
  current CSV output.

## Best Use

Use this after the merge grammar is stable and after Spark exports pattern or
window aggregates.

