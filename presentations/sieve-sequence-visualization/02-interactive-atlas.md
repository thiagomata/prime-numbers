# Proposal 02: Interactive Sieve Atlas

## Format

A browser-based interactive view using D3, Canvas, WebGL, deck.gl, or a mix.

This is not a dashboard of charts. It is a map of the sequence. The user can
scrub stages, zoom from exact gaps into density tiles, inspect 2-gap
neighborhoods, and switch between strip, cycle, transition, and safe-zone views.

## Core Idea

Treat each stage as a navigable world.

The x-axis is position in one period. The y-axis is stage. Zoom controls decide
whether the marks represent individual gaps, binned gap histograms, 2-gap
neighborhoods, or transition events.

## Views

### Strip View

One period laid out horizontally.

- Close zoom: every gap is a segment with exact value.
- Medium zoom: 2-gaps are bright ticks; other gaps become lengths or colors.
- Far zoom: buckets show local distribution and 2-gap density.

### Cycle View

One period wrapped around a circle.

- Good for showing periodicity and the rotation that aligns the next head.
- Better for small and medium stages than for stage 9.

### Transition View

Stage `n` repeated `head` times, then filtered into stage `n+1`.

- Shows copies, filtered values, and merges.
- Lets the user pause on a filtered value to see the exact ancestor gaps.

### Safe-Zone View

Focus on `[head, head^2]` or `[0, head^2]`, depending on the chosen convention.

- The boundary is explicit.
- 2-gaps inside the boundary can be visually separated from later-dependent
  2-gaps outside it.

### 2-Gap Neighborhood View

Compress non-2 runs around 2-gaps and show spacing patterns.

Example:

```text
10, 2, 4, 2, 10, 2
```

This makes distances between twin-prime candidates visible without drowning in
all ordinary gaps.

## Interactions

- Stage scrubber.
- Play/pause transition.
- Zoom from exact to aggregate.
- Hover or click a gap to inspect origin, age, merge count, and ancestors.
- Toggle safe-zone boundary.
- Toggle composite revelation coloring.
- Select a 2-gap and follow its descendants where lineage is available.

## Data Needed

- exact gaps for small stages;
- partitioned gap files for medium stages;
- binned tiles for large stages;
- `origin`, `mergeCount`, and ancestor fields;
- 2-gap compressed files;
- stage summary;
- optional value-to-first-rejecting-head table.

## Strengths

- Best format for research and discovery.
- Lets the user test hypotheses interactively.
- Scales naturally if data is pre-tiled.
- Can reuse visual grammar from the film.

## Weaknesses

- More engineering than a video.
- Needs an explicit data contract to avoid loading huge CSVs directly.
- Harder to make emotionally crisp unless the transition view is excellent.

## Best Use

Use this as the main working tool once Spark outputs stable aggregate and tile
files.

