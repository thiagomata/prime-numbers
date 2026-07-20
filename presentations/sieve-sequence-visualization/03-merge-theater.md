# Proposal 03: Merge Theater

## Format

A focused animation or small interactive scene dedicated to one transition at a
time.

This is the smallest strong prototype. It does not try to show everything. It
only teaches the viewer to see the copy-or-merge rule.

## Core Idea

Every new gap has a visible cause:

```text
copy:  [a]             -> [a]
merge: [a] x [b]       -> [a + b]
merge: [a] x [b] x [c] -> [a + b + c]
```

The `x` marks a filtered value. The animation makes deletion and repair feel
like one event.

## Scene

1. Show a row of surviving values.
2. Draw gaps between adjacent values.
3. Introduce the new head.
4. Mark values divisible by the new head.
5. Fade those values as composites revealed at this stage.
6. Pull neighboring gap segments together.
7. Replace them with a new gap labeled by the sum.
8. Repeat across the stage.
9. Rotate to the next head.

## What It Makes Noticeable

### Merge

The viewer sees that a merge is not a mysterious new gap. It is the sum of
adjacent old gaps after interior values are removed.

### Composite Revelation

The deleted value is not shown as "bad from the beginning." It is shown as a
candidate whose composite status becomes visible only when the new filter is
introduced.

### Safe-Zone Boundary

When the transition is shown near the beginning of the sequence, the safe-zone
boundary can sit in the same scene. Merges before and after the line still
happen, but only the left side carries local certification meaning.

## Data Needed

- current stage values and gaps;
- next-stage gap output;
- per-gap `origin`;
- ancestor gap values for merges;
- value divisibility by the new head;
- safe-zone endpoint `head^2`.

## Strengths

- Highest explanatory value per unit of implementation.
- Works with very small stages.
- Establishes the visual grammar needed by every larger artifact.
- Gives a concrete answer to "what happened here?"

## Weaknesses

- Does not show global density by itself.
- Needs careful pacing to avoid becoming repetitive.
- Lineage data must be accurate or the animation will teach the wrong lesson.

## Best Use

Build this first for stages 2 through 5. Once it feels right, embed it inside
the semantic zoom film and interactive atlas.

