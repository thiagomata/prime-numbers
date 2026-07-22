# Proposal 01: Semantic Zoom Film

## Format

A rendered explanatory video, probably built with Manim or Motion Canvas.

The film starts with a tiny exact sequence and continuously zooms out until the
viewer can no longer read individual gaps. The visual language changes at each
scale: labels become ticks, ticks become density, and density becomes a global
shape.

## Core Idea

Start with the trees:

```text
S_2: [2, 4]
S_3: [6, 4, 2, 4, 2, 4, 6, 2]
```

Then zoom out until the viewer sees the forest:

```text
stage -> repeated old cycle -> new filter -> deletions -> merges -> new cycle
```

The camera does not merely enlarge the plot. It changes the level of truth being
shown:

- exact gap labels at small scale;
- copy and merge events at transition scale;
- 2-gap neighborhoods at local scale;
- density texture at large scale;
- safe-zone boundary at certification scale.

## Storyboard

1. **Seed and first gaps**
   Show the first stages as literal finite cycles. Every gap is readable.

2. **The repeated-copy moment**
   Lay out the current gap cycle repeated `head` times. This makes the
   boundary-free expansion visible before anything is deleted.

3. **The composite reveal**
   Mark the values divisible by the new head. They were accepted by earlier
   filters, but the new filter exposes them as composite.

4. **The merge**
   Remove a filtered value and show its two adjacent gaps becoming one gap.
   Use labels like `4 + 2 = 6` only while the camera is close enough.

5. **The safe-zone line**
   Draw a boundary at `head^2`. Values before the boundary can be treated as
   certified by the current sieve when both endpoints of a 2-gap are inside it.
   Values after it remain visible, but their status is later-dependent.

6. **Zoom out**
   Labels fade out. 2-gaps remain highlighted. Later stages become textures:
   stripes, pulses, and local density fields.

## Visual Grammar

| Event | Visual |
|-------|--------|
| Copied gap | Steady segment carried forward |
| Merged gap | Two segments pull together through a deleted point |
| Newly exposed composite | Hollow candidate turns marked and fades |
| Confirmed prime in safe zone | Filled point with quiet emphasis |
| 2-gap | Persistent bright short arc |
| Safe-zone boundary | Crisp moving vertical line at `head^2` |
| Beyond safe zone | Same data, lower certainty styling |

## Data Needed

- stage summary: `stage`, `head`, `period`, `modulus`, `twoGapCount`;
- first values for small stages;
- gap cycle for stages where exact rendering is practical;
- per-gap `origin` for copy/merge animation;
- sampled or binned density for large stages;
- optional composite metadata: which later head first rejects a value.

## Strengths

- Best format for public explanation.
- Makes the mathematical transition memorable.
- Separates accepted candidates from certified primes cleanly.
- Can be narrated without requiring user interaction.

## Weaknesses

- Less useful for research exploration.
- Requires careful scripting and rendering.
- Large-stage detail must be pre-aggregated; exact stage 9 drawing is not the
  point of this format.

## Best Use

Use this for the final shareable artifact after the interaction grammar has been
tested in a smaller prototype.

