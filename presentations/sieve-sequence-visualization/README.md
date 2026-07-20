# Sieve Sequence Visualization Proposals

This folder collects competing presentation concepts for explaining sieve
sequence gap evolution from Spark-derived data.

The shared goal is to make three events unmistakable:

1. **Merge:** a filtered value disappears and neighboring gaps combine.
2. **Composite revelation:** a value that survived earlier filters is later
   exposed as non-prime.
3. **Safe-zone exit:** the view crosses the boundary where current filters no
   longer certify primality.

The proposals are intentionally separate. They can share data products, but
each has a different storytelling center.

## Proposal Set

| File | Core Format | Best For |
|------|-------------|----------|
| `01-semantic-zoom-film.md` | Manim-style video | A polished explanatory narrative from trees to forest |
| `02-interactive-atlas.md` | Browser interactive | Exploration, scrubbing, and local inspection |
| `03-merge-theater.md` | Event-first animation | Making copy/merge mechanics emotionally obvious |
| `04-two-gap-neighborhood-lab.md` | Focused research tool | Studying 2-gap spacing, neighborhoods, and safe-zone behavior |
| `05-data-prep-contract.md` | Data interface | Spark outputs needed by the visual concepts |
| `06-article-diagram-ideas.md` | Static article figures | Diagrams that can sit inside the written articles |

## Suggested First Build

Build `03-merge-theater.md` first as a small prototype using stages 1 through 5.
It has the strongest explanatory payoff with the least data volume. Once the
merge grammar feels right, reuse it inside the film and the interactive atlas.

For articles, start with the copy-or-merge strip and safe-zone boundary
diagrams from `06-article-diagram-ideas.md`. Those two figures explain the most
with the least visual machinery.
