# Proposal 06: Article Diagram Ideas

## Purpose

The articles need static figures that clarify the mathematics without behaving
like screenshots of a tool. Each diagram should carry one claim, fit in a
markdown article, and remain honest about the boundary between verified
structure, mathematical derivation, and open local questions.

These figures should avoid internal ticket language. If adapted into
`articles/`, they should be self-contained and use article-native wording.

## Diagram 1: Copy-Or-Merge Strip

### Article Use

Use in a section explaining how filtering changes gaps.

### Shape

```text
before:

e_i ---- g_i ---- e_{i+1} ---- g_{i+1} ---- e_{i+2}
                     x

after:

e_i ----------- g_i + g_{i+1} ----------- e_{i+2}
```

### What It Shows

A deleted survivor does not create a mysterious new gap. It causes neighboring
old gaps to telescope into a summed gap. If no interior survivor is deleted, the
gap is copied.

### Caption Draft

When a filter removes an interior accepted value, the two adjacent gaps merge
into their sum. When both endpoints and no interior value are removed, the old
gap is copied unchanged.

## Diagram 2: Repeated Period Before Filtering

### Article Use

Use before copy-or-merge, especially in the sieve sequence article.

### Shape

```text
old period M:

|--------- S_k ---------|

expanded by new head h:

|--------- S_k ---------|--------- S_k ---------| ... |--------- S_k ---------|
copy 0                  copy 1                         copy h-1
```

Then overlay marks where the new head removes values.

### What It Shows

The next stage starts from exact repeated copies of the old finite period. The
new prime filter acts across those copies; the old filters do not need to be
re-applied.

### Caption Draft

Adding a new head expands one old period into `h` translated copies. The new
filter removes one congruence class across those copies, and the surviving
values determine the next gap cycle.

## Diagram 3: Candidate, Composite, Certified Prime

### Article Use

Use in a section that distinguishes current sieve acceptance from primality.

### Shape

```text
stage k:

accepted by filters <= p_k:

  hollow dots: candidates
  filled dots inside safe zone: certified primes

later stage:

  crossed hollow dot: candidate later rejected by p_j
```

### What It Shows

A value can be accepted by the current finite sieve without being prime. It
becomes certified only when it lies inside the safe zone for the installed
filters.

### Caption Draft

Current acceptance is not the same as primality. Inside the safe zone, accepted
values have no untested small divisor left; outside it, a later filter may still
reveal a composite.

## Diagram 4: Safe-Zone Boundary

### Article Use

Use in gap dynamics and local survival sections.

### Shape

```text
p                         p^2
|--------------------------|
      certified window

2-gap fully inside:

x ---- 2 ---- x+2          [certifies a twin-prime pair]

2-gap crossing or outside:

                     y ---- 2 ---- y+2
                     [survives current filters, not yet certified]
```

### What It Shows

Both endpoints of a 2-gap must lie inside the safe zone for local
certification. A global full-period 2-gap outside the window is still important,
but it answers a different question.

### Caption Draft

A 2-gap certifies a twin-prime pair only when both endpoints lie in the safe
zone. Full-period survival counts many 2-gaps, but the local problem is where
those 2-gaps land.

## Diagram 5: Full-Period Survival Versus Local Window

### Article Use

Use when warning against overreading global 2-gap counts.

### Shape

```text
one huge period:

|--------------------------------------------------------------------|
  many 2-gaps across the full cycle

front safe window:

|------ p^2 ------|
  local question: does a 2-gap land here?
```

### What It Shows

The full period can contain many 2-gaps while the safe zone remains a much
smaller positional question.

### Caption Draft

Global survival is exact over a complete period. The hard question is local:
whether at least one surviving 2-gap lands inside the front safe window.

## Diagram 6: 2-Gap Descendant Fan

### Article Use

Use near the full-period 2-gap survival recurrence.

### Shape

```text
one old 2-gap
      |
      +-- copy 0  survives
      +-- copy 1  removed: left endpoint divisible by q
      +-- copy 2  survives
      +-- ...
      +-- copy r  removed: right endpoint divisible by q
      +-- ...
```

For a new odd prime `q`, two copy classes are forbidden and the remaining
`q - 2` copies survive.

### What It Shows

A 2-gap does not merely "usually" survive in a full expanded period. It has an
exact forbidden-copy-class structure.

### Caption Draft

Each old 2-gap lifts to one copy in each new block. For an odd new prime, one
copy loses its left endpoint and one copy loses its right endpoint, leaving
`q - 2` surviving 2-gap descendants over the complete expanded period.

## Diagram 7: 2-Focused Compression

### Article Use

Use in empirical or exploratory sections about spacing between twin-prime
candidates.

### Shape

```text
full gaps:

[6][4][2][4][2][4][6][2]

2-focused compression:

[10][2][4][2][10][2]
```

### What It Shows

The compressed view keeps every 2-gap and collapses runs of non-2 gaps into
distances between them. It is a reader-friendly way to discuss 2-gap spacing
without showing the entire gap cycle.

### Caption Draft

For 2-gap analysis, non-2 runs can be collapsed into distances between
consecutive 2-gaps. This preserves the visible spacing of twin-prime candidates
while reducing the surrounding detail.

## Diagram 8: Stage Summary Ladder

### Article Use

Use near the beginning of an empirical section.

### Shape

```text
stage    head    period      2-gaps
S_1        3          1          1
S_2        5          2          1
S_3        7          8          3
S_4       11         48         15
...
```

This can be a compact table, a log-scale bar ladder, or a paired table/plot.

### What It Shows

Period size grows explosively while 2-gaps remain visible in absolute count.
The figure should not imply local safe-zone occupancy by itself.

### Caption Draft

The complete periodic cycle grows quickly, and so does the absolute number of
2-gaps. This is a full-period statistic; local safe-zone placement is a separate
question.

## Diagram 9: Rotation Is A Change Of View

### Article Use

Use where the sequence rotates the next gap cycle around the next head.

### Shape

```text
same cyclic gaps:

      before rotation              after rotation

      [4][2][4][6][2]              [2][4][6][2][4]
             ^                            ^
        arbitrary start              next head start
```

### What It Shows

Rotation changes the linear rendering of a cyclic object. It should not be read
as creating, deleting, or merging gaps.

### Caption Draft

The final rotation chooses the next head as the displayed starting point. It
changes the linear view of the cycle, not the cyclic multiset of gaps.

## Diagram 10: Article Figure Map

### Suggested Placement

| Article Area | Best Diagrams |
|--------------|---------------|
| Sieve sequence construction | Repeated Period Before Filtering, Rotation Is A Change Of View |
| Copy-or-merge theorem | Copy-Or-Merge Strip |
| Current acceptance versus primality | Candidate, Composite, Certified Prime |
| Gap dynamics and 2-gap survival | 2-Gap Descendant Fan, Full-Period Survival Versus Local Window |
| Safe-zone discussion | Safe-Zone Boundary |
| Empirical Spark section | Stage Summary Ladder, 2-Focused Compression |

## Production Notes

- Use Mermaid only for flow diagrams. Use custom SVG, Manim stills, or generated
  PNGs for gap strips where precise spacing matters.
- Keep labels short. Let captions do the explanatory work.
- Prefer one claim per figure.
- Do not put ticket references in article captions.
- Do not label a candidate as prime unless the diagram places it inside the
  safe zone with the relevant filters already installed.
- For article diagrams derived from Spark data, state whether the figure is
  exact, sampled, or aggregated.
