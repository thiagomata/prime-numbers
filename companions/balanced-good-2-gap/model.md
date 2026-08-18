# Balanced Good (Protective Parent) 2-Gap Companion Process

**Candidate hypothesis:** N/A -- this file states and proves facts about a
constructed companion process, not an open hypothesis about the real sieve.

**Conditional implication:** Mathematically proved (see the properties
below); the premises each theorem needs are stated explicitly in that
theorem's Status line, not assumed silently.

**Empirical status:** Not yet measured (no simulation run).

## Purpose

The protective parent policy is the local opposite of
[the balanced adversarial 2-gap companion](../balanced-adversarial-2-gap/model.md).
Where the adversarial parent destroys its target child whenever the
exact-two-deletion rule allows it, the protective parent *preserves* it
whenever that rule allows it. Both share the identical global recurrence
proved for every balanced companion in
[Global Persistence Independence](../properties/global-persistence-independence.md):
choosing *which* two copies die never changes how many survive.

| Companion | Choice of the two destroyed copies | Global behavior | Local behavior |
|---|---|---|---|
| [Balanced adversarial](../balanced-adversarial-2-gap/model.md) | prefer the head/window | exact `r-2` growth | can enforce local extinction, unconditionally |
| [Balanced random](../balanced-randomized-2-gap/model.md) | uniform two-subset | exact `r-2` growth | statistical baseline (proved conditional on spatial uniformity) |
| Balanced good / protective (this file) | avoid the head/window whenever possible | exact `r-2` growth | maximizes local survival |

Its purpose is the mirror image of the adversarial file's point: it fixes the
*optimistic* endpoint of the same balanced family, isolating how much of the
balanced-random companion's local loss is attributable to the random
placement itself (the `1-2/r` factor) rather than to any positional
information a policy could exploit.

## Definition

Fix a target region `W` (a square-safe window, or a single distinguished
head position). For parent `g`, let `T_g(W)` be the indices of its children
that lie in `W`. In the post-crossover regime (the target window is shorter
than the old period, so each parent contributes at most one child to it),

```math
|T_g(W)|\le1.
```

Because the incoming filter `r>=5`, at least `r-1>=4` child indices lie
outside `T_g(W)`. The protective parent policy chooses its harmful pair from
among those:

```math
K_{g,r}^{\mathrm{protective}}
\subseteq
(\mathbb Z/r\mathbb Z)\setminus T_g(W),
\qquad
|K_{g,r}^{\mathrm{protective}}|=2.
```

This is well defined whenever `T_g(W)` is nonempty, since removing at most
one index from `r>=5` choices always leaves at least two to delete. Exactly
two children are removed regardless, so exactly `r-2` descendants survive --
identical to every other balanced companion.

```math
\begin{aligned}
T_g(W)\ne\varnothing
&\Longrightarrow
\text{the protective parent preserves the target child},\\
T_g(W)=\varnothing
&\Longrightarrow
\text{the target choice is irrelevant to this parent}.
\end{aligned}
```

## What It Is (and Is Not)

The protective parent is an oracle comparison, not a plausible random
filter: it is allowed to see the chosen target and place its two deletions
elsewhere. It does not model the real sieve's arithmetic (which does not
"choose" anything positionally) any more than the adversarial companion
does. Its role is to define the optimistic endpoint of the balanced family,
exactly as the adversarial companion defines the pessimistic endpoint and
the random companion sits, unconditionally on placement, between them.

## Mixed Adversarial/Protective Policies

The properties below study a *mixture*: at each filter `r`, a locally
relevant lineage independently becomes an adversarial parent (destroys its
target child) with probability `alpha_r`, or a protective parent (preserves
it) with probability `1-alpha_r`. This isolates exactly the local placement
question -- given that a lineage is not itself adversarial, does removing
the random-placement penalty change how much adversarial share the process
can tolerate?

## Related

- [Balanced adversarial 2-gap companion process](../balanced-adversarial-2-gap/model.md)
  -- the pessimistic endpoint of the same balanced family.
- [Balanced randomized 2-gap companion process](../balanced-randomized-2-gap/model.md)
  -- the position-blind baseline this file's mixtures are compared against.
- [Global Persistence Independence](../properties/global-persistence-independence.md)
  -- the shared exact `r-2` recurrence every balanced companion obeys.
- [Cumulative Local-Hazard Law](../properties/cumulative-local-hazard-law.md),
  [Logarithmic-Worsening Thresholds](../properties/logarithmic-worsening-thresholds.md)
  -- the shared relative-hazard machinery this family's thresholds specialize.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §5.2](
  ../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
  -- the source article section defining the protective parent policy.
