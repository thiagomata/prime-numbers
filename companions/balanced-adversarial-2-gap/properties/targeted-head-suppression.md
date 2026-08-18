# Targeted Head Suppression

**Status:** Mathematically proved, unconditionally for the head, and
conditional on one geometric premise (already established elsewhere) for a
general target window. For the balanced adversarial 2-gap companion. Not a
claim about the real modular filter.

## Meaning

An adversary that is free to choose, independently for every parent, which
two of its `r` children to destroy can drive a chosen target region's local
population to exactly zero forever, while the global 2-gap population keeps
growing without bound. This is the sharp, unconditional demonstration that
unbounded global growth alone carries no information about local or
positional outcomes.

## Setup

Fix a target region `W` (a square-safe window, or a single distinguished
point, "the head"). For each parent `g` at the step installing filter `r`,
let `m_g(W)` be the number of `g`'s `r` children landing in `W`. The
adversary destroys `\min(2, m_g(W))` of those children -- using its two
allotted deletions on `W`-copies first, wherever any exist. The surviving
local contribution from parent `g` is therefore

```math
S_g^{\mathrm{adv}}(W) = m_g(W) - \min(2, m_g(W)) = \max(0, m_g(W) - 2),
```

and summing over parents,

```math
N_{\mathrm{adv}}(W) = \sum_g \max(0, m_g(W) - 2).
```

## Property

**Claim:** if `m_g(W) \le 1` for every parent `g`, then
`N_{\mathrm{adv}}(W) = 0`.

**Proof:** `m_g(W)\in\{0,1\}` for each `g` implies `m_g(W)-2 \in \{-2,-1\}`,
both negative, so `\max(0,m_g(W)-2)=0` for every term. The sum of zeros is
zero. $\blacksquare$

The adversary achieves this while spending only one of its two allotted
deletions on each relevant parent (or zero, where `m_g(W)=0`); the other
deletion is spent anywhere else in that parent's `r` copies, with no effect
on `W`. Nothing about this choice touches the global recurrence -- every
parent still loses exactly 2 of its `r` copies, so

```math
N_k \to \infty \quad\text{globally, while simultaneously}\quad N_k(W_k) = 0
```

for every chosen target window `W_k`, at every layer, forever.

**For the head alone, the premise is not even needed.** A single point
target has `m_g(\{\text{head}\}) \le 1` automatically for every parent --
`g`'s `r` children are `r` distinct positions, so at most one of them can
equal any one fixed coordinate. Whenever a parent has a child sitting at the
prospective head position, the adversary spends one deletion there. So the
global 2-gap population can explode while no 2-gap ever reaches the head
again, unconditionally, no geometric assumption required at all. `\blacksquare`

## The One Premise, Already Established

The general-window version needs `m_g(W)\le1` for every parent, which holds
whenever the window's length is smaller than the *current* modulus `M`
(children of one parent are spaced exactly `M` apart, so a window shorter
than `M` can contain at most one of them). This is not a new assumption --
it is already the crossover fact recorded in Section 7 of
[`articles/learnings/learnings-capacity-argument.md`](
../../../articles/learnings/learnings-capacity-argument.md):

> "For $p \le 7$ ... every 2-gap in the cycle falls inside the window. For
> $p \ge 11$, the primorial $M_k$ permanently outgrows $p^2$."

So for every stage past the first few (`p \ge 11`), the square-safe window
is already smaller than the modulus, and the construction above applies
unconditionally from that point on.

## What This Does And Does Not Say

This adversary is **stronger than the real modular filter** -- that gap is
the actual research content of this model, not a footnote. This adversary
chooses its two harmful copies independently and freely for every parent,
specifically targeting whichever parents currently have a child in `W`. The
real filter's choice is not free: which two copies die is rigidly
determined by residue arithmetic,
`K^{\mathrm{real}}_{g,r} = \{-aM^{-1}, -(a+2)M^{-1}\} \pmod r`
([Copy-index filter frequency](
../../../properties/sieve-sequence/copy-index-filter-frequency.md)) -- the
same fixed formula applied uniformly to every parent, with no freedom to
choose which parents to target. A fully free adversary is a legitimate
bound on *magnitude*, but is too pessimistic to say anything about
*position*, because the real process's rigidity is exactly the structure a
valid positional argument needs to exploit. See
[the model file](../model.md) for the full discussion of what this
demonstration does and does not settle about the real sieve.

## Related

- [Balanced adversarial 2-gap companion process](../model.md) -- full
  purpose, comparison with the other balanced companions, and discussion.
- [Balanced randomized 2-gap companion process](
  ../../balanced-randomized-2-gap/model.md)
- [Balanced good (protective parent) 2-gap companion process](
  ../../balanced-good-2-gap/model.md)
- [Copy-index filter frequency](
  ../../../properties/sieve-sequence/copy-index-filter-frequency.md)
- [Exact global 2-gap count](
  ../../../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Short-window discrepancy](../../../candidates/short-window-discrepancy.md)
- [Local surplus](../../../candidates/local-surplus.md)
