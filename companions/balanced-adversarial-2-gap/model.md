# Balanced Adversarial 2-Gap Companion Process

**Candidate hypothesis:** N/A -- this file states and proves a fact about a
constructed companion process, not an open hypothesis about the real sieve.

**Conditional implication:** Mathematically proved (see "Proof" below); the
one geometric premise it needs is itself already an established fact (cited
under "The One Premise, Already Established").

**Empirical status:** N/A -- a closed-form combinatorial argument, not an
empirical claim.

## Purpose

The third of three companion processes sharing the same exact global
mechanics as
[the balanced randomized 2-gap companion](../balanced-randomized-2-gap/model.md)
(every parent produces exactly `r-2` surviving children,
`N(Q)=N_0\prod(r-2)`, proved unbounded exactly as in
`exact-global-two-gap-count.md`), but choosing *which* two copies die
adversarially instead of uniformly at random. Its purpose is to make a
single point sharp and unconditional:

> Unbounded global 2-gap growth alone cannot force head 2-gaps.

| Companion | Choice of the two destroyed copies | Global behavior | Local behavior |
|---|---|---|---|
| [Balanced good / protective](../balanced-good-2-gap/model.md) | avoid the head/window whenever possible | exact `r-2` growth | maximizes local survival |
| [Balanced random](../balanced-randomized-2-gap/model.md) | uniform two-subset | exact `r-2` growth | statistical baseline (proved conditional on spatial uniformity) |
| Adversarial (this file) | prefer the head/window | exact `r-2` growth | can enforce local extinction, unconditionally |

All three share the identical, already-proved global recurrence. Only the
local outcome differs -- from guaranteed extinction (this file) to
conditionally-guaranteed persistence (the random companion) -- which is
exactly the demonstration that global population size carries zero
information about local/positional outcomes on its own.

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

## Proof

**Claim:** if `m_g(W) \le 1` for every parent `g`, then `N_{\mathrm{adv}}(W) = 0`.

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
again, unconditionally, no geometric assumption required at all.

## The One Premise, Already Established

The general-window version needs `m_g(W)\le1` for every parent, which holds
whenever the window's length is smaller than the *current* modulus `M`
(children of one parent are spaced exactly `M` apart, so a window shorter
than `M` can contain at most one of them). This is not a new assumption for
this file -- it is already the crossover fact recorded in Section 7 of
`articles/learnings/learnings-capacity-argument.md`:

> "For $p \le 7$ ... every 2-gap in the cycle falls inside the window. For
> $p \ge 11$, the primorial $M_k$ permanently outgrows $p^2$."

So for every stage past the first few (`p \ge 11`), the square-safe window
is already smaller than the modulus, and the adversarial construction above
applies unconditionally from that point on.

## The Real Filter Is Weaker Than This Adversary

This adversary is **stronger than the real modular filter**, and that gap
is the actual research content here, not a footnote. This adversary chooses
its two harmful copies *independently and freely for every parent*,
specifically targeting whichever parents currently have a child in `W`. The
real filter's choice is not free: which two copies die is rigidly
determined by residue arithmetic --
`K^{\mathrm{real}}_{g,r} = \{-aM^{-1}, -(a+2)M^{-1}\} \pmod r`
(`properties/sieve-sequence/copy-index-filter-frequency.md`) -- the *same*
fixed formula applied uniformly to every parent, with no freedom to
"choose" which parents to target based on where their children happen to
land. This is exactly the distinction already flagged, in looser language,
in Section 21 of `articles/learnings/learnings-capacity-argument.md`
("Worst-Case Adversarial Merge Bounds Size, Not Position"): a fully free
adversary is a legitimate bound on *magnitude* but is too pessimistic to
say anything about *position*, because the real process's rigidity is
exactly the structure a valid positional argument needs to exploit, and a
free adversary discards that structure entirely.

**The real open research question, stated precisely by these three
companions together:** does the arithmetic coupling in `K^{\mathrm{real}}`
keep the actual filter's local behavior closer to the friendly/balanced-random
companions (where local survival is proved, or proved conditional on
spatial uniformity), or does it permit the kind of sustained, coordinated
concentration near the head that this unconstrained adversary can achieve
at will? Nothing proved in this file or
[the balanced randomized companion](../balanced-randomized-2-gap/model.md)
answers that -- both are companions to the real process, not descriptions
of it. What they jointly
establish is the *shape* of the open question: it is entirely about whether
`K^{\mathrm{real}}`'s rigidity is closer to random or closer to adversarial,
not about population size, which is settled identically in all three cases.

## Related

- [Targeted Head Suppression](properties/targeted-head-suppression.md) --
  this model's proved theorem, cited by name.
- [Balanced randomized 2-gap companion process](../balanced-randomized-2-gap/model.md)
- [Balanced good (protective parent) 2-gap companion process](../balanced-good-2-gap/model.md)
- [Copy-index filter frequency](../../properties/sieve-sequence/copy-index-filter-frequency.md)
- [Exact global 2-gap count](../../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Short-window discrepancy](../../candidates/short-window-discrepancy.md)
- [Local surplus](../../candidates/local-surplus.md)
