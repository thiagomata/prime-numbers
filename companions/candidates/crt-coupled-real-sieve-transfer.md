# CRT-Coupled Real-Sieve Transfer

**Status:** Open shared transfer obligation. No deterministic real-sieve bound,
probabilistic coupling, spatial-uniformity theorem, or cross-layer mixing theorem
is claimed.

**Classification:** Candidate bridge between constructed companion models and
the deterministic real sieve. This note records what a transfer result must
establish; it is not itself a transfer theorem.

## Question

The real filter and the balanced companions share exact global mechanics: at a
new prime filter, each old 2-gap has indexed copies and exactly two copy-index
classes are harmful. They differ in how the harmful locations are determined.
The companions choose or optimize locations by a declared policy; the real
sieve fixes them through residue arithmetic and CRT coupling.

Can those CRT-determined locations be controlled strongly enough to verify the
premises of a proved companion survival theorem? If not, can their correlations
be characterized sharply enough to show which companion premise fails?

The real sieve is deterministic. Terms such as “random-like” and “mixing” are
comparison language unless a probability space or a rigorous coupling is
explicitly defined.

## What Is Already Exact

The real sieve has an exact two-harmful-copy-class law and an exact global
2-gap recurrence. Balanced companions preserve the corresponding `r-2`
descendant count. The companion properties then prove consequences of their
stated placement, supply, availability, and dependence premises.

These exact shared counts do not determine where survivors lie. In particular,
global persistence does not imply square-window occupancy, head recurrence, or
spatial uniformity.

## Two Distinct Gaps

The transfer problem has two layers that must not be conflated.

First, within the balanced randomized companion, choosing a harmful pair
uniformly for each parent does not by itself prove that all survivor positions
form a uniformly random subset, or that head events across layers are
independent or sufficiently weakly dependent.

Second, the real filter does not make those random choices. Its harmful indices
come from deterministic residues. Relating that CRT-coupled process to a
companion benchmark requires an additional arithmetic theorem, not an appeal to
the companions’ shared global count.

## Missing Transfer

A successful transfer must control the quantities required by one named
companion theorem. Depending on the theorem, this can include:

- the spatial distribution of survivors along one coherent CRT-coupled lineage;
- realized relative damage `w_r` and cumulative local hazard `D(Q)`, rather
  than marginals taken from changing windows;
- availability or abundance of the chosen local target;
- cross-layer dependence strong enough to justify any probabilistic recurrence
  conclusion; and
- errors caused by structure the randomized model does not preserve, including
  CRT correlations between different gaps, shared-value effects, gap merging,
  and the deterministic relation between residues and killed copy indices.

Exact-quota variants add another distinction: preserving the number of shots
does not preserve their locations or their dependence.

## What Would Resolve It

A positive resolution may take either of two forms:

1. A deterministic arithmetic theorem directly bounds the real sieve’s
   coherent-lineage damage, availability, and recurrence strongly enough to
   obtain the desired survival conclusion.
2. A probability space and coupling are defined rigorously, with quantitative
   spatial and dependence errors that verify every premise of a named companion
   theorem for the coupled real process.

A sharp correlation theorem showing that the required premise fails would also
resolve the obligation, negatively, by identifying where the companion
benchmark ceases to model the real filter.

## What Does Not Resolve It

None of the following alone supplies the transfer:

- exact global `r-2` growth;
- independent harmful-pair choices inside the constructed companion;
- exact shot quotas without location control;
- finite square-window or one-step destruction measurements;
- marginal estimates assembled from different windows instead of one coherent
  lineage; or
- an undefined assertion that the deterministic filter “behaves randomly.”

The first three bullets are not merely unhelpful — their insufficiency is
now proved in a strong form: the [Past-Span Saturation property](
../../properties/sieve-sequence/past-span-saturation-does-not-determine-placement.md)
shows that the complete constraint family expressible from all previous
layers is exactly the per-fiber quota, that every fiber-admissible
placement (of which the real sieve is one point among `r^(phi(P))`)
satisfies every global innovation identity, and that the CRT product
structure keeps placement invisible to the past at any depth. No
accumulation of complete-period identities can discharge this obligation;
only arithmetic coupled to the new layer's residue geometry — windows,
intervals, the head — can see placement.

The 2-gap-specific bullet — CRT correlations between different gaps and
shared-value effects — is likewise characterized at the complete-period
level by the [2-Gap Placement Saturation property](
../../properties/sieve-sequence/two-gap-placement-saturation.md): the
balanced two-class law is exactly a compatible-coloring condition on the
2-gap fiber graph, counts and marginal statistics are coloring-blind
(next-period total `(r-2)G` for every compatible coloring), and the only
complete-period statistics carrying placement are the separation-resolved
pair counts, whose exclusion-intersection term is rigid arithmetic
(`h=0, +-2 mod r`) under the real rule.

## Related

- [Companion Models](../README.md)
- [Balanced Randomized 2-Gap Companion](../balanced-randomized-2-gap/model.md)
- [Global Persistence Independence](../properties/global-persistence-independence.md)
- [Copy-Index Filter Frequency](../../properties/sieve-sequence/copy-index-filter-frequency.md)
- [Phase-Transition Analysis: Relation to the Real Sieve](../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md#8-relation-to-the-real-sieve)
- [Random-Like Merge Survival](../../candidates/random-like-merge-survival.md)
- [Short-Window Discrepancy](../../candidates/short-window-discrepancy.md)
