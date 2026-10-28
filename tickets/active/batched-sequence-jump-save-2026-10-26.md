# Batched sequence jump — documentation save

## START HERE

Micro-goal: extend the existing batch property with the exact sequence-level
identity: repeated expansion followed by one union filter reconstructs any later
prime-headed sequence after cyclic gap reconstruction and final rotation.

## Goal

Save the user's finite multi-stage jump construction in the existing indexed
property note, distinguishing a mathematical derivation from Stainless verification.

## Strategy

Extend `properties/sieve-sequence/exact-batched-two-gap-survival.md` rather than
create a duplicate. Use canonical reduced residues, a product of incoming primes,
intersection of divisibility predicates, and final head anchoring. Include the
special choice of the first prime above the starting head squared.

## Current State

Documentation complete. The existing property now includes exact reconstruction
of any later prime-headed sequence by one expansion-and-filter batch. Critic
semantic post-check and Monitor post-check passed. Markdown whitespace, paired
fences, and relative-link checks passed; no runtime validation was required.

## What is Learned

- The existing note already proves the complete-period batched 2-gap count.
- `SpecSieveSequence.scala` defines acceptance as passing all smaller prime
  filters and being at least the head; this supports the sequence identity.
- Intermediate rotations affect representation, not the retained residue set.
- Cyclic wrap-around and the final head rotation must be explicit.
- The retained expanded residues are exactly R_q; sorting, cyclic differences,
  and anchoring at q reconstruct the later stream. The first prime above p^2
  is an optional choice of destination, not a precondition of the identity.

## Related Work

- [Fixed-window shot budgets](fixed-window-shot-budget-2026-10-26.md): finite
  batch bookkeeping and local survivor certificates; no general placement proof.
- [Architecture explanation](explain-sieve-sequence-architecture.md): existing
  expand/filter/sort/gap/rotate representation discussion.
- Existing property: `properties/sieve-sequence/exact-batched-two-gap-survival.md`.

## Alternatives, Risks, and Assumptions

A separate note would duplicate the existing batch construction. Instead add a
sequence-level section there. Assume p and q are primes with q>p, all smaller
prime filters installed at p, and the complete period is available. Main risks
are omitting p, filtering q itself, forgetting wrap-around, or asserting local
survival from a complete-period identity. Validate these by direct set equality.

## Validation

Markdown-only; no executable instructions or runtime changes. Check the exact
filter range p<=r<q, canonical residue lifts, proof, cyclic final gap, head
anchoring, source links, and whitespace. Do not claim a new verified Scala theorem.

## Failed Paths

None attempted. A short-window survival conclusion is excluded because the
identity alone does not control locations of surviving residues; revisit only
with an additional proved placement bound.

## Open Concerns

No dedicated Stainless verification of the multi-stage identity is added.

## Next Action

None for this save. A dedicated Stainless proof or a short-window placement
result would be separate work; neither is claimed or required here.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-26 | Existing batch note covers counts but not explicit reconstruction of the later sequence. | Critic PASS and Monitor pre-PASS; created documentation ticket. |
| 2026-10-27 | Full-period expansion and union filtering recover exactly the later residue set and anchored stream. | Added the property; Critic and Monitor post-checks PASS; whitespace, fences, and links PASS. Documentation save complete. |
