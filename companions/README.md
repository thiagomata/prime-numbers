# Companion Models

This folder collects constructed companion models — stochastic and adversarial
processes that share some structural mechanics with the real sieve sequence
but are not the real sieve — together with their proved properties and open
candidates.

Each named model has a `model.md`, a README registry, and local `properties/`
and `candidates/` directories. Shared proved claims live in
[`properties/`](properties/README.md); shared open claims and transfer
obligations live in `candidates/`.

## Scope Contract

Companion claims use the same lifecycle as real-sieve claims: an open claim
lives under the appropriate `candidates/` directory and moves to the matching
`properties/` directory when proved. Companion properties are a distinct
evidence category. They are **not**:

- **Properties of the real sieve sequence.** They are not filed under
  `properties/sieve-sequence/`, whose catalog is reserved for established
  results about the real modular filter. A companion property describes what a
  constructed model does, not what the real sieve does.
- **Real-sieve candidates.** Open companion claims are filed locally under a
  model's `candidates/` directory or, when shared, under
  `companions/candidates/`. The root [`candidates/`](../candidates/README.md)
  remains reserved for open claims about the real sieve sequence.
- **Synthesis articles.** They are not filed under `articles/`. An individual
  proved theorem about a companion model deserves its own citable one-claim
  file so that articles, candidates, and other properties can link to it by
  short name.

They **are**:

- proved mathematical theorems about explicitly constructed processes;
- useful as reference points for interpreting the real sieve's behavior
  (what would local survival look like *if* the real filter's arithmetic
  behaved like uniform, targeted, or optimal placement); and
- clearly labeled with the premises each theorem assumes, and the model it
  belongs to.

The project vocabulary recognizes this category in
[`VOCABULARY.md`](../VOCABULARY.md): *"A heuristic or random-model benchmark
guides expectation but is not a deterministic theorem about the sieve."* This
folder is where the proved-theorem instances of that category live.

## How To Read A Companion Property

Every companion property file states:

1. **Status:** which model it belongs to and which premises it assumes.
   Spatial-uniformity, optimistic quadratic supply, head availability, and
   cross-layer mixing are premises, not facts about the real sieve. A property
   that needs them says so in its Status line.
2. **Meaning:** what the theorem says in plain language.
3. **Formal claim:** the statement in a `math` block.
4. **Proof:** the derivation, with bracketed justification labels matching
   [`PROOF_GUIDE.md`](../PROOF_GUIDE.md).

A companion property whose premises are not satisfied by the real sieve does
not transfer. Transferring any companion result to the real modular filter is a
separate open research obligation, not a corollary.

## Model Index

| Model | Folder | What it randomizes or optimizes |
|---|---|---|
| Shared proved claims | [`properties/`](properties/README.md) | Hazard law, allocation bounds, fixed-factor and logarithmic-worsening thresholds used by multiple specializations |
| Shared open claims | `candidates/` | Cross-model conjectures and transfer obligations not yet proved |
| Balanced random | [`balanced-randomized-2-gap/`](balanced-randomized-2-gap/README.md) | Two harmful copy indices drawn uniformly per parent |
| Balanced adversarial | [`balanced-adversarial-2-gap/`](balanced-adversarial-2-gap/README.md) | Two deletions spent on a chosen target region whenever possible |
| Balanced good | [`balanced-good-2-gap/`](balanced-good-2-gap/README.md) | Two deletions spent away from the target whenever possible |
| Exact-quota random location | [`exact-quota-random-location/`](exact-quota-random-location/README.md) | Exact CRT shot count retained, shot locations drawn uniformly without replacement |

All four models preserve the real sieve's exact `r-2` descendant law
(`N_{k+1}=(r_k-2)N_k`); see
[Global Persistence Independence](properties/global-persistence-independence.md).
They differ only in which two copies die.

## Related Work

- [Phase-transition article (draft)](../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
  — the synthesis that assembles companion properties into a relative-hazard
  and allocation phase diagram.
- [Sieve-Sequence Property Catalog](../properties/sieve-sequence/README.md) —
  proved properties of the real modular filter.
- [Candidate Catalog](../candidates/README.md) — open sufficient conditions for
  real-sieve 2-gap survival.
