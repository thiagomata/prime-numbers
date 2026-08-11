# Deep Study: Sieve Sequence And Gap Dynamics

## Goal

Build a source-grounded understanding of `articles/chapter6/sieve-sequence.md`
and `articles/chapter6/gap-dynamics.md` sufficient to answer later deep,
technical questions about their definitions, proof architecture, verified
results, conditional results, limitations, and mathematical implications.

## Current State

The two articles are current but sit over several proof surfaces: the
linear-scan specification, canonical derived cycles, operational gap cycles,
transition helpers, and specialized property objects. Recent formatting
tickets changed presentation without changing mathematical claims. Existing
architecture and property-catalog tickets record important context and open
proof boundaries.

## Expected State

- Every important article concept is mapped to its definition and proof role.
- Verified claims are traced to the exact Scala `.holds` functions.
- Conditional, mathematical-only, empirical, and open claims remain clearly
  distinguished from Stainless-verified theorems.
- The relationship between residue filtering, gap copying/merging, rotation,
  survivor counts, safe windows, and twin-gap claims is understood end to end.

## Related Tickets And Context

- `tickets/sieve-sequence-epic.md`
- `tickets/active/explain-sieve-sequence-architecture.md`
- `tickets/active/sieve-sequence-v2-article.md`
- `tickets/active/sieve-sequence-property-catalog.md`
- `tickets/active/sieve-sequence-article-guideline-formatting-2026-07-23.md`
- `tickets/active/gap-dynamics-math-formatting-2026-07-23.md`
- `tickets/future/math-only-sieve-gap-survival-article.md`
- `tickets/done/gap-dynamics-v2-research-update.md`

## Alternatives, Risks, And Assumptions

- Reading only the prose was rejected because similarly named proof surfaces
  have different semantic roles.
- Re-running verification is unnecessary because this is a read-only study;
  existing `.holds` declarations and their bodies are the evidence to inspect.
- Assume article source links may omit supporting lemmas; validate by searching
  all relevant Chapter 6 `.holds` functions and reading cited bodies.
- Risk: mathematical implications may be stronger than the verified result.
  Validate theorem preconditions and article qualification language together.
- Risk: historical tickets may describe superseded designs. Treat current
  source and current articles as authoritative, using tickets only for context.

## Hypotheses And Validation

1. The spec/canonical/cycle separation explains most apparent duplication.
   Validate against the main data models and equivalence property objects.
2. Copy-or-merge dynamics follows directly from filtering a sorted survivor
   list, while persistence claims require additional capacity or window facts.
   Validate against gap/filter lemmas and the capacity-argument learning article.
3. Head changes and rotation are the principal boundary between same-head
   results and a full next-stage correctness theorem. Validate against next-level
   and period/head property objects plus open-work sections.

## Final Validation

- Re-read both articles after source tracing.
- Cross-check their claims against `OBJECTS.md`, `LEARNINGS.md`,
  `PROOF_GUIDE.md`, relevant `.holds` bodies, and directly related articles.
- Record a concise learning log identifying the stable mental model and known
  proof boundaries without modifying code or published articles.

## Learning Log

- 2026-07-23: Ticket created after locating the current articles, architecture
  ticket, recent formatting tickets, property catalog, epic, and mathematical
  follow-up context. Deep source tracing remains read-only.
