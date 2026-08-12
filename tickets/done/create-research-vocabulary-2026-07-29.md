# Create a Canonical Research Vocabulary

**Created:** 2026-07-29
**Updated:** 2026-07-29
**Status:** Complete
**Depends on:** `audit-one-layer-global-scope-2026-07-29.md` (complete)

## START HERE

Create `VOCABULARY.md` at the repository root. Its immediate purpose is to
make every research document state the same three coordinates explicitly:
the population being discussed, the mathematical scope of the claim, and the
evidence or proof status. Then link the candidate and property catalogs to it.

## Related Tickets

- `audit-one-layer-global-scope-2026-07-29.md` — corrected several places where
  one-layer, conditioned-chain, and global statements had been conflated. The
  audit demonstrates that scope qualifiers must be part of the canonical
  vocabulary rather than left to local convention.
- `verify-19-21-escape-wall-2026-07-27.md` — separates local ellipse clearance
  from payment of the weighted global budget. That distinction should be
  expressible in stable, reusable terms.

## Goal

Create a concise canonical vocabulary for the sieve-sequence research so that
candidates, properties, articles, empirical reports, and future tickets use
the same terms for objects, transformations, proof scope, quantifiers, and
status. Completion requires the permanent document plus discoverable links
from the main candidate and property catalogs.

## Strategy

Consolidate rather than replace local notation. The root document will define
cross-cutting meanings and require local documents to map any specialized
symbols to them. It will prioritize distinctions that have caused real
reasoning errors: full period versus local window, one layer versus a
conditioned chain, survival versus final certification, exact identity versus
bound, and empirical support versus mathematical or Stainless proof.

This approach is preferred to expanding each catalog independently because
duplicated definitions would drift. A single giant mathematical notation
index was rejected because article-specific symbols remain easier to read
when defined near their use.

## Current State

- `candidates/README.md` has a small Common Notation section.
- `properties/sieve-sequence/README.md` has a Status Vocabulary section.
- `PROOF_GUIDE.md` governs proof presentation.
- `VOCABULARY.md` now defines the shared terminology, scope qualifiers,
  quantifiers, proof/evidence statuses, collision language, and writing
  checklist.
- Its internal links resolve and `git diff --check` passes.
- Root `README.md` links to the vocabulary.
- `candidates/README.md` maps its local `p,q` notation to the canonical
  filter-prime and future-head roles.
- `properties/sieve-sequence/README.md` identifies its status labels as a
  local subset of the canonical evidence taxonomy.
- All planned permanent documentation edits are complete.
- The final audit confirmed every new link, all required vocabulary sections,
  clean Markdown diffs, and preservation of the unrelated staged empirical
  CSV.

## Expected State

- Root `VOCABULARY.md` defines canonical cross-cutting language.
- The document covers objects, transformations, scope, quantifiers, evidence
  status, budgets/energies, and common non-equivalences.
- Root `README.md`, `candidates/README.md`, and
  `properties/sieve-sequence/README.md` link to it.
- Existing local notation remains valid where it is explicitly mapped and
  does not conflict with the canonical meanings.

## Approaches Considered

### Root canonical vocabulary with local mappings

**Status:** RECOMMENDED

Define shared meanings once and let specialized documents retain local symbols
after mapping them.

**Strengths:** Discoverable, resistant to drift, and suitable for all research
artifacts.

**Risks:** It can become too broad or silently redefine symbols already used
with different meanings.

**Fallback:** Split a later notation index from the conceptual vocabulary if
the symbol table grows beyond what is useful for shared language.

### Separate glossaries in each catalog

**Status:** NOT SELECTED

**Strengths:** Each glossary could be narrowly tailored.

**Risks:** Duplicates the most important definitions and recreates the drift
this work is intended to prevent.

**Fallback:** Keep short local notation sections, but make them subordinate to
the root vocabulary.

## Assumptions

- Cross-cutting terminology can be standardized without changing established
  mathematical definitions.
- Existing specialized symbols need not all be renamed; explicit mappings and
  warnings are sufficient.
- Validation: compare every proposed definition with current candidate and
  property usage before publishing it.

## What is Learned

- The repository already has useful local notation and status language, but
  neither is canonical across document families.
- The highest-value vocabulary is not a list of nouns alone. It must encode
  scope and epistemic status because those qualifiers determine what a claim
  actually proves.
- “Candidate” is overloaded between a research hypothesis and a numerical
  prime candidate, so the canonical document should require a qualifier.
- `M_i` is already used both for actual harmless survivors and for a one-step
  multiplicative main term. The vocabulary therefore standardizes concepts,
  not universal symbols, and recommends `N_{i+1}` or `a_iN_i` in new shared
  work.
- `A_i`, `T`, `G`, and the prime letters also have role collisions. Explicit
  local definitions are safer than retroactive global renaming.

## Failed Paths

- No attempted implementation has failed.
- A single exhaustive index of every article symbol was pre-empted because it
  would duplicate local definitions and be difficult to maintain. Reconsider
  only if repeated symbol collisions remain after the cross-cutting vocabulary
  is adopted.

## Open Concerns

- Symbols such as `T` and `G` have local meanings in existing documents. The
  vocabulary must not imply that an unqualified symbol has one universal
  meaning when the repository does not support that claim.
- “Verified” must name its verifier or evidence class; otherwise readers may
  confuse Stainless verification with a finite empirical check.
- The document should be prescriptive enough to prevent ambiguity without
  forcing long boilerplate into every proof.

## Validation

- Confirm all relative links resolve.
- Search the new document for every planned scope and status distinction.
- Run `git diff --check`.
- No Stainless verification is required because all changes are Markdown.
- Confirm the unrelated staged empirical CSV remains untouched.

## Implementation Plan

1. Create `VOCABULARY.md` with canonical definitions and usage rules.
2. Link it from `README.md`.
3. Link it from `candidates/README.md`.
4. Link it from `properties/sieve-sequence/README.md`.
5. Audit links and terminology, then close this ticket.

## Next Action

Done. Apply the writing checklist in `VOCABULARY.md` when new cross-cutting
research terms or claims are introduced.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-29 | Search found no canonical glossary. The closest material is split between candidate notation, property status language, and the proof guide. | Create a root vocabulary focused on shared meaning and ambiguity prevention. |
| 2026-07-29 | The canonical draft is complete. Existing symbol collisions mean shared meanings can be standardized safely, but a universal symbol table cannot. | Link the root README to the vocabulary, then link both research catalogs. |
| 2026-07-29 | The root README now exposes the vocabulary at the project entry point. | Link the candidate catalog's Common Notation section to the canonical meanings. |
| 2026-07-29 | The candidate catalog now keeps its established `p,q` notation while mapping those symbols to canonical semantic roles. | Link the property catalog's status section to the full evidence taxonomy. |
| 2026-07-29 | The property catalog now presents its three common labels as a subset of the full taxonomy. All permanent edits are complete. | Run the final cross-file audit and close the ticket if clean. |
| 2026-07-29 | Final audit passed: links resolve, required sections are present, `git diff --check` is clean, and unrelated staged data is untouched. | Ticket complete; move to `tickets/done/`. |
