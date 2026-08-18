# Companion-Model Properties Folder

**Created:** 2026-08-12
**Updated:** 2026-08-12
**Status:** Reorganization in progress

> **Plan correction (2026-08-12):** The earlier `common/` and open-properties
> layouts below are retained as decision history but are superseded by the
> approved Strategy, Expected State, and Implementation Plan at the end of
> this ticket.

## Related Tickets

- `draft-mixed-adversarial-random-companion-2026-08-11.md` — authoring of the
  phase-transition article whose twelve theorem-shaped properties are the source
  material for this split (in progress). Key lesson: the draft deliberately
  separates unconditional global persistence from conditional spatial
  conclusions, and labels every theorem with its premises. This split must
  preserve those premise labels when extracting properties into standalone files.

## Related Articles

- `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md` —
  the source draft. Its twelve proved properties and four model definitions are
  what get extracted.

## Goal

Create a new top-level `companions/` category for **proved properties of
constructed companion models** — a category the repository currently lacks.
The draft article proves twelve theorems about the balanced random, balanced
adversarial, balanced good, and exact-quota random-location companion models.
These are not properties of the real sieve sequence (so they do not belong in
`properties/sieve-sequence/`), not open survival hypotheses (so they do not
belong in `candidates/`), and more than expository prose (so they should not
live only inside an article). Each model gets its own properties subfolder.

## Current State

- The draft article at
  `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md`
  contains twelve theorem-shaped properties plus inline definitions of four
  companion models. Its math has been reviewed and is correct.
- Two companion model files already exist in `candidates/`:
  `balanced-randomized-2-gap-companion-process.md` and
  `balanced-adversarial-2-gap-companion-process.md`. Both are misfiled — they
  are not candidate hypotheses (the adversarial one literally states
  "Candidate hypothesis: N/A"), and neither appears in the candidates README
  numbered index (#1–#25).
- `candidates/README.md` line 6: "`properties/`, which is reserved for
  established mathematical results" — implicitly restricts `properties/` to
  real-sieve results by the way the catalog is used.
- `properties/sieve-sequence/README.md` line 3: "strong sieve-sequence
  properties" — companion-model results do not qualify.
- `VOCABULARY.md` line 507 already recognizes the category: "A heuristic or
  random-model benchmark guides expectation but is not a deterministic theorem
  about the sieve." But there is no folder for proved theorems of that kind.
- No runtime gates apply: this is a Markdown-only reorganization. The
  `green-to-green` rule requires no Scala/Python runs.

## Superseded Expected State

```
companions/
├── README.md
├── common/
│   ├── README.md
│   ├── global-persistence-independence.md       (draft §3)
│   ├── cumulative-local-hazard-law.md           (draft §5)
│   ├── fixed-factor-survival.md                 (draft §5.1)
│   ├── logarithmic-worsening-thresholds.md      (draft §5.2)
│   └── local-survivor-allocation-range.md       (draft §12)
├── balanced-randomized-2-gap/
│   ├── README.md
│   ├── bad-random-square-window-boundary.md     (draft §6)
│   ├── constant-share-trivial-fatality.md       (draft §7)
│   ├── reciprocal-decay-specialization.md       (draft §8.1)
│   ├── log-over-linear-decay-specialization.md  (draft §8.2)
│   └── bad-random-head-boundary.md              (draft §9)
├── balanced-adversarial-2-gap/
│   ├── README.md
│   └── targeted-head-suppression.md             (draft §12 head case, §13)
├── balanced-good-2-gap/
│   ├── README.md
│   ├── cohort-survival.md                       (draft §14)
│   ├── square-window-threshold.md               (draft §15)
│   └── head-threshold.md                        (draft §16)
└── exact-quota-random-location/
    ├── README.md
    ├── survival-factor.md                       (draft §19)
    ├── head-recurrence.md                       (draft §19 Borel-Cantelli)
    └── biased-quota-skew-frontier.md            (draft §20)
```

Each model subfolder mirrors `properties/sieve-sequence/`: a README that
defines the model and holds a short-name registry, then one-claim files. The
`common/` subfolder holds the model-agnostic companion theorems (hazard law,
allocation bounds) that the draft presents before specializing.

The draft article remains the synthesis that cites companion properties by
short name, the way `gap-dynamics-v3.md` cites real-sieve properties.

## Approaches Considered

### A. New top-level `companions/` with per-model subfolders

**Status:** RECOMMENDED

Create `companions/` as a peer of `properties/` and `candidates/`. Each model
gets its own subfolder with a README and one-claim property files. A `common/`
subfolder holds cross-model theorems. Move the two existing companion files
out of `candidates/` into the appropriate model subfolders.

**Strengths:**
- Mirrors the existing `properties/sieve-sequence/` shape, which the project
  already understands.
- Each model's properties are co-located and discoverable as a group.
- Fixes the existing misfiling of the two `candidates/balanced-*-companion-*.md`
  files without disturbing the candidate catalog.
- Makes the "proved but not about the real sieve" category explicit in the
  tree, matching the distinction `VOCABULARY.md` already draws.

**Risks:**
- Adds a top-level directory; requires a README explaining the category.
- Cross-references from the article and from `candidates/` need updating.

**Fallback:** If per-model subfolders feel too granular, collapse to
`companions/` with a flat file list and a single README — but this loses the
grouping the user asked for.

### B. Put companion properties in `properties/sieve-sequence/` with a scope tag

Rejected. The `properties/` README promises "strong sieve-sequence properties";
companion-model results are explicitly not about the real sieve. Filing them
there would break the catalog's contract and mislead anyone using the property
registry.

### C. Keep everything in the article

Rejected. The user's question was specifically about where the theorems and
properties should live as their own files. Leaving them only in the article
defeats the point of citable one-claim notes.

## Assumptions

- The draft article's mathematics is correct (reviewed; all identities,
  asymptotics, table values, and phase boundaries verified numerically and
  analytically).
- The two `candidates/balanced-*-companion-*.md` files are safe to move: they
  are not referenced from the candidates README numbered index, and their
  content is definitions/proofs about constructed models rather than open
  hypotheses.
- Markdown-only reorganization: no Scala, Python, or build gates apply.

## Risks

- Breaking inbound links to the two moved candidate files. Mitigation: grep
  for references before moving and update them.
- Duplicating content between the article and the new property files. Mitigation:
  the property files hold the formal claim, proof, and status; the article
  holds synthesis, phase-diagram tables, and the experimental program, citing
  properties by short name.

## Validation

- `grep -rl` for every cross-reference to moved/created files; confirm none
  dangle.
- Each new property file has: a Status line naming the model and its premises,
  a Meaning section, the formal claim in a math block, the proof, and a short
  name suitable for the registry.
- `git diff --check` passes (whitespace).
- No runtime gates required (Markdown-only).

## Superseded Implementation Plan

1. Create `companions/README.md` defining the category and its scope contract.
2. Create `companions/common/` with README + five cross-model property files
   (§§3, 5, 5.1, 5.2, 12).
3. Create `companions/balanced-randomized-2-gap/` with README + five files
   (§§6, 7, 8.1, 8.2, 9); move `candidates/balanced-randomized-2-gap-companion-process.md`
   in as the model definition section of the README (or a sibling `model.md`).
4. Create `companions/balanced-adversarial-2-gap/` with README +
   `targeted-head-suppression.md` (§§12 head, 13); move
   `candidates/balanced-adversarial-2-gap-companion-process.md` in similarly.
5. Create `companions/balanced-good-2-gap/` with README + three files
   (§§14, 15, 16); the good-sister definition comes from draft §13.
6. Create `companions/exact-quota-random-location/` with README + three files
   (§§19, 19-BC, 20).
7. Update `candidates/README.md` to note the two companion files moved and why.
8. Update inbound references in the draft article and anywhere else grep finds.
9. Final `git diff --check` and link audit.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-12 | The repo has no home for proved properties of constructed companion models. The two existing companion files in `candidates/` are misfiled (one says "Candidate hypothesis: N/A"). | Decided on a new `companions/` top-level category with per-model subfolders. |
| 2026-08-12 | Some draft theorems (§5 hazard law, §12 allocation bounds) are model-agnostic and used by all four specializations. | Added a `companions/common/` subfolder rather than arbitrarily assigning them to one model. |
| 2026-08-12 | The user clarified that `properties/` is proved-only, `candidates/` is its open sieve counterpart, and each companion owns its properties and candidates. | Superseded the open-properties and `common/` layouts with local status directories. |
| 2026-08-12 | Renamed the shared status-neutral companion directory from `common` to `properties`; all six file hashes matched, confirming a content-preserving move. References to `common` are intentionally stale pending one-file repairs. Conditional companion implications remain proved properties when their premises are explicit. | Set the next micro-action to align only `companions/README.md` with the approved shared and per-model `properties/`/`candidates/` lifecycle. |
| 2026-08-12 | The top-level companion index now states the approved shared and model-local claim lifecycle and no longer references `common/`. The planned shared candidates directory does not yet exist. | Set the next micro-action to align only the balanced-randomized model README; retained the old real-sieve property links for the separate flattening migration. |
| 2026-08-12 | Aligned the balanced-randomized README with the approved local lifecycle: shared theorem links now use `companions/properties`, proved model claims are registered under local `properties`, and open model claims are assigned to local `candidates`. Two theorem sources remain at model root and three registered theorem files remain prospective. | Set the next micro-action to move only Bad/Random Square-Window Boundary into the local properties directory without editing its contents. |
| 2026-08-12 | Moved Bad/Random Square-Window Boundary into the randomized model's local properties directory; its post-move SHA-256 matched. The README registry link is now live. Constant-Share remains at model root, so its sibling theorem link is temporarily stale. | Set the next micro-action to move only Constant-Share Trivial Fatality into the same local properties directory, preserving its bytes. |
| 2026-08-12 | Moved Constant-Share Trivial Fatality into the randomized model's local properties directory with matching SHA-256. Its sibling and README registry links now resolve, and no randomized theorem remains beside `model.md`. | Set the next micro-action to repair only Bad/Random's stale cumulative-hazard link using the verified `../../properties/` depth. |
| 2026-08-13 | Repaired Bad/Random Square-Window Boundary's shared Cumulative Local Hazard link to `../../properties/cumulative-local-hazard-law.md`; the target resolves, no `common/` remains in that file, and Markdown whitespace validation passed. | Set the next micro-action to repair only Constant-Share Trivial Fatality's stale Logarithmic-Worsening link with the verified `../../properties/` depth. |
| 2026-08-13 | Repaired Constant-Share Trivial Fatality's Logarithmic-Worsening link to `../../properties/logarithmic-worsening-thresholds.md`; the target resolves, no `common/` remains in that theorem, its Status and 70-line structure are unchanged, and its expected size is 2257 bytes. | Set the next micro-action to replace only the final nonhistorical `companions/common/` prose reference in Local Survivor Allocation Range. |
| 2026-08-13 | Replaced the final nonhistorical `companions/common/` prose token in Local Survivor Allocation Range with `companions/properties/`; no `common/` references remain under companion documents, its proved Status and 123-line structure remain intact, and whitespace validation passed. The next definite proved-only violation is the explicitly open Perfect Scenario headline under properties. | Set the next micro-action to move only `infinite-perfect-scenario-property.md` from real-sieve properties to root candidates, preserving bytes and deferring link and index repairs. |
| 2026-08-13 | The Perfect Scenario move was recovered after its post-check treated Git's unstaged deletion-plus-untracked representation as non-green. The restored source matches the original hash, the destination is absent, and both paths are clean. `git check-ignore` proves no ignore rule applies; the failure was the status expectation, not the move or destination. | Recorded the failed path and set a corrected retry of the same single move using filesystem and HEAD-hash validation while accepting the expected unstaged Git state. |
| 2026-08-13 | Retried the Perfect Scenario relocation with the corrected gate. The candidate now lives under root `candidates/` with its original SHA-256, line count, byte count, headline, and open Status; the old deletion plus new untracked path is the expected unstaged representation and no ignore rule applies. | Set the next micro-action to repair only the moved candidate's two internal article paths from `../../articles/` to `../articles/`. |
| 2026-08-13 | Repaired the moved Perfect Scenario candidate's only two internal article links to `../articles/`; both targets resolve, no stale `../../articles/` remains, and the file retains 565 lines and its open Status. Six inbound occurrences across five documents remain. The proved-property README has one registry row and one item in a continuous 89-item Recommended Reading list. | Set the next micro-action to remove those two README entries and mechanically renumber subsequent reading items so the remaining 88-item list stays continuous. |
| 2026-08-13 | Removed the Perfect Scenario candidate from the proved-property registry and Recommended Reading list, then mechanically renumbered the remaining list to a continuous 1–88. Validation found 87 registry rows, preserved all non-number content under normalized hash `222d2dc0820bd4e8fd378e789fb73ad23492b2addc2bdcdfae6a386dffd82ce0`, retained the pre-existing open-catalog paragraph, and reduced stale inbound references to four across four documents. | Set the next micro-action to repair only the finite generator note's link to the candidate's new root location. |
| 2026-08-13 | Repaired the finite generator note's Perfect Scenario link to `../../candidates/infinite-perfect-scenario-property.md`; the target resolves, the file remains 235 lines and is 7378 bytes, and its adjacent links and Status are unchanged. Three stale inbound links remain. | Set the next micro-action to repair only the recent-prime-sieves deep-dive's Perfect Scenario link to the root candidate. |
| 2026-08-13 | Repaired the recent-prime-sieves deep-dive's Perfect Scenario link to `../../../candidates/infinite-perfect-scenario-property.md`; the target resolves, the research Status and adjacent project-note links are unchanged, and the file remains 654 lines at 23015 bytes. Two stale inbound links remain. | Set the next micro-action to repair only gap-dynamics-v2's Perfect Scenario catalog-table link. |
| 2026-08-13 | Repaired gap-dynamics-v2's Perfect Scenario catalog link to `../../candidates/infinite-perfect-scenario-property.md`; the target resolves, the row and adjacent table entries are unchanged, and v2 remains 2595 lines at 105205 bytes. Only v3 retains the stale property path. | Set the next micro-action to repair only gap-dynamics-v3's matching table link. |
| 2026-08-13 | Repaired gap-dynamics-v3's Perfect Scenario link to the root candidate; no nonhistorical former-path references remain. Classified every section of the unwanted open aggregate: fourteen numbered entries and all deferred items duplicate existing candidates; entries 4, 15, and 17 contain unique mathematical obligations; entry 16 is formalization tracking; introduction and Related are archive scaffolding. | Set the next micro-action to remove only the open aggregate's inbound paragraph from the proved-property README while leaving the aggregate intact for one-at-a-time extraction. |
| 2026-08-13 | Removed the open aggregate's sole inbound paragraph from the proved-property README while preserving its 87-row and 1–88 catalogs and leaving the aggregate byte-identical at SHA-256 `32ba486a2d1df0328cca1cc94933b896b28642b0663a24ea29dd95cb4a3ecd8c`. Research of entry 15 confirmed that exact global growth does not transfer spatial placement: the randomized model omits CRT cross-gap correlations, shared-endpoint and merge effects, and deterministic residue-to-copy-index structure. | Set the next micro-action to create only the shared companion CRT-transfer obligation note, without claiming an unproved coupling or stochastic law for the real sieve. |
| 2026-08-13 | Extracted open-catalog entry 15 into the 105-line shared companion candidate `crt-coupled-real-sieve-transfer.md`; its nonclaims and seven links validate. Entry 17 research shows that Safe-Zone Exhaustion Curve mixes two proved facts with one unproved short-interval estimate and two failed localization paths. | Set the next micro-action to create only a focused root safe-zone tight-bound candidate before narrowing the mixed-status property note. |

## Strategy

Treat the real sieve as the repository default: a claim moves from
`candidates/` to `properties/` when it is proved. Treat every companion model
as a self-contained domain with `model.md`, `README.md`, `properties/`, and
`candidates/`. Shared companion claims live in `companions/properties/` or
`companions/candidates/` according to their status. Preserve existing files by
moving rather than deleting them, and repair affected links after each move.

First correct the partial companion/open-catalog layout introduced by this
ticket. The broader flattening of `properties/sieve-sequence/` is a separate,
high-reference migration and must not be bundled into that cleanup.

## Approved Expected State

```text
properties/
|-- README.md
`-- *.md                         proved sieve claims

candidates/
|-- README.md
`-- *.md                         open sieve claims

companions/
|-- README.md
|-- properties/                 shared proved claims
|-- candidates/                 shared open claims
`-- <model>/
    |-- README.md
    |-- model.md
    |-- properties/
    `-- candidates/
```

The status directory is local to its subject. A proved candidate moves from
that subject's `candidates/` directory to its `properties/` directory.

## Current State (Approved Plan)

- The shared companion directory move is complete: the README and five theorem
  notes now live under `companions/properties/`; `companions/common/` is absent.
- The move was content-preserving: the six-file before/after SHA-256 manifest
  matched exactly.
- The top-level and randomized companion indexes are aligned; the two
  randomized theorem links use verified shared-property paths. The final
  `companions/common/` self-description was changed to
  `companions/properties/`; no `common/` references remain in nonhistorical
  companion documents.
- `companions/README.md` now documents shared and model-local `properties/` and
  `candidates/`, while deliberately preserving the current real-sieve property
  links until the separate root-property flattening.
- The randomized README now points shared theorems to `companions/properties/`,
  defines local `properties/` and `candidates/`, and registers all five proved
  model claims under local `properties/`. The two existing theorems now live
  there byte-for-byte with matching hashes; their mutual sibling links and
  README registry links resolve. The other three destinations are prospective.
- The first unique open-catalog obligation is extracted:
  `companions/candidates/crt-coupled-real-sieve-transfer.md` exists as a
  105-line, 4963-byte shared transfer note. It makes no real-sieve bound,
  coupling, spatial-uniformity, or mixing claim; all seven Related links
  resolve.
- The proved-property README no longer advertises the open aggregate: its only
  inbound paragraph was removed, leaving the README at 570 lines and 50258
  bytes with 87 registry rows and continuous Recommended Reading 1–88.
  `properties/sieve-sequence/open/README.md` remains intact and untracked at
  261 lines and 12144 bytes with SHA-256
  `32ba486a2d1df0328cca1cc94933b896b28642b0663a24ea29dd95cb4a3ecd8c`;
  it now has no nonhistorical inbound link.
- `infinite-perfect-scenario-property.md` now lives under root `candidates/`
  with its explicit open Status. Its two internal article links use the correct
  `../articles/` depth and resolve. The proved-property README no longer
  registers or recommends it: its registry has 87 rows, its Recommended
  Reading list is continuous from 1–88, the normalized preservation hash is
  `222d2dc0820bd4e8fd378e789fb73ad23492b2addc2bdcdfae6a386dffd82ce0`,
  and the pre-existing open-catalog paragraph was preserved. The finite
  generator link now points to the root candidate and resolves while preserving
  its 235-line structure. The recent-prime-sieves deep-dive also points to the
  root candidate; its research Status and 654-line structure are unchanged, and
  it is 23015 bytes. gap-dynamics-v2 now points to the root candidate; its table
  row fields and 2595-line structure are unchanged, and it is 105205 bytes.
  gap-dynamics-v3 now also points to the root candidate; its table fields and
  2330-line structure are unchanged, and it is 105643 bytes. No nonhistorical
  reference to the former property path remains. The relocation and link
  repair are complete. The moved candidate is 565 lines and 13851 bytes.
- The companion tree is incomplete, and existing companion documents contain
  stale or planned links.
- 2026-08-19: `companions/balanced-good-2-gap/` and
  `companions/exact-quota-random-location/` — steps 5 and 6 of the superseded
  plan above, previously unexecuted (their folders existed but were never
  populated, confirmed empty at the time) — were reconstructed from the
  phase-transition draft article's current §5.2-§5.5 (protective parent
  policy) and §7.1 (exact-quota random-location), following the balanced
  randomized/adversarial siblings' file structure: `model.md` + a
  `properties/` file per proved theorem (3 each) + `README.md`. All internal
  links verified to resolve. The stale "its model folder is not yet
  populated" note in `companions/properties/position-blind-index-spectrum.md`
  was corrected to link the new model. Both remaining balanced-adversarial's
  missing `README.md` and the 3 aspirational rows in
  `balanced-randomized-2-gap/README.md`'s registry (reciprocal-decay,
  log-over-linear-decay, bad-random-head-boundary — none of which exist as
  files) are pre-existing gaps, out of scope here.
- Flattening the roughly 90 property notes has no filename collisions, but it
  affects hundreds of path mentions, including an operational reference in
  `scripts/retire_property_numbers.py`. It is not a Markdown-only cleanup and
  must preserve overlapping user changes.

## What is Learned

- The project lifecycle is `candidates/` to `properties/`: open claims are
  promoted only when proved.
- `properties/` and `candidates/` already have the sieve sequence as their
  default subject, so repeating `sieve-sequence/` adds no information.
- Companion models are separate subjects. Their definitions, proved results,
  and open claims belong together under each model.
- Shared companion claims still need an explicit proof-status directory;
  `common/` alone is insufficient.
- The companion root index can describe the complete lifecycle before every
  planned directory exists, provided the missing directory remains explicit in
  Current State and is created by a subsequent scoped action.
- A theorem with explicit unproved real-sieve transfer premises belongs in a
  companion `properties/` directory when the conditional implication itself is
  proved. Its status must keep those premises visible; the unresolved premise
  or transfer obligation belongs in the corresponding `candidates/` directory.
- A registry may point prospectively into the approved status directory while
  moves are performed one file at a time, but Current State must distinguish
  existing misplaced files from not-yet-created claims.
- A note whose headline assertion explicitly says it is open belongs in
  `candidates/` even when it contains a proved finite supporting theorem. Mixed
  proved support does not promote an unresolved headline claim to
  `properties/`.
- An unstaged relocation of a tracked file to a new path is normally represented
  as a tracked deletion plus an untracked destination. That is not evidence
  that the destination is ignored when filesystem and hash checks prove the
  relocation.
- `candidates/infinite-perfect-scenario-property.md` is not ignored by any
  repository rule; no `.gitignore` exception is needed or justified.

### Open-Catalog Routing Map

- Entries 1, 2, 3, 5–14, and 18 duplicate existing root candidates; no
  extraction is needed.
- Entry 4 contains a unique combined capacity-frontier and safe-index
  intersection obligation; route it later to one focused root candidate.
- Entry 15 is extracted to
  `companions/candidates/crt-coupled-real-sieve-transfer.md`.
- Entry 16 is a Stainless formalization obligation, not a mathematical
  candidate; preserve it in verification tracking.
- Entry 17 is the open tight safe-zone estimate currently mixed with two proved
  results. Preserve the estimate and its two failed localization paths in one
  root candidate before narrowing the property note.
- The Deferred section duplicates existing candidates; the introduction and
  Related section are aggregate scaffolding only.
- The companion transfer obligation must not claim that the deterministic real
  sieve is stochastic or that exact descendant growth implies spatial
  uniformity. The randomized model omits cross-gap CRT correlations,
  shared-endpoint and merge effects, and the deterministic residue-to-copy-index
  relation.
- Safe-Zone Exhaustion Curve contains three evidence statuses: an exact
  boundary at `p^2`, a cited universal lower bound of order `2p`, and the
  unproved estimate `hat A(p)=(p^2-p) product_(r<p)(1-1/r)`. The open part is a
  short-interval localization claim, not a consequence of Mertens' global
  density product. Its reported zero overshoot violations for prime heads
  13–131 are finite evidence only.

## Failed Paths

- **Open catalog under properties:** `properties/sieve-sequence/open/`
  duplicates `candidates/` and contradicts the proved-only contract. Retry only
  if that contract changes.
- **Shared `companions/common/`:** this groups claims by applicability but not
  by proof status. Retry only if the local claim lifecycle is abandoned.
- **Theorems directly beside `model.md`:** this mixes model definition and
  result status. Retry only if status is represented by another equally clear
  mechanism.
- **Perfect Scenario move with incorrect Git-status gate:** the tracked
  property was moved byte-for-byte to root `candidates/`, but the expected
  unstaged deletion-plus-untracked representation was treated as a failed
  relocation and recovered under red-cascade. Retry only with a corrected
  post-check that accepts this unstaged representation and compares the
  destination bytes with the tracked HEAD source hash. The corrected retry
  succeeded; do not repeat the recovery or add ignore rules.

## Open Concerns

- Before the unlinked aggregate moves, extract entry 4 and entry 17 and preserve
  entry 16 in verification tracking. For entry 17, create the candidate first;
  only afterward remove the unproved estimate and failed paths from the proved
  property note.
- Some existing property notes contain open or research material and need a
  later claim-by-claim classification rather than a bulk assumption.
- Flattening `properties/sieve-sequence/` affects hundreds of references and
  at least one operational Python path. It requires its own baseline and
  regression plan.
- The partial companion tree currently contains broken links to planned files.

## Approved Implementation Plan

1. Replace `companions/common/` with shared `properties/` and `candidates/`,
   then place model-specific claims in each model's local status directory.
2. Route the unique obligations from the aggregate open README, then move that
   rejected catalog out of the property tree and remove its inbound link.
3. Complete missing companion model definitions and registries one claim at a
   time, preserving premise and verification labels.
4. Audit and repair companion links, then validate Markdown whitespace and
   local links.
5. Plan the root-property flattening separately, including Python gates for
   operational path changes.

## Next Action

Create only `candidates/safe-zone-exhaustion-tight-bound.md` as a focused root
candidate preserving Property 3 and its two failed localization approaches.
Do not edit `safe-zone-exhaustion-curve.md`, the open aggregate, candidate
indexes, presentation code, or any other file. The note must label the proposed
bound for primes `p>=13` unproved, distinguish finite evidence through 131 from
proof, state the missing short-interval theorem, and keep the proved elementary
and cited universal baselines separate.
