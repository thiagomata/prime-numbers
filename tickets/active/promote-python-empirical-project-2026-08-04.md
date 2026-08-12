# Promote the Python Empirical Project

**Created:** 2026-08-04
**Updated:** 2026-08-04
**Status:** In Progress

## START HERE

The duplicated stale `v1.MainTest` expectations are repaired: all 230 Scala
tests pass, and post-change `just verify-ch 1` through `just verify-ch 6` is
green with zero invalid and zero unknown in every chapter. Both legacy Python
compatibility gates also exit 0 with explicit `RESULT: PASS`. The first
destination slice, `empirical/sieve-sequence/pyproject.toml`, is complete and
fully validated. The minimal package bootstrap is also complete and passes its
destination import check plus both Python compatibility gates. The canonical
window core is now present and behavior-identical to the green legacy core.
Three initially identified stabilization-rationale blocks in legacy
`lib_lineage.py` are corrected, and both Python compatibility gates exit 0 with
explicit `RESULT: PASS`. The initially identified contradictory paragraph in
`candidates/analysis/FINDINGS_lineage.md` is also corrected. A broader audit
found additional stale full-period-frontier claims that must be cleaned before
the lineage CLI is added. Canonical window
and lineage cores are now present and behavior-identical to their green legacy
sources. The destination-owned window test passes with import-only normalized
identity, and the destination-owned lineage test now does too. The next action
is exactly one `sieve-sequence-lineage` console-script entry in
`pyproject.toml`; keep all legacy files intact.

## Related Tickets

- `tickets/active/empirical-candidate-stress-test-2026-07-23.md` — introduced
  the window-measurement Python implementation and its interpretation rules.
- `tickets/active/lineage-experiment-2026-07-23.md` — introduced the lineage
  experiment and stable-small-k comparison.
- `tickets/archived/empirical-g-local-crossover.md` — introduced the redundant
  Chapter 7 Scala prime-counter runner and its legacy CSV.

## Goal

Make the Python empirical analysis a first-class, independently installable and
testable project with root-level commands, preserve its current datasets and
results, correct the invalid stability rationale, migrate live documentation,
and then remove the redundant Chapter 7 Scala runner and legacy CSV explicitly
identified by the user.

## Strategy

Proceed compatibility-first from a green baseline. First repair the duplicated
stale `MainTest` expectation atomically, then run the Scala regression gates.
Add the new Python package alongside the legacy `candidates/analysis` entry
points, prove equivalent behavior with its tests, expose root `just` commands,
and only then retire the legacy Python locations. Preserve existing datasets in
place during the initial package migration; any data relocation or regeneration
is a separate phase after schema and output compatibility are established.

The Python package is the canonical fast empirical implementation. Chapter 6
remains the verified specification, and the Spark implementation remains the
large full-cycle implementation. The unrelated Chapter 7 `@extern` prime
counter is not part of the sieve-sequence implementation and will be removed
only after the Python replacement gates are green.

Validation is language-scoped by the user's 2026-08-04 decision: Python-only
changes receive relevant Python import, unit, and CLI validation without Scala
tests or Stainless; Scala-only changes receive relevant Scala tests and
Stainless validation without Python gates; Markdown-only changes receive
neither unless they change executable instructions; mixed-language or shared
orchestration changes receive the applicable gates for every affected language.

## Current State

- The two mirrored expected-output strings in `src/test/scala/v1/MainTest.scala`
  now match the captured production fallback output. `just test` reports 230
  run, 230 succeeded, and 0 failed.
- A fresh chapter-by-chapter baseline completed on 2026-08-04: chapter 1 has
  16 valid, chapter 2 has 1,374 valid, chapter 3 has 1,602 valid, chapter 4 has
  2,995 valid, chapter 5 has 2,145 valid, and chapter 6 has 4,390 valid. Every
  chapter reports zero invalid and zero unknown. The same counts passed again
  after the test change.
- The working tree contains substantial unrelated user changes, including the
  staged `data/sieve-sequence/first_gaps_per_seq.csv`. They are outside this
  ticket and must not be edited, staged, interpreted as migration output, or
  reverted.
- The current empirical Python implementation and tests live under
  `candidates/analysis/`. Both Python test scripts pass in its existing virtual
  environment.
- A fresh compatibility run with bytecode writes disabled completed on
  2026-08-04: `test_measure.py` exited 0 with `RESULT: PASS`, followed by
  `test_lineage.py` exiting 0 with `RESULT: PASS`. No runner generated data.
- `empirical/sieve-sequence/pyproject.toml` now defines the
  `sieve-sequence-empirical` project, Python 3.11+, and the existing NumPy and
  SymPy dependencies, with explicit `src/` package discovery. Exact TOML and
  local discovery assertions plus all four Python gates pass.
- Its scripts table now exposes `sieve-sequence-window` and
  `sieve-sequence-lineage`. Exact two-entry TOML, callable imports, an explicit
  temporary max=7 two-row window CSV, and an explicit temporary Q=11 lineage
  CSV with three rows and `r=[3,5,7]` pass. All four Python gates pass and
  repository data is unchanged; no Scala/Stainless validation applies.
- `empirical/sieve-sequence/README.md` now documents the first-class install,
  explicit-path console and source workflows, destination tests, output policy,
  exact stable-small-`k` boundary, guarded diagnostics, and finite-evidence
  limits. Fresh unit, import, dense, sparse, and lineage checks pass with exact
  temporary schemas and no repository data change.
- Root `.gitignore` now covers `.venv/` and `*.egg-info/`. Both intended
  canonical generated paths match those rules, and no tracked path matches
  either pattern.
- The canonical `.venv` independently installs project `0.1.0`, NumPy `2.5.1`,
  and SymPy `1.14.0`; both console executables and exact entry mappings pass,
  and the ignored environment/metadata add no Git-status noise.
- Root `empirical-test` is discoverable and runs both canonical suites through
  the independent environment with exactly two `RESULT: PASS` markers and no
  repository data write.
- Root `empirical-window` is discoverable and its temporary max=7 run produces
  the exact 18-column schema and two rows without changing repository data.
- Root `empirical-window-sparse` is discoverable and its temporary
  stride=2/max=11 run produces the exact 18-column schema and three rows without
  changing repository data.
- Root `empirical-lineage` is discoverable; its q=19 dry-run derives the Q-safe
  default path, and an explicit temporary Q=11 run produces the exact 22-column
  schema, three rows, and `r=[3,5,7]` without changing repository data.
- The live-reference audit found exactly 18 non-ticket files with legacy
  implementation names:
  - Canonical naming fixes:
    `empirical/sieve-sequence/src/sieve_sequence_empirical/window.py`,
    `empirical/sieve-sequence/src/sieve_sequence_empirical/lineage.py`, and
    `empirical/sieve-sequence/tests/test_window.py`.
  - Canonical source/runner/test references while preserving numerical
    provenance: `empirical/sieve-sequence/capacity-density-candidates.md` and
    `empirical/sieve-sequence/hereditary-shot-spacing.md`.
  - Canonical command/findings references while preserving measured values:
    `candidates/README.md`,
    `candidates/bounded-consecutive-destruction.md`,
    `candidates/bounded-post-merge-spacer.md`,
    `candidates/distinguished-head-spacer.md`,
    `candidates/hereditary-shot-spacing-capacity.md`,
    `candidates/local-pattern-residue-balance.md`,
    `candidates/local-surplus.md`, `candidates/protected-cluster.md`,
    `candidates/protected-endpoints.md`,
    `candidates/random-like-merge-survival.md`,
    `candidates/refuted/bounded-cyclic-destruction-run-two.md`,
    `candidates/short-window-discrepancy.md`, and
    `candidates/uniform-local-observable-sampling.md`.
    `candidates/README.md` additionally needs the separate invalid stable-table
    rationale corrected.
- Canonical `empirical/sieve-sequence/FINDINGS.md` preserves the exact source
  heading and line-5-to-EOF body, changes only provenance lines 3-4 to root
  commands, has no stale references, and passes root tests plus a temporary
  dense schema smoke without changing repository data.
- Canonical `empirical/sieve-sequence/FINDINGS_lineage.md` likewise preserves
  the exact source heading/body and changes only provenance lines 3-4; root
  tests and the temporary exact Q=11 lineage smoke pass without data changes.
- The candidate overview now points to canonical lineage findings, states the
  exact stable-small-`k` lower/CRT-upper theorem and early enumeration, scopes
  guarded diagnostics correctly, and retains the finite-evidence limitation.
- All fifteen audited Markdown files now use canonical CLI/core/test/findings
  paths; the migration changed only exact path literals and left zero
  `candidates/analysis` references in that set.
- Canonical `window.py` documentation now names `window_cli.py` and
  `tests/test_window.py`; stale scan, import, root tests, and both legacy
  compatibility gates pass.
- Canonical `lineage.py` documentation now names `lineage_cli.py` and
  `tests/test_lineage.py`; stale scan, import, root tests, and both compatibility
  gates pass.
- Canonical `tests/test_window.py` now contains an executable repository-root
  instruction through the canonical environment; that exact command, import,
  root tests, and both compatibility gates pass.
- The global deletion audit finds zero external legacy Python references, and
  all inventoried Chapter 7 and `AGENTS.md` documentation blockers are cleared.
  Unrelated `Main` extern methods remain.
- Actual file deletion remains blocked by the repository's critical
  `never-destroy` rule despite the user's requested end state; it requires an
  authoritative rule change or maintainer deletion.
- The canonical window test no longer references the old Scala runner or CSV;
  it accurately documents its internal `[q,q^2)` two-path consistency check,
  and all scoped Python gates pass.
- The learnings Section 6 now marks the old `[p,p^2)` evidence historical,
  incompatible, superseded, and pending retirement, while linking existing
  canonical q-window data and both findings documents.
- The draft-article audit found obsolete Chapter 7 dependencies in its
  title/banner/abstract, method source links, sbt/CSV reproduction, results
  path, conclusion/extern framing, data/file list, and third reference.
- The draft article is now explicitly historical/superseded, removes live old
  commands/paths, separates the different canonical q-window successor, and
  passes canonical path, unit, and temporary schema checks without data writes.
- `AGENTS.md` now correctly states that verified `SpecSieveSequence.next` has no
  extern; source-wide main-code externs are exactly `Main` plus the five
  retirement-pending Chapter 7 empirical helpers.
- The final audit finds no external references to retirement targets. The
  canonical package, README, both findings, both tests, installed console
  executables, and all four root recipes are present; `data/candidates` is
  unchanged. Only the physical legacy Python files, five Chapter 7 helpers, and
  old CSV remain.
- `empirical/sieve-sequence/src/sieve_sequence_empirical/__init__.py` now makes
  the destination package importable with version `0.1.0`. Its exact import
  contract and both legacy Python gates pass. Unnecessary Scala verification
  started under the superseded validation policy was stopped; no such result is
  required for this Python-only slice.
- The scoped changes so far are the two mirrored `v1.MainTest` expected
  literals, `empirical/sieve-sequence/pyproject.toml`,
  `empirical/sieve-sequence/src/sieve_sequence_empirical/__init__.py`, and
  `empirical/sieve-sequence/src/sieve_sequence_empirical/window.py`,
  `empirical/sieve-sequence/src/sieve_sequence_empirical/lineage.py`, plus the
  canonical `empirical/sieve-sequence/src/sieve_sequence_empirical/window_cli.py`,
  canonical `empirical/sieve-sequence/src/sieve_sequence_empirical/lineage_cli.py`,
  plus the
  destination-owned `empirical/sieve-sequence/tests/test_window.py` and
  `empirical/sieve-sequence/tests/test_lineage.py`, plus the
  three corrected stabilization-rationale documentation blocks in
  `candidates/analysis/lib_lineage.py` and the corrected theorem/evidence
  paragraph in `candidates/analysis/FINDINGS_lineage.md`.
- Canonical `window.py` is byte-identical to legacy `lib.py`, with SHA-256
  `e0931094b4d5c1b95ab248ab781d2a5367e478b67df5568a02a4c12bbeca8062`.
  Complete `transition` outputs match at `(p,q)=(3,5),(5,7),(7,11)`, and both
  legacy Python gates remain green.
- Canonical `lineage.py` now has SHA-256
  `a1357644e17128f9ef8f5466ba2487e1771b6cecd5b46a2510c97a00fba6ada0`.
  Its module header correctly distinguishes exact stable small-`k` sigma from
  gated full-period diagnostics. Legacy `lib_lineage.py` now has the identical
  correction and full hash; `cmp` and all four Python gates pass.
- Destination `tests/test_window.py` differs from legacy `test_measure.py` only
  by its canonical package import. Its SHA-256 is
  `d208fcd809937dd2caa3d72124b0e1edd33274cd6ad769ffd3fbe77226daf779`;
  normalized full-content identity, the destination test, and both legacy
  Python gates pass.
- Destination `tests/test_lineage.py` differs from legacy `test_lineage.py`
  only by its canonical package import. Its SHA-256 is
  `4cb7c351ef303dd3c19adfcdbf6f4b6a9752a2563ccad66c95827d7f32a8ae65`;
  normalized full-content identity, the destination test, and both legacy
  Python gates pass.
- Canonical `window_cli.py` preserves dense/sparse positional behavior and the
  exact CSV schema, uses `main(argv=None)` for future console-script entry
  points, and resolves existing `data/candidates` defaults relative to the
  caller rather than the installed source tree. Both destination tests and
  both legacy gates pass. Explicit temporary dense/sparse smokes produced exact
  headers and 2/3 rows respectively, with no repository data change.
- Canonical `lineage_cli.py` preserves the corrected search behavior and exact
  CSV schema, uses canonical imports, `pathlib`, caller-relative existing data
  defaults, and `main(argv=None)`. Both destination tests and both legacy gates
  pass. Its explicit Q=11 temporary smoke has exact headers, three rows with
  `r=[3,5,7]`, and no repository data change.
- Packaging discovery research was paused before any temporary copy or build:
  the proposed legacy virtual environment lacks setuptools. The user then
  prioritized a durable `AGENTS.md` update so future work does not run Scala
  verification for Python-only changes or Python gates for Scala-only changes.
- `AGENTS.md` now applies that language-scoped policy consistently across the
  green-to-green rule, red-cascade, both checklists, Monitor schema, and Action
  Proposal format. A follow-up search found no stale unconditional verification
  wording in those policy locations.
- Packaging research resumed. The legacy venv lacks setuptools; system Python
  has setuptools 58 and wheel 37, below the declared setuptools `>=75` backend,
  so neither environment can provide a trustworthy no-install wheel build.
- The legacy `run_lineage.py` header now makes the correct distinction and all
  four Python gates pass. The legacy README lineage overview is now corrected,
  so the broader wording audit is complete. Core, runner, findings, and README
  consistently distinguish exact stable small-`k` sigma values
  from still-gated full-period diagnostics such as `T_r`, `sigma_r_T`, and the
  cyclic destroyed run.

## Expected State

- A first-class Python project under `empirical/sieve-sequence/`, with package
  metadata, importable modules, CLI entry points, tests, and a focused README.
- Root `just` commands run the empirical tests, window measurement, sparse
  window measurement, and lineage experiment without compiling Stainless code.
- The stability explanation distinguishes finite regression evidence from the
  mathematical monotonicity plus admissible-pattern CRT argument.
- Live documentation references the first-class project. Historical tickets
  retain their original paths as an audit record.
- The redundant Chapter 7 Scala runner, its legacy CSV, and superseded Python
  locations are removed only after the applicable language-scoped replacement
  and repository gates pass.

## Exact Scope and Boundaries

### Protected existing work

All pre-existing modified, staged, and untracked paths shown by `git status`
when this ticket was created are user-owned and out of scope, unless a later
step explicitly identifies a necessary live-documentation overlap and inspects
it before editing. In particular, do not touch
`data/sieve-sequence/first_gaps_per_seq.csv`.

### Later deletion targets explicitly requested by the user

- `src/main/scala/v1/chapter7/empirical/EmpiricalRunner.scala`
- `src/main/scala/v1/chapter7/empirical/CsvWriter.scala`
- `src/main/scala/v1/chapter7/empirical/GapAnalyzer.scala`
- `src/main/scala/v1/chapter7/empirical/SegmentedSieve.scala`
- `src/main/scala/v1/chapter7/empirical/Types.scala`
- `data/empirical/results.csv`
- `candidates/analysis/README.md`
- `candidates/analysis/FINDINGS.md`
- `candidates/analysis/FINDINGS_lineage.md`
- `candidates/analysis/lib.py`
- `candidates/analysis/lib_lineage.py`
- `candidates/analysis/measure_candidates.py`
- `candidates/analysis/requirements.txt`
- `candidates/analysis/run_lineage.py`
- `candidates/analysis/test_lineage.py`
- `candidates/analysis/test_measure.py`

The ten `candidates/analysis/` files may be removed only after the new package,
commands, and live references are verified.

The listed deletion authority is narrow. It does not authorize deletion of the
empirical article, current Python-generated datasets, historical tickets, or
any other path.

## Assumptions and Validation

- **Assumption:** The two `MainTest` failures are expectation drift rather than
  a production regression. **Validation:** capture the actual fallback output,
  update both identical expectations to that output, and require 230/230 tests.
- **Assumption:** The current Python scripts define the behavior to preserve.
  **Validation:** run both legacy tests before migration and equivalent package
  tests after each migration slice; compare schemas and representative outputs.
- **Assumption:** Existing datasets need not move to make the code first-class.
  **Validation:** package CLI defaults resolve the current data paths from the
  repository root and tests cover explicit output paths.
- **Assumption:** Chapter 7 is unused by executable code. **Validation:** repeat
  reference searches immediately before deletion and compile/test afterward.
- **Final validation:** because the completed migration retires both Scala and
  Python paths, its cumulative end-state validation includes 230/230 Scala
  tests, `just verify-ch 1` through `just verify-ch 6`, the new Python test
  command, Python CLI smoke tests, and reference searches showing no live
  dependency on retired paths. Intermediate slices use only the language gates
  defined in Strategy.

## What is Learned

- Chapter 6's `SpecSieveSequence.next` is verified Scala and has no `@extern`.
  The repository context claiming otherwise is stale.
- The sieve-related `@extern` methods are confined to `Main` and the unrelated
  Chapter 7 empirical package; Chapter 8 Spark code is runtime-only but does not
  use `@extern`.
- Chapter 7's CSV runner is not consumed by tests or programs. Its CSV records
  an older `[p, p^2]` prime-counter-style measurement, whereas the Python
  analysis records the required `[q, q^2)` candidate measurements including
  worst-case destruction and actual survivors.
- Finite agreement of stable small-k values is regression evidence, not a proof
  of stability. The proof rationale must use monotonicity for the lower bound
  and the admissible-pattern CRT theorem for the matching upper bound.
- The Codex shell PATH does not include Homebrew, but the installed launcher is
  `/opt/homebrew/bin/just`. Using that exact path completed all six chapter
  checks successfully.
- The Main test failures were expectation drift: removing only the obsolete
  `just show` output line from both mirrored assertions restored 230/230 without
  changing production behavior or any Stainless verification count.
- The two existing Python tests are the migration oracle. Both pass without
  generating data, so destination slices can be compared against a stable
  source-side baseline before any legacy path is retired.
- Minimal metadata can be valid before README, entry points, and package
  discovery exist. Omitting those fields in the first slice avoided dangling
  references while preserving the dependency contract.
- Python and Scala validation are independent unless a change affects both
  ecosystems. This avoids paying the Stainless cost for empirical-only work and
  avoids running Python analysis gates for isolated Scala changes.
- An exact source-to-destination copy plus representative whole-result equality
  is a low-risk way to establish the canonical module before destination-owned
  tests and documentation take over.
- The lineage core is standalone apart from declared NumPy and SymPy
  dependencies, so its corrected legacy source can become canonical without
  retaining any hidden import dependency on `candidates/analysis`.
- When generating an `Add File` patch from command output, preserve the
  source's trailing newline exactly; blindly adding another patch newline can
  create an otherwise invisible extra blank line and break identity checks.
- Removing the terminal empty item from newline-terminated command output
  before prefixing patch lines preserves exactly one final newline in an added
  file; the lineage test used this construction and passed identity first try.
- Caller-relative existing data paths preserve repository-root behavior while
  keeping an installed CLI independent of its package location. Explicit
  output paths remain the reliable choice for automation and smoke tests.
- Both canonical CLIs can now be called as modules and are shaped for future
  zero-argument console-script entry points; packaging metadata must still be
  proven to discover the `src/` package before those scripts are exposed.
- A language-scoped decision recorded only in a ticket is too easy for future
  work to miss when `AGENTS.md` still contains unconditional `just verify`
  checklists. The authoritative rule, checklists, and Monitor schema must agree.
- Explicit `src/` discovery metadata removes package-layout ambiguity without
  relying on an unavailable compatible local build backend.
- Shell/interpreter resolution can vary by working directory. Packaging checks
  should use explicit interpreter paths when different installed environments
  provide `tomllib` and setuptools capabilities.
- Console entries are being exposed one at a time so each installed surface has
  its own callable and schema smoke evidence.
- Both console entries are now exposed and individually validated against their
  exact temporary-output schema, so canonical user documentation can reference
  the installed command names without depending on legacy runner paths.
- Unit suites are only one part of Python green-to-green validation: import and
  CLI gates must also be selected when the changed Python surface affects them.
- A local editable-install workflow needs ignore coverage for both the virtual
  environment and setuptools metadata before it is safe to create either in the
  repository.
- Explicit ignore validation contains the canonical environment and editable
  metadata without hiding any tracked repository file.
- The independent canonical environment removes the last runtime dependency on
  the legacy analysis directory and can now back reproducible root recipes.
- A strict root test recipe makes the destination-owned Python unit gates
  discoverable without coupling them to Scala or legacy paths.
- The installed dense console surface is now reproducible from the root with
  explicit parameters and a documented default dataset path.
- The sparse console surface now has the same first-class root workflow and
  retains an explicit output override for safe validation.
- Deriving the default lineage filename from the selected Q prevents parameter
  overrides from silently overwriting a misleading Q17 dataset.
- Historical numerical parameters and datasets remain meaningful provenance,
  but their live implementation references must move to canonical commands and
  paths before the legacy directory is retired.
- The 258-line window findings and 151-line lineage findings must be preserved
  canonically; `candidates/README.md` also separately repeats the invalid claim
  that the proved stable table is an unproved extrapolation.
- Both detailed findings documents are now preserved canonically, so live
  references can move without losing numerical or interpretive provenance.
- The user-facing candidate overview is now semantically aligned with the
  canonical lineage implementation and findings.
- Live Markdown provenance now resolves to first-class canonical files without
  altering any measured values or surrounding user edits.
- Searching only for the original invalid “monotone stabilization” phrase was
  too narrow. A semantic wording audit is required because the same false
  frontier conclusion can appear under different language.
- Exact source/canonical byte identity may be intentionally broken for one
  reviewed documentation correction, but the mirror must be the next isolated
  change so compatibility evidence remains easy to audit.
- Mirroring the reviewed canonical header immediately restored full identity at
  `a1357644...6ada0` without changing behavior; all four Python gates stayed
  green.
- Runner-level documentation must describe the actual fallback split, not the
  diagnostic materialization guard as if it disables the small-`k` search.
- The `5e7` guard is an implementation/materialization limit on current
  full-period diagnostic fields, not a mathematical limit on the exact stable
  small-`k` values used by the #14 search.
- The honest one-Q limitation is independent of the frontier: a tiny sample
  proves nothing general even when the relevant exact measurements can scale.
- Scaling experiments can continue exact #14/#12/#13 measurements while
  treating guarded full-period diagnostics as optional fields rather than a
  prerequisite for the run.
- The reassessment can preserve its valid warning that monotonicity alone is
  insufficient while also recording that the admissible-pattern CRT theorem
  now supplies the missing upper bound.
- Rationale cleanup is complete only when every layer—core documentation,
  runner documentation, findings, and user-facing README—states the same
  exact-small-`k` versus guarded-diagnostics boundary.
- Stable small-k exactness needs both inequalities: filtering monotonicity and
  the exact sub-wheel give the lower bound, while an admissible pattern
  translated by CRT supplies the matching upper bound. Later finite-wheel
  agreement is implementation evidence only.
- `candidates/analysis/FINDINGS_lineage.md` had contradicted that theorem and
  the corrected implementation documentation by calling the exact table a
  heuristic extrapolation. It is now corrected before canonical lineage code
  or documentation is copied.

## Failed Paths

- **Keep the Python implementation hidden under `candidates/analysis`.** This
  failed the maintainability goal: it has directory-local imports, no package
  metadata, and no root workflow. Retry only if the repository intentionally
  abandons first-class Python tooling.
- **Use or extend the Chapter 7 Scala runner.** This failed because it is a
  separate prime counter, does not generate the required sieve-sequence
  candidate data, and still participates in the heavyweight Scala build. Retry
  only if a future requirement specifically needs that legacy measurement.
- **Delete the empirical article with Chapter 7.** This was rejected because
  the Python scripts generate the data needed by the empirical analysis. Retry
  only if the article itself is superseded after its claims are migrated.
- **Move datasets during the package migration.** This was pre-empted because
  simultaneous code and data-path changes obscure compatibility failures.
  Retry as a separate phase after package tests establish schema equivalence.
- **Repair only one duplicated `MainTest` assertion.** This would deliberately
  leave the baseline red and trigger `red-cascade`. Retry only if the duplicate
  test cases cease to share the same expected behavior.
- **Propose the atomic `MainTest` repair before a fresh verification baseline.**
  The Monitor rejected this because the available logs predate HEAD and omit
  chapters 1, 3, and 4. Retry the exact two-literal proposal only after all six
  chapter checks report zero invalid and zero unknown.
- **Run Scala verification after Python-only slices.** This was started for the
  package bootstrap because the earlier rule coupled every non-Markdown change
  to Stainless. The user clarified that cross-language validation is not
  required, so the running verifier was stopped. Retry only for a mixed or
  Scala-affecting change.
- **Claim that folding a prime inserts only large gaps and therefore proves
  stabilization.** This is invalid: filtering removes survivors and merges
  adjacent gaps, so it gives no upper bound or equality proof. Retry only with
  the monotone lower bound plus the admissible-pattern CRT upper bound.
- **First destination window-test addition.** Patch construction added one
  extra blank line at EOF, producing SHA-256 `c6d05c...e921c7`; normalized
  identity failed and testing stopped. The permitted same-target retry removed
  exactly that blank and restored the expected hash. Retry generation only with
  the source newline boundary inspected explicitly.
- **Combined packaging validation under unqualified `python3`.** From the
  empirical project directory it resolved Homebrew Python 3.14, which has
  `tomllib` but no setuptools, so the command failed before discovery. The
  same-target retry split TOML parsing and setuptools discovery across explicit
  compatible interpreters. Retry only with interpreter capabilities resolved
  first.
- **Call the two destination unit suites all Python green-to-green gates.** The
  README's first wording was too broad and could cause import or CLI changes to
  skip their affected gates. The allowed same-target correction identifies the
  suites as unit gates and requires applicable import/CLI checks.
- **Create the canonical environment before checking ignore coverage.** Monitor
  blocked the proposal because `.venv` and editable `*.egg-info` artifacts were
  not ignored, which could leave a large untracked tree that cannot be cleaned
  under the repository's no-`rm` rule. Add precise ignore coverage first.
- **Install the canonical project inside the restricted network sandbox.** The
  first editable install failed only because pip could not resolve the declared
  build dependency. The approved same-target escalated retry installed all
  dependencies and entries successfully; no legacy fallback was used.
- **Improvise a shorter canonical findings heading.** The first copy changed
  line 1 despite the approved exact-heading plan. The same-target correction
  restored source heading equality while preserving the approved header/body.
- **Use lookbehind in a default `rg` stale-name scan.** The command exited 2
  because lookaround requires PCRE2; the portable same-target character-class
  retry passed and project validation remained green.
- **Wrap new inline math in code spans.** Seven convention expressions in the
  article deprecation pass rendered their dollar delimiters literally. The
  same-target formatting correction removed only the surrounding backticks.

## Open Concerns

- The completed atomic repair of two identical test expectations was a narrow
  exception to the one-assertion-per-change rule because changing either one
  alone would have preserved a known red state. It does not relax the rule for
  later changes.
- Production `Main` still names `v1.DivMain` in its fallback message. Improving
  that help contract remains a separate future green-to-green change with its
  own test design.
- `Justfile` and package metadata changes are non-Markdown and therefore require
  validation for the languages and workflows they actually affect. A future
  `Justfile` change adding Python commands is mixed orchestration and must at
  least exercise those commands; it does not automatically require Stainless.
- Some live documentation files already contain unrelated user edits. Any
  necessary overlap must be inspected and patched narrowly; otherwise leave it
  for a separately coordinated documentation pass.
- The rationale cleanup is complete and the canonical lineage-CLI prerequisite
  is cleared. Legacy documentation remains until canonical CLI, README,
  commands, and live references are verified.

## Next Action

Blocked pending an authoritative change to the critical `never-destroy` rule,
or maintainer-performed deletion of the exact physical retirement targets.
Do not delete the legacy Python files, five Chapter 7 empirical helpers, or old
CSV while the current repository rule remains in force.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-04 | The Python analysis is the required empirical implementation; the Chapter 7 runner is an unrelated prime counter. | Scoped a compatibility-first first-class Python migration and the exact later deletions. |
| 2026-08-04 | The current baseline is blocked by two identical stale test expectations, while repairing only one would leave red. | Recorded the narrowly approved atomic duplicate repair as the first prerequisite. |
| 2026-08-04 | The worktree contains unrelated staged and untracked work. | Declared all pre-existing changes protected and singled out the staged large CSV. |
| 2026-08-04 | The existing verification logs predate HEAD and do not cover all six chapters. | Deferred the test repair and made a fresh chapter 1–6 baseline the immediate next action. |
| 2026-08-04 | Fresh chapters 1–6 passed with 16, 1,374, 1,602, 2,995, 2,145, and 4,390 valid checks respectively; every chapter had zero invalid and zero unknown. | Restored the atomic MainTest repair as the next action and retained full post-change regression gates. |
| 2026-08-04 | The atomic removal of the obsolete `just show` expectation restored 230/230 tests; all six post-change chapter counts remained green. | Closed the red baseline prerequisite and made the two legacy Python gates the migration compatibility baseline. |
| 2026-08-04 | Both legacy Python tests exit 0 with explicit `RESULT: PASS` and do not need to generate CSV data. | Fixed them as the compatibility oracle and selected only the destination `pyproject.toml` as the first migration slice. |
| 2026-08-04 | The new `pyproject.toml` parses exactly and preserves both Python gates, 230/230 Scala tests, and all six verification counts. | Completed the metadata slice and selected only the package `__init__.py` bootstrap for the next review. |
| 2026-08-04 | The package bootstrap imports with version `0.1.0`, and both Python gates remain green. The user clarified that Python and Scala changes do not require cross-language validation. | Stopped the unnecessary Scala verifier, recorded language-scoped gates, and selected one Python core module as the next slice. |
| 2026-08-04 | Canonical `window.py` is byte-identical to legacy `lib.py` at SHA-256 `e0931094...a8062`; three complete transition comparisons and both Python gates pass. | Completed the window-core slice and blocked lineage copying until its invalid stability rationale is corrected. |
| 2026-08-04 | The first lineage explanation falsely used filtering alone as a stabilization proof; correct exactness needs a monotone lower bound and an admissible-pattern CRT upper bound. Both Python gates pass after correction. | Replaced that rationale and selected only the separate `_SIGMA_STABLE` comment block as the next micro-goal. |
| 2026-08-04 | The `_SIGMA_STABLE` comment repeated the same invalid monotonicity-only claim. Both Python gates exit 0 with explicit `RESULT: PASS` after replacing it with the exact lower-bound/CRT-upper-bound rationale. | Completed the second rationale block and selected only the adjacent `sigma_r_stable` docstring as the next micro-goal. |
| 2026-08-04 | The `sigma_r_stable` docstring now states theorem-based exactness and both Python gates pass, but `FINDINGS_lineage.md` still calls the same table heuristic. | Completed all three implementation documentation corrections and selected only the contradictory findings paragraph before canonical copying. |
| 2026-08-04 | The lineage findings now state theorem-based exactness for `2 <= k <= 10` and retain finite measurements as regression evidence only. | Completed the rationale cleanup and selected an exact corrected-source copy into canonical `lineage.py` as the next runtime slice. |
| 2026-08-04 | Canonical `lineage.py` is byte-identical at SHA-256 `dff9011b...60a3a`; destination import, every representative equality case, and both Python gates pass. | Completed the lineage-core slice and selected one destination-owned window test as the next step toward independent Python validation. |
| 2026-08-04 | Destination `test_window.py` has import-only normalized identity and all Python gates pass; its first generated patch had one extra EOF blank, caught before testing and corrected on the same target. | Recorded the newline-generation failure and selected one destination-owned lineage test as the next independent gate. |
| 2026-08-04 | Destination `test_lineage.py` has import-only normalized identity at SHA-256 `4cb7c3...8ae65`; destination and legacy Python gates pass without a retry. | Completed destination-owned core validation and selected canonical window-CLI output-policy research. |
| 2026-08-04 | Canonical `window_cli.py` preserves schema and dense/sparse behavior while removing install-location assumptions; destination tests, explicit temporary CSV checks, and legacy gates pass without repository data writes. | Completed the window CLI slice and selected canonical lineage-CLI research with documentation cleanup. |
| 2026-08-04 | A semantic wording audit found additional false full-period-frontier claims beyond the three initially searched blocks. | Retracted the premature cleanup claim, inventoried all stale locations, deferred the lineage CLI, and selected only the canonical lineage module header first. |
| 2026-08-04 | Canonical lineage header now distinguishes exact stable small-`k` sigma from gated full-period diagnostics at SHA-256 `a13576...6ada0`; all four Python gates pass. | Recorded the intentional documentation-only identity break and selected the mirrored legacy header correction next. |
| 2026-08-04 | Legacy and canonical lineage cores again match at SHA-256 `a13576...6ada0`; `cmp` and all four Python gates pass. | Closed the mirrored-header step and selected only the stale legacy runner header next. |
| 2026-08-04 | Legacy runner header now states exact stable small-`k` search beyond the frontier and gated full-period diagnostics; all four Python gates pass. | Removed the runner from the stale inventory and selected only the findings hard-limit bullet next. |
| 2026-08-04 | The findings hard-limit bullet now scopes `5e7` to current full-period diagnostics and preserves exact stable small-`k` #14 search beyond it. | Removed that bullet from the stale inventory and selected only the adjacent tiny-Q wording next. |
| 2026-08-04 | The findings tiny-Q bullet preserves the one-sample limitation while allowing exact #14/#12/#13 scaling beyond the diagnostic frontier. | Removed that bullet from the stale inventory and selected only the “Next Step” paragraph. |
| 2026-08-04 | The findings “Next Step” now scales exact #14/#12/#13 measurements beyond the pilot and treats guarded diagnostics as optional. | Removed the scaling paragraph from the stale inventory and selected only the reassessment heading/introduction. |
| 2026-08-04 | The reassessment now records the admissible-pattern CRT upper bound and exact theorem scope while preserving the valid monotonicity cautions. | Completed the findings rationale cleanup and selected only the legacy README lineage overview. |
| 2026-08-04 | The legacy README now states exact stable small-`k`, guarded full-period diagnostics, and exact-or-unmeasured out-of-profile behavior. | Closed the rationale audit across core, runner, findings, and README, then restored canonical lineage-CLI work as the next slice. |
| 2026-08-04 | Canonical `lineage_cli.py` passes destination tests, exact Q=11 temporary CSV checks, and legacy gates without repository data writes. | Completed both canonical CLIs and selected read-only packaging discovery validation before exposing console scripts. |
| 2026-08-04 | The legacy venv lacks setuptools, so the temporary wheel plan was stopped before copying/building. The user requested a durable language-scoped validation rule. | Paused packaging research and selected a coherent `AGENTS.md` rule/checklist/Monitor-schema correction before resuming it. |
| 2026-08-04 | `AGENTS.md` now authoritatively scopes Python, Scala/Stainless, mixed, and Markdown validation. Compatible local wheel tooling is unavailable without installation. | Resumed packaging with explicit `src/` discovery metadata as the next Python-only slice. |
| 2026-08-04 | Explicit `src/` discovery parses and resolves exactly `sieve_sequence_empirical`; all four Python gates pass. An initial combined check failed because workdir `python3` lacked setuptools, then the split-interpreter retry passed. | Completed discovery metadata and selected only the window console entry next. |
| 2026-08-04 | The one-entry scripts table exposes a callable `sieve-sequence-window`; its max=7 temporary CSV has exact headers and two rows, all four Python gates pass, and repository data is unchanged. | Completed the window entry and selected only the lineage console entry next. |
| 2026-08-04 | The exact two-entry scripts table now exposes a callable lineage command; its Q=11 temporary CSV has exact headers, three rows, and `r=[3,5,7]`. All four Python gates pass and repository data is unchanged. | Completed console-script metadata and selected exactly one canonical Python README as the next migration slice. |
| 2026-08-04 | The canonical README now exposes reproducible explicit-path workflows and accurately separates unit, import, and CLI gates; fresh focused checks pass without touching repository data. | Completed first-class Python documentation and selected exactly one root empirical-test recipe next. |
| 2026-08-04 | The canonical environment cannot be created safely until its `.venv` and editable-install metadata are ignored. | Blocked environment setup before side effects and selected one root ignore-policy change. |
| 2026-08-04 | Root ignore rules now contain both canonical `.venv` and editable `*.egg-info` artifacts without matching tracked files. | Cleared the side-effect prerequisite and restored canonical environment creation as the next action. |
| 2026-08-04 | The independent canonical environment installs project 0.1.0 and exact console entries; an approved network retry recovered the sandbox-only build-dependency failure without a legacy fallback. | Cleared the runtime prerequisite and restored the single empirical-test root recipe next. |
| 2026-08-04 | Root `empirical-test` is discoverable and produces exactly two passing canonical unit-suite markers without writing data. | Completed the root Python unit workflow and selected one dense empirical-window recipe next. |
| 2026-08-04 | Root `empirical-window` is discoverable and its temporary max=7 run has the exact 18-column/two-row output without touching repository data. | Completed the dense root workflow and selected one sparse-window recipe next. |
| 2026-08-04 | Root `empirical-window-sparse` is discoverable and its temporary stride=2/max=11 run has the exact 18-column/three-row output without touching repository data. | Completed the sparse root workflow and selected one Q-safe lineage recipe next. |
| 2026-08-04 | Root `empirical-lineage` safely derives Q-specific defaults and its explicit Q=11 temporary run has the exact 22-column/three-row layer output. | Completed all root Python workflows and selected a live-reference audit before legacy retirement. |
| 2026-08-04 | Eighteen live files still name legacy implementation paths, and both detailed findings documents must move canonically; one candidate overview also repeats the invalid stable-table rationale. | Classified canonical updates versus retained numerical provenance and selected the window findings copy first. |
| 2026-08-04 | Canonical window findings preserve the exact source heading/body and differ only in the approved root reproduction/gate header; an initial heading drift was caught and corrected. | Preserved the detailed window analysis and selected the lineage findings copy next. |
| 2026-08-04 | Canonical lineage findings also preserve their exact heading/body and pass root tests plus an exact temporary Q=11 smoke. | Preserved both findings documents and prioritized the invalid stable-table rationale in the candidate overview. |
| 2026-08-04 | The candidate overview now states the exact stable-small-k theorem, guarded diagnostics, canonical findings path, and finite-evidence limit. | Removed the critical invalid rationale and selected the bounded Markdown path migration next. |
| 2026-08-04 | All fifteen audited Markdown files now point to canonical implementation/findings paths with measured prose and prior user edits preserved. | Completed the live Markdown migration and selected canonical window docstring naming next. |
| 2026-08-04 | Canonical window documentation now names its canonical CLI and test; import plus canonical and compatibility suites remain green. | Removed window-core legacy naming and selected the lineage-core header next. |
| 2026-08-04 | Canonical lineage documentation now names its canonical CLI/test and all scoped Python gates pass; a portable scan replaced an unsupported lookbehind command. | Removed lineage-core legacy naming and selected the final canonical test-header instruction next. |
| 2026-08-04 | The final canonical window-test instruction executes from repository root and all canonical plus compatibility gates remain green. | Removed the last inventoried canonical naming error and selected a global deletion-blocker audit. |
| 2026-08-04 | Legacy Python has no live external references; Chapter 7 still has three documentation consumers plus one stale AGENTS claim, while the absolute never-destroy rule blocks requested deletion. | Recorded exact blockers and selected the canonical test comment cleanup first. |
| 2026-08-04 | The canonical window test now documents only its actual internal q-window consistency check and all scoped Python gates pass. | Removed one Chapter 7 reference blocker and selected the stale learnings CSV claim next. |
| 2026-08-04 | Learnings Section 6 now labels the old p-window data superseded and pending retirement while pointing to canonical q-window evidence. | Removed the stale learnings claim and selected a framing audit of the obsolete draft article. |
| 2026-08-04 | The draft article presents the old p-window experiment as current across its framing, reproduction, data, and references; canonical q-window evidence cannot reproduce those tables. | Selected one article-wide deprecation pass that strictly separates historical numbers from the current successor experiment. |
| 2026-08-04 | The old article is now explicitly historical, non-runnable, and separate from the canonical q-window successor; one inline-math rendering error was caught and corrected. | Removed the broad draft-article blocker and selected the stale AGENTS extern claim next. |
| 2026-08-04 | AGENTS now accurately states that verified SpecSieveSequence.next has no extern and isolates the five retirement-pending Chapter 7 helpers from Main. | Cleared the final documentation reference blocker and selected the final read-only retirement audit. |
| 2026-08-04 | The final audit is clean outside the physical targets: canonical artifacts and all four root recipes exist, and repository candidate data is unchanged. | Stopped at the authoritative never-destroy rule and requested a rule change or maintainer deletion for physical retirement. |
