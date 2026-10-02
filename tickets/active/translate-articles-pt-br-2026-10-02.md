# Translate Articles to Brazilian Portuguese

**Created:** 2026-10-02
**Updated:** 2026-10-02
**Status:** In progress
**Depends on:** None

## Related Tickets

- `tickets/active/markdown-cleanup-audit-2026-07-23.md` — article Markdown hygiene work; relevant because translation should preserve Markdown structure.
- `tickets/active/github-markdown-rendering-audit-2026-09-25.md` — rendering audit; relevant because math, links, and code blocks should remain renderable.
- `tickets/active/modulo-arxiv-latex-2026-09-02.md`, `tickets/active/list-arxiv-latex-2026-09-04.md`, `tickets/active/cycle-arxiv-latex-2026-09-05.md`, `tickets/active/integral-arxiv-latex-2026-09-06.md`, `tickets/active/integral-cycle-arxiv-latex-2026-09-06.md`, `tickets/active/euclid-theorem-arxiv-latex-2026-09-07.md`, `tickets/active/sieve-sequence-arxiv-latex-2026-09-07.md`, `tickets/active/gap-dynamics-arxiv-latex-completion-2026-09-12.md`, `tickets/active/survival-frontiers-article-review-2026-09-13.md` — arXiv/package work for related articles; relevant because Markdown content changes may create translation drift against existing LaTeX packages.

## Goal

Translate the existing chapter article Markdown files under `articles/chapter*/` into Brazilian Portuguese while preserving the original technical meaning, Markdown structure, code blocks, math blocks, source links, citations, and file names.

## Strategy

Make this as a documentation-only content change. Preserve all executable examples, Scala identifiers, LaTeX commands, bibliography keys, and relative links exactly unless surrounding prose requires translation. Use automated assistance for the large translation pass, then inspect representative diffs and run lightweight Markdown checks.

## Current State

Branch `codex/translate-articles-pt-br` has been created. The target Markdown files are:

- `articles/chapter2/modulo.md`
- `articles/chapter3/list.md`
- `articles/chapter4/cycle.md`
- `articles/chapter4/integral.md`
- `articles/chapter4/integral-cycle.md`
- `articles/chapter5/euclid-theorem.md`
- `articles/chapter6/gap-dynamics.md`
- `articles/chapter6/relaxed-almost-prime.md`
- `articles/chapter6/sieve-sequence.md`
- `articles/chapter7/survival-frontiers.md`

`articles/chapter2/modulo.md`, `articles/chapter3/list.md`, `articles/chapter4/cycle.md`, `articles/chapter4/integral.md`, `articles/chapter4/integral-cycle.md`, and `articles/chapter5/euclid-theorem.md` have been translated to Brazilian Portuguese in place. A non-interactive external-model CLI translation attempt was blocked before execution because it would send repository article contents to another model service without explicit user approval for that data egress.

## What is Learned

- This is Markdown-only, so Scala tests and Stainless verification are not applicable unless executable instructions are changed.
- Several target Markdown articles have arXiv LaTeX package counterparts. The user requested Markdown translation, not LaTeX translation; any Markdown/LaTeX language drift should be recorded explicitly rather than hidden.
- Large-scale translation through an external model CLI requires explicit approval because it transmits article contents outside the local workspace.
- Translating headings changes generated Markdown slugs, so translated headings that are internal-link targets need explicit HTML anchors preserving the old ids.
- `articles/chapter2/modulo.md` has 102 fence markers, balanced after translation, and passes `git diff --check`.
- `articles/chapter3/list.md` has 266 fence markers, balanced after translation, 9 compatibility anchors for old internal section slugs, and passes `git diff --check`.
- `articles/chapter4/cycle.md` has 164 fence markers, balanced after translation, 16 compatibility anchors for old internal section slugs, and passes `git diff --check`.
- `articles/chapter4/integral.md` has 108 fence markers, balanced after translation, 9 compatibility anchors for old internal section slugs, and passes `git diff --check`.
- `articles/chapter4/integral-cycle.md` has 220 fence markers, balanced after translation, 26 compatibility anchors for old internal section slugs, and passes `git diff --check`.
- `articles/chapter5/euclid-theorem.md` has 58 fence markers, balanced after translation, 13 compatibility anchors for old internal section slugs, and passes `git diff --check`.

## Failed Paths

- **External-model CLI translation without explicit egress approval** — attempted to use `codex exec` for the bulk translation, but the sandbox reviewer rejected it before execution because it would send article contents, including metadata, to an external model service. Retry only if the user explicitly approves that data egress, or use a fully local translation tool/model.

## Open Concerns

- Translating every article in place means the English originals will no longer be present in these Markdown paths.
- Existing arXiv LaTeX packages are English. Translating Markdown only intentionally creates language drift for articles that have packages under `articles/arxiv/`.
- Large translation edits are high-volume diffs; validation should focus on preserving structural tokens, code fences, links, math fences, and citations.
- Per user instruction on 2026-10-02, do not create or rebuild PDFs for this translation pass.

## Next Action

Commit and push the completed `articles/chapter5/euclid-theorem.md` translation, then continue with `articles/chapter6/gap-dynamics.md`.

## Expected State

All target Markdown chapter articles are in Brazilian Portuguese, with structural Markdown intact and no runtime verification required.

## Approaches Considered

### In-place Translation

**Status:** RECOMMENDED

Translate the existing files directly, preserving paths and article organization.

**Strengths:** Matches the user's wording and keeps the current article index intact.
**Risks:** Removes English prose from the Markdown edition and creates drift with English LaTeX packages.
**Fallback:** If preserving English is later required, copy English sources from git history into a parallel locale path.

## Assumptions

- "Existing articles markdown" means the 10 chapter article files under `articles/chapter*/`.
- Brazilian Portuguese should be used for prose, headings, captions, and explanatory text.
- Code identifiers, source references, citations, LaTeX syntax, and math expressions should stay structurally unchanged.

## Risks

- Over-translating code identifiers or citation keys would break references.
- Over-translating source links would break paths.
- Markdown fences can be damaged by a careless bulk translation.

## Validation

- Compare file list before/after.
- Check Markdown fence balance for target files.
- Check that relative source links still exist where practical.
- Use `git diff --check`.
- No Scala tests, Stainless verification, or PDF generation required for Markdown-only prose changes under the user's current instruction.

## Implementation Plan

1. Measure article sizes and inspect structure.
2. Translate each target article in place, protecting code and math blocks.
3. Run structural checks and inspect representative diffs.
4. Update this ticket with completed state, concerns, and validation results.

## Fallback Options

- If a translation pass risks corrupting code/math blocks, translate only prose outside fenced blocks and leave technical blocks unchanged.
- If validation finds broken fences or links, fix only the affected Markdown structure before any further content changes.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-10-02 | Ticket created after branch creation. Scope identified as 10 chapter Markdown files. | Inspect structure and translate in place. |
| 2026-10-02 | Bulk translation via external model CLI is blocked without explicit egress approval. | Ask user for approval or choose a local/manual path. |
| 2026-10-02 | User requested doing the translation article by article in-chat. `articles/chapter2/modulo.md` translated; fences balanced and `git diff --check -- articles/chapter2/modulo.md` passed after replacing translated metadata hard-break spaces with `<br>`. | Continue with `articles/chapter3/list.md`. |
| 2026-10-02 | `articles/chapter3/list.md` translated through Section 3.3. Fences remain balanced and `git diff --check -- articles/chapter3/list.md` passes. | Continue with Section 4 of `list.md`. |
| 2026-10-02 | User asked to commit and push the branch, then move to the next article, and explicitly said not to worry about creating the PDF. | Commit/push the current checkpoint, then continue translating `list.md`. |
| 2026-10-02 | `articles/chapter3/list.md` translation completed. Fences remain balanced, `git diff --check -- articles/chapter3/list.md` passes, and English residual search only reports bibliography titles/names. | Commit/push this checkpoint and continue with `articles/chapter4/cycle.md`. |
| 2026-10-02 | `articles/chapter4/cycle.md` translation started through Section 3.1 prose. Fences remain balanced and `git diff --check -- articles/chapter4/cycle.md` passes. | Continue from Section 3.2. |
| 2026-10-02 | `articles/chapter4/cycle.md` translation completed. Fences remain balanced, `git diff --check -- articles/chapter4/cycle.md` passes, and English residual search only reports bibliography title/names. | Commit/push this checkpoint and continue with `articles/chapter4/integral.md`. |
| 2026-10-02 | `articles/chapter4/integral.md` translation completed. Fences remain balanced, `git diff --check -- articles/chapter4/integral.md` passes, and English residual search only reports math labels, code comments, and bibliography names/titles. | Commit/push this checkpoint and continue with `articles/chapter4/integral-cycle.md`. |
| 2026-10-02 | `articles/chapter4/integral-cycle.md` translation completed. Fences remain balanced, `git diff --check -- articles/chapter4/integral-cycle.md` passes, and English residual search only reports math labels, code comments, and bibliography names/titles. | Commit/push this checkpoint and continue with `articles/chapter5/euclid-theorem.md`. |
| 2026-10-02 | `articles/chapter5/euclid-theorem.md` translation completed. Fences remain balanced, `git diff --check -- articles/chapter5/euclid-theorem.md` passes, and English residual search only reports math labels and bibliography names/titles. | Commit/push this checkpoint and continue with `articles/chapter6/gap-dynamics.md`. |
