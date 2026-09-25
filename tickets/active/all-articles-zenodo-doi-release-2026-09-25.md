# All-Article Zenodo DOI Release

**Created:** 2026-09-25
**Updated:** 2026-09-25
**Status:** In progress

## START HERE

Embed the five newly reserved Zenodo DOIs in their synchronized Markdown and
LaTeX editions, rebuild the PDFs, and validate the exact release artifacts.

## Goal

Make each remaining article identify its own unpublished Zenodo record in the
Markdown, LaTeX, and generated PDF while keeping every Zenodo draft unpublished.

## Strategy

Apply one front-matter-only DOI change per article, validate Markdown/LaTeX/PDF
parity after each change, and generate source packages before recording final
PDF hashes so no later build changes the release bytes.

## Current State

- Branch `article-dois-all-remaining` starts from `origin/master` at `2352f5f2`.
- Five empty, unpublished Zenodo drafts reserve these DOIs:
  - `list`: `10.5281/zenodo.22955771`
  - `sieve-sequence`: `10.5281/zenodo.22955782`
  - `gap-dynamics`: `10.5281/zenodo.22955786`
  - `relaxed-almost-prime`: `10.5281/zenodo.22955792`
  - `survival-frontiers`: `10.5281/zenodo.22955798`
- The draft titles are saved; no files have been uploaded or published.
- All five unchanged packages have green PDF-build and parity baselines.
- `list` now contains `10.5281/zenodo.22955771` in Markdown, LaTeX, and its
  rebuilt PDF; parity remains PASS with the same two baseline warnings.
- `sieve-sequence` now contains `10.5281/zenodo.22955782` in Markdown, LaTeX,
  and its rebuilt PDF; parity is a clean PASS.
- `gap-dynamics` now contains `10.5281/zenodo.22955786` in Markdown, LaTeX,
  and its rebuilt PDF; parity remains PASS with its baseline warning.
- `relaxed-almost-prime` now contains `10.5281/zenodo.22955792` in Markdown,
  LaTeX, and its rebuilt PDF; parity is a clean PASS.
- `survival-frontiers` now contains `10.5281/zenodo.22955798` in Markdown,
  LaTeX, and its rebuilt PDF; parity is a clean PASS.
- All five synchronized source edits and source archives are complete and
  green. Page 1 of every PDF is visually clean and its text layer contains
  the assigned DOI.
- Final PDF SHA-256 values:
  - `list`: `37ef83855a41d54d3aceacd5d3af32ec3ea91252af5144dca1d012fe0dd7521d`
  - `sieve-sequence`: `524ab74fc5c98d6be6fbfc5d8654413148c9b2a864f986bfcec701bae775783a`
  - `gap-dynamics`: `abc6f911716b9a3e78132b8b7354130fee455f965dd04eca01e40f8915f852b3`
  - `relaxed-almost-prime`: `02f4428002ccf47942218b60492f0cc1108f7db88662e5f8c44c73f6f7bdc6f7`
  - `survival-frontiers`: `8e88f1866d5a559b82e0c75799afd6f3171a48e8dfad75ff23919f7e5ffd26ef`
- Final source-archive SHA-256 values:
  - `list`: `0700bf663d3d8262361117242d247700f7bb56a1b29236d9705f8f661fbb77a5`
  - `sieve-sequence`: `5ca489defbe1a1f24221b6f8afc8d038f8ad7ea318466faed6e9f8a5f1c5e4c0`
  - `gap-dynamics`: `4b654ab44c0e26addec6d5a4dbf7b81ca7d51cf4217042f225d1a74512f08bb6`
  - `relaxed-almost-prime`: `2ac13dbe4a9f315ddec31e0137fb4b3af58c8b1b5eab52eacbb79e3740de2602`
  - `survival-frontiers`: `8be3701ccd869b2cfa141c2c315caaff5b45961e11960e198795f1c765ad23b2`

## What is Learned

- One Zenodo draft per article is required to preserve one DOI per article.
- Reserving each DOI before building lets the PDF contain the same DOI as its
  eventual Zenodo record.
- `list` already has an rxiVerse publication identifier that must be preserved.

## Failed Paths

- A single multi-file Zenodo draft was rejected because it would provide one
  collection DOI rather than one DOI per article. Reconsider only as an
  additional collection record, never as the article identity scheme.
- System `python3` could not run the PDF text-layer check because it does not
  include `pypdf`. The same check passes with Codex's bundled PDF runtime;
  retry system Python only if that environment gains the dependency.
- Markdown hard breaks written as trailing spaces failed `git diff --check`.
  Replacing only the five new breaks with explicit `<br>` tags fixed the
  check; use that form for future DOI front-matter additions.

## Open Concerns

- Final PDFs must not be rebuilt after their hashes are recorded and files are
  uploaded, because PDF metadata may make rebuilt bytes differ.
- Publishing and file upload are outside this change and require separate user
  review; all drafts must remain unpublished during this work.

## Next Action

Review the final diff and commit the synchronized DOI sources and generated
PDFs on `article-dois-all-remaining`. Keep Zenodo drafts unpublished.

## Validation

1. Build each article package successfully with a clean LaTeX log.
2. Require `just arxiv-parity <article>` to pass for every article.
3. Build each source archive, then rerun parity without another PDF rebuild.
4. Extract each PDF text layer and confirm its own DOI is present.
5. Render and visually inspect page 1 of all five PDFs.
6. Record SHA-256 hashes for the final PDFs and source archives.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-09-25 | Five independent drafts reserve DOI values and have saved titles but no uploaded files. | Create a clean branch and establish build/parity baselines. |
| 2026-09-25 | All five unchanged article packages build successfully and pass parity; `list` and `gap-dynamics` retain only their existing non-failing warnings. | Begin the per-article synchronized DOI edits with `list`. |
| 2026-09-25 | `list` builds with its reserved DOI and parity remains PASS with its two unchanged warnings. | Continue with `sieve-sequence`. |
| 2026-09-25 | `sieve-sequence` builds with its reserved DOI and parity passes cleanly. | Continue with `gap-dynamics`. |
| 2026-09-25 | `gap-dynamics` builds with its reserved DOI and parity remains PASS with its unchanged warning. | Continue with `relaxed-almost-prime`. |
| 2026-09-25 | `relaxed-almost-prime` builds with its reserved DOI and parity passes cleanly. | Continue with `survival-frontiers`. |
| 2026-09-25 | `survival-frontiers` builds with its reserved DOI and parity passes cleanly; all five synchronized DOI edits are green. | Generate source archives and perform final PDF verification. |
| 2026-09-25 | Final source generation and parity pass for all five articles; page-one renders are clean and PDF text extraction finds each DOI. System Python lacked `pypdf`, while the bundled runtime passed the same check. | Freeze the recorded artifacts, review the diff, and commit. |
| 2026-09-25 | Final diff review found trailing-space Markdown breaks. Explicit `<br>` tags fixed `git diff --check`; regenerated PDFs and archives pass parity and visual/text inspection with the final hashes recorded above. | Commit the complete synchronized artifact set. |
