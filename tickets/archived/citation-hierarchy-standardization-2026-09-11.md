# Citation Hierarchy Standardization Across Article PRs

**Status: COMPLETE** — all PRs merged to master on 2026-09-12.

## Goal

Apply the citation precedence hierarchy to every cross-article citation
(MD references + LaTeX bib entries), then rebuild affected PDFs:

1. Magazine (peer-reviewed) — none currently
2. Archive (viXra/rxiVerse/arXiv) — modulo: ai.viXra:2609.0009,
   list: rxiVerse:2609.0023
3. Release (GitHub release tag) — cycle: cycle-article-v1.0.0
4. Internal (master link) — unreleased articles (integral, integral-cycle,
   euclid-theorem, sieve-sequence, gap-dynamics)

## Strategy

Fix one branch at a time (small-changes rule), push, merge, then move to
the next. The citation must use the HIGHEST level available for the cited
article at the time of the fix. Merges were done in dependency order
(list first, then each dependent article).

## Final State (all on master)

| Citing article | Cites | Final link |
|---|---|---|
| list | modulo | viXra + note (ai.viXra:2609.0009) |
| list (self) | — | Published line: rxiVerse:2609.0023 (PR #32) |
| cycle (#23) | list | https://rxiverse.org/abs/2609.0023 + note |
| cycle (#23) | integral | master (level 4, no release) |
| cycle (#23) | modulo | viXra + note |
| integral (#24) | list | https://rxiverse.org/abs/2609.0023 + note |
| integral-cycle (#27) | list | https://rxiverse.org/abs/2609.0023 + note |
| integral-cycle (#27) | cycle | blob/cycle-article-v1.0.0/ tag |
| integral-cycle (#27) | integral | master |
| integral-cycle (#27) | modulo | viXra + note |
| euclid-theorem (#28) | list | https://rxiverse.org/abs/2609.0023 + note |
| euclid-theorem (#28) | cycle | blob/cycle-article-v1.0.0/ tag |
| euclid-theorem (#28) | integral, integral-cycle | master |
| euclid-theorem (#28) | modulo | viXra + note |
| sieve-sequence (#29) | list | https://rxiverse.org/abs/2609.0023 + note |
| sieve-sequence (#29) | cycle | blob/cycle-article-v1.0.0/ tag |
| sieve-sequence (#29) | integral-cycle | master |
| sieve-sequence (#29) | modulo | viXra + note |
| gap-dynamics (#30) | sieve-sequence | master (level 4, correct) |

## What is Learned

- Author-name formats are consistent: full name in headers
  (Thiago Henrique Ramos da Mata), abbreviated (Mata, T. H.) in citations.
- "Unpublished manuscript" label was removed (misleading — articles are
  published, just not peer-reviewed; the archive is a repository, not a
  magazine).
- Archive links today: modulo (ai.viXra:2609.0009), list
  (rxiVerse:2609.0023). All other articles are unreleased.
- Release pinning: cite the article's OWN release tag (e.g.
  cycle-article-v1.0.0), not the citing article's snapshot tag.
- MD link-text convention: `Available at: [URL](URL)` for archive links;
  `[Local article](URL).` kept for repo-internal links (sieve-sequence,
  gap-dynamics style); archive links must NOT say "Local article".
- Bib convention: `howpublished = {\url{...}}` + `note = {archive:ID}`
  for archive citations (e.g. `note = {rxiVerse:2609.0023}`).
- Binary merge conflicts on PDFs/tarballs: resolve by REGENERATING the
  artifacts (`just arxiv-pdf <name>` + tarball recipe), never by picking
  a side.
- All 6 article PR branches do not touch list/modulo files, so merges
  were safe. Verified post-merge: no stale citations remain on master.
- PR merge transient failure "Base branch was modified" resolves on
  retry after the previous merge settles.
- The integral §5.2 inductive-hypothesis typo (tail(L) -> tail(I)) landed
  on master via PR #24.

## Failed Paths

- (2026-09-11) Applied list-article-v1.0.2 tag citations to cycle and
  integral branches before learning list was archived at rxiVerse:2609.0023;
  required follow-up commits on both branches to bump to the archive link.
  Lesson: confirm the highest available level right before pushing.

## Open Concerns

- cycle-article-v1.0.0 tag predates PR #23's merged changes; citing it
  pins to the released snapshot (release-pinning semantics — acceptable).
- When integral/integral-cycle/euclid-theorem/sieve-sequence/gap-dynamics
  get releases or archive links, dependent citations must be bumped
  (inherent to the hierarchy). No bump policy set yet — bump when the
  citing article is next revised.
- gap-dynamics LaTeX package (articles/arxiv/gap-dynamics/) exists only
  as untracked local files; committing it to the branch is a separate
  task.
- list-article-v1.0.2 release assets (list.pdf, tarball) predate the
  Published line; clobbering them is optional follow-up.

## Update (2026-09-21): Zenodo Archive Tier

The hierarchy's "Open Concerns" note above ("when integral/integral-cycle/
euclid-theorem/sieve-sequence/gap-dynamics get releases or archive links,
dependent citations must be bumped") has started happening. A new tier sits
above "Release (GitHub release tag)": **Zenodo DOI**, minted by depositing an
article's own arXiv PDF/source package to Zenodo directly (separate from the
repo-wide Zenodo archival that already covers every GitHub Release).

- `integral` deposited to Zenodo (10.5281/zenodo.22746792); every citation to
  it (`cycle`, `integral-cycle`, `euclid-theorem`, `sieve-sequence`) bumped
  from level 3/4 to the DOI.
- `cycle` deposited to Zenodo (10.5281/zenodo.22865441); every citation to it
  (`integral-cycle`, `euclid-theorem`, `sieve-sequence`) bumped from the
  `cycle-article-v1.0.0` tag to the DOI. `cycle.md`'s own pinpoint citations
  into `modulo.md` subsections were separately synced from `blob/master` to
  `blob/cycle-article-v1.0.0`, matching what its already-released LaTeX
  package had done at release time but the Markdown had never picked up.
- `integral-cycle` deposited to Zenodo (10.5281/zenodo.22868423); citations
  to it from `euclid-theorem` and `sieve-sequence` bumped to the DOI. One
  pinpoint subsection citation (`cycle`'s reference into `integral-cycle`
  §6.1) was deliberately left on the tag-pinned GitHub link, since a bare
  DOI can't address a specific subsection the way a tag-pinned anchor can.
- `euclid-theorem` went through the same release-prep pass `cycle`/`list`/
  `modulo`/`integral-cycle` already had: self-referencing source links
  pinned to a new `euclid-theorem-article-v1.0.0` tag, and a missing
  Appendix B added with a freshly reproduced chapter-5 verification log
  (2,145 valid, 0 invalid, 0 unknown). Not yet deposited to Zenodo.
- Repo-wide sweep (`.md`+`.tex`+`.bib`) confirmed zero remaining stale
  cross-article citations after these bumps.

Lesson confirmed from "Open Concerns": every time a cited article gains a
higher citation tier, every existing citation to it needs a follow-up bump —
this is now a recurring, expected step each time an article is deposited to
Zenodo, not a one-off.

## Learning Log

| Date | Entry |
|---|---|
| 2026-09-11 | Ticket created. Hierarchy defined by author: magazine > archive > release > internal. |
| 2026-09-11 | Fixed cycle (#23): wrong snapshot-tag citations -> list tag, integral master, modulo note. |
| 2026-09-11 | Fixed integral (#24): 6 list citations -> release tag. |
| 2026-09-11 | Learned list is archived at rxiVerse:2609.0023 (author provided link). |
| 2026-09-11 | integral-cycle (#27) committed final: list -> rxiVerse archive, cycle -> tag. |
| 2026-09-11 | list article: Published line added (rxiVerse:2609.0023) in list.md + main.tex, PDF rebuilt. |
| 2026-09-12 | Plan approved by author: merge all PRs in order, no new releases, no AI mentions in PRs. |
| 2026-09-12 | PR #32 (list Published line) merged after resolving binary conflicts by regeneration. |
| 2026-09-12 | cycle #23, integral #24, integral-cycle #27, euclid-theorem #28, sieve-sequence #29, gap-dynamics #30 all merged in order. |
| 2026-09-12 | Post-merge verification on master: zero stale citations; §5.2 typo fix confirmed on master. Ticket archived. |
