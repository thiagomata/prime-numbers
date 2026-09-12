# Citation Hierarchy Standardization Across Article PRs

## Goal

Apply the citation precedence hierarchy to every cross-article citation
(MD references + LaTeX bib entries), then rebuild affected PDFs:

1. Magazine (peer-reviewed) — none currently
2. Archive (viXra/arXiv) — modulo: http://ai.viXra.org/abs/2609.0009
3. Release (GitHub release tag) — list: list-article-v1.0.2, cycle: cycle-article-v1.0.0
4. Internal (master link) — unreleased articles (integral, integral-cycle,
   euclid-theorem, sieve-sequence, gap-dynamics)

## Strategy

Fix one branch at a time (small-changes rule), push, then move to the next.
The citation must use the HIGHEST level available for the cited article at
the time of the fix.

## Current State

Citation matrix (who cites whom, current link level vs required):

| Citing article (PR) | Cites | Current | Required |
|---|---|---|---|
| list (master, v1.0.2) | modulo | viXra + note (level 2) | OK |
| integral (#24) | list | master (level 4) | list-article-v1.0.2 tag (level 3) |
| cycle (#23) | list | cycle-article-v1.0.0 tag (WRONG tag) in bib; master in MD | list-article-v1.0.2 tag |
| cycle (#23) | integral | cycle-article-v1.0.0 tag (wrong, no integral release) in bib; master in MD | master (level 4) |
| cycle (#23) | modulo | viXra in bib WITHOUT note; viXra in MD | viXra + note (level 2) |
| integral-cycle (#27) | list | master | list-article-v1.0.2 tag |
| integral-cycle (#27) | integral | master | master (OK) |
| integral-cycle (#27) | cycle | master | cycle-article-v1.0.0 tag |
| integral-cycle (#27) | modulo | viXra + note | OK |
| euclid-theorem (#28) | list | master | list-article-v1.0.2 tag |
| euclid-theorem (#28) | integral | master | master (OK) |
| euclid-theorem (#28) | cycle | master | cycle-article-v1.0.0 tag |
| euclid-theorem (#28) | integral-cycle | master | master (OK) |
| euclid-theorem (#28) | modulo | viXra + note | OK |
| sieve-sequence (#29) | list | master | list-article-v1.0.2 tag |
| sieve-sequence (#29) | cycle | master | cycle-article-v1.0.0 tag |
| sieve-sequence (#29) | integral-cycle | master | master (OK) |
| sieve-sequence (#29) | modulo | viXra + note | OK |
| gap-dynamics (#30, local) | sieve-sequence | master | master (OK) |

## What is Learned

- Author-name formats are now consistent: full name in headers
  (Thiago Henrique Ramos da Mata), abbreviated (Mata, T. H.) in citations.
- "Unpublished manuscript" label was removed in PR #24's integral.md
  (master's old copy still has it; resolves on merge).
- Only ONE viXra archive link exists today (modulo, 2609.0009).
- Release tags available for citation pinning: list-article-v1.0.2 (latest),
  cycle-article-v1.0.0.
- All 6 PR branches do NOT touch list/modulo files, so merges are safe.

## Failed Paths

(none yet)

## Open Concerns

- cycle-article-v1.0.0 tag predates PR #23's current changes; citing it
  pins to the released snapshot (acceptable — release pinning semantics).
- After each article gets its own release, dependent citations must be
  bumped (inherent to release pinning).
- PDF rebuilds needed for every article whose bib changed.

## Next Action

1. Verify cycle (#23) branch citation state precisely (MD + bib).
2. Fix cycle: modulo note, list -> list-article-v1.0.2, integral -> master.
3. Rebuild cycle PDF if its LaTeX package exists on the branch.
4. Push cycle branch; repeat per branch (integral #24, integral-cycle #27,
   euclid-theorem #28, sieve-sequence #29). gap-dynamics needs no change.

## Learning Log

| Date | Entry |
|---|---|
| 2026-09-11 | Ticket created. Hierarchy defined by author: magazine > archive > release > internal. |
