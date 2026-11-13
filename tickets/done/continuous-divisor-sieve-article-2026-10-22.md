# Continuous divisor sieve: article draft

Created: 2026-10-22
Status: Completed — article-draft consolidation and guideline review

## START HERE

User asks to improve the imaginary-function draft to match the other articles.
Consolidate the existing uniform divisor-sieve note and wave analysis into
articles/chapter6/draft-continuous-divisor-sieve.md and its faithful arXiv package.
Keep the research notes. User prefers mathematical development without a
Stainless side-by-side implementation; state the mathematical-only proof scope
once, without implying a scheduled verification task.

## Goal

A self-contained mathematical draft with consistent notation, complete proofs
of the existing properties, source credit at use, honest scope, and a clean
PDF produced by the existing just arxiv-pdf command with passing parity.

## Strategy

Establish a green new-document skeleton, then add one property per unit with
MD-to-LaTeX sync and existing build/parity gates. Reuse proved arguments:
normalized Fejer waves; activated recurrence; local finite stabilization;
integer divisor height and prime contacts; redundant composite filters;
square-root certification; divisor factorization/parity/multiplication;
simultaneous twin contacts; translated folding; activation correction; bounded
twin amplitude. Candidate estimates remain open, not new theorems. No Scala,
Python, existing article, renderer, or executable recipe changes are planned.

## Related Work

- [Original construction](../future/continuous-complex-sieve.md).
- [Wave research](../active/continuous-wave-twin-research.md).
- [Completed attribution correction](../done/article-attribution-priority-audit-2026-10-21.md).
- [Uniform note](../../properties/sieve-sequence/uniform-continuous-divisor-sieve.md).
- [Wave analysis](../../properties/sieve-sequence/research/continuous-wave-twin-analysis.md).
- [Attribution inventory](../../properties/sieve-sequence/research/continuous-sieve-attribution.md).

## Current State

Completed the self-contained draft at
articles/chapter6/draft-continuous-divisor-sieve.md and faithful package
articles/arxiv/draft-continuous-divisor-sieve/. Its 15-page PDF is
output/pdf/draft-continuous-divisor-sieve.pdf within that package.
Existing just arxiv-pdf and arxiv-parity gates pass cleanly; final log:
/private/tmp/continuous-article-final.log (18 matched headings, 48 math labels,
9 URLs; no advisories). All 15 final pages were rendered and visually checked
at /private/tmp/continuous-article-final-01.png through -15.png. The intro list
lead now stays with its list. No figures or image-only pages exist.

All 63 math fences, six introduction groups, 33 internal links and seven
cited references passed coverage/anchor/scope checks. Mathematical proofs
passed Critic review; house style and guidelines passed Monitor review.
Proof status is stated once in the abstract. No Scala verification is claimed
or scheduled. The original uniform note links to the article edition, with
its mathematics preserved. Existing source/media/article edits outside this
scope were not changed. No new DOI, commit, push or publication was made.

## What is Learned

W_m is a normalized Fejer kernel, not a newly discovered general sine wave.
Activation protects each filter's own integer and fixes the past endpoint by
endpoint. Compact stabilization needs the shifted domain X+2 for pair curves. The
interval bound X is distinct from the pair height B(t).
Mathematical identities do not establish historical originality or distribution.
Existing source proofs cover the planned properties; quadratic/sixfold and
independent count estimates remain research directions, not proved here.

## Failed Paths

- Final inspection accidentally used host Python, which lacks pypdf; no
  document or build changed. Retried only the reader using the bundled
  codex-primary-runtime Python successfully before the layout edit. Always
  use that runtime for PDF inspection; host Python is viable only after
  independently confirming its dependencies.

No mathematical or publication-build attempt has failed. One read assumed a root notes directory;
the actual materials are properties notes and tickets. Use the discovered
paths, and retry a root notes search only if such a directory is added.

## Open Concerns

The proofs are mathematical and not Stainless-verified; formalization is not
an active obligation of this user-authorized mathematical draft. Exact
historical priority of the activated combinations remains unassigned.
No twin-prime infinitude, frequency estimate or efficiency result is claimed.
Independent integer-contact lower bounds and the coordinate/finite-period
comparison remain separate research directions, explicitly scoped in Future
Work. The unreliable Hardy-Wright locator in the wider guide is recorded
below but not propagated. It is outside this article-draft correction scope.

## Validation

Independent Critic semantic and Monitor rule reviews for each unit. Existing
just arxiv-pdf draft-continuous-divisor-sieve must exit zero with clean compile log;
just arxiv-parity draft-continuous-divisor-sieve must PASS. Check local links, fences,
proof coverage and MD/TeX fidelity. Render and inspect every final PDF page.
No Scala/Python gates apply to article-only work. No new DOI is assigned.

## Next Action

No article-draft work remains in this scope. Deliver the Markdown and PDF.
Any further mathematical research proceeds under the existing wave-research
ticket; it is not silently asserted complete by this consolidation.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-22 | No article edition yet exists; the draft is spread across two mathematical notes. | Opened this scoped consolidation ticket, retaining notes and prior working changes. |
| 2026-10-22 | Skeleton built clean and parity PASS; fixed 13-section plan established. | Complete Property 1 selective-wave proof; prior green log /private/tmp/continuous-article-skeleton.log. |
| 2026-10-22 | Selective-wave proof and precise normalization passed clean build/parity and semantic review. | Complete activated recurrence and monotonicity; prior green log /private/tmp/continuous-article-02.log. |
| 2026-10-22 | Selective waves and activated recurrence passed mathematical review and clean existing build/parity. | Complete compact stabilization and continuity; prior green log /private/tmp/continuous-article-03.log. |
| 2026-10-22 | Compact stabilization and continuity proved and reviewed; clean existing build/parity passed. | Complete integer divisor height and prime contacts; prior green log /private/tmp/continuous-article-04.log. |
| 2026-10-22 | Prime-contact equivalence proved and reviewed with clean build/parity. | Complete composite redundancy and first prime-step rejection; prior green log /private/tmp/continuous-article-05.log. |
| 2026-10-22 | Composite redundancy and prime p-squared first rejection reviewed and built green. | Complete finite-stage square-root certification; prior green log /private/tmp/continuous-article-06a.log. |
| 2026-10-22 | Composite redundancy and finite-stage certification reviewed and built green. | Complete divisor factorization and low-height classifications; prior green log /private/tmp/continuous-article-06b.log. |
| 2026-10-22 | Divisor product and low-height classifications reviewed and built green. | Complete square-parity property; prior green log /private/tmp/continuous-article-07a.log. |
| 2026-10-22 | Square-parity proof reviewed and built green, completing the second divisor-height law. | Complete coprime multiplication law; prior green log /private/tmp/continuous-article-07b.log. |
| 2026-10-22 | All three divisor-height laws proved, reviewed and built green. | Complete direct paired-wave twin-contact construction; prior green log /private/tmp/continuous-article-07c.log. |
| 2026-10-22 | Direct paired-wave construction and exact twin-contact theorem reviewed and built green. | Complete translated bare-wave folding identity; prior green log /private/tmp/continuous-article-08.log. |
| 2026-10-22 | Translated-wave folding identity proved, reviewed and built green. | Complete exact filter-four activation correction; prior green log /private/tmp/continuous-article-09.log. |
| 2026-10-22 | Activated filter-four correction proved, reviewed and built green. | Complete bounded twin amplitude and exact contact equivalence; prior green log /private/tmp/continuous-article-10.log. |
| 2026-10-22 | Bounded amplitude and exact finite/completed contact equivalence reviewed and built green. | Complete future-work scope and exact integer-count interface; prior green log /private/tmp/continuous-article-11.log. |
| 2026-10-22 | Future-work count interface and explicit scope boundaries reviewed and built green. | Complete premise-preserving conclusion and property recap; prior green log /private/tmp/continuous-article-12.log. |
| 2026-10-22 | All mathematical sections and full conclusion recap proved and built green; 63 math blocks preserved in prose pass. | Complete house-prose and framing conformance; prior green log /private/tmp/continuous-article-13.log. |
| 2026-10-22 | House prose/framing conforms to full guides and all math blocks remain unchanged. | Complete source and internal-reference conformance; prior green log /private/tmp/continuous-article-prose.log. |
| 2026-10-22 | Reference conformance reviewed and built green with all original math blocks preserved. | Complete relation spacing, bound notation and proof/recap alignment; prior green log /private/tmp/continuous-article-references.log. |
| 2026-10-22 | Publication-series voice requires the full guides as well as a matching outline; proof status is a factual once-only statement. | Completed draft-prefix MD/LaTeX/PDF, seven sources, all proof groups, final clean build/parity and 15-page visual review; source note discovery link added, original mathematics and unrelated work preserved. |

## Section Plan

00 abstract; 01 introduction; 02 preliminaries (selective waves); 03 recurrence; 04 local limit;
05 prime contacts; 06 filter effects/certification; 07 divisor laws; 08 twins;
09 folding; 10 activation correction; 11 bounded amplitude; 12 future work;
13 conclusion; 14 references (BibTeX, unnumbered in PDF). No hardcoded
cross-references will be added before these numbers are fixed.

Section-plan addition: 6.1 Which Filters Remove Contacts. No earlier section numbers change.

Section-plan addition: 6.2 A Certified Region. Existing section numbers remain unchanged.

Section-plan addition: 7.1 Factorization and Low Heights.
Style steering: match neighboring articles at sentence level as well as layout,
including motivation, mathematical transitions, citation placement and scope.

Section-plan addition: 7.2 Odd Heights and Perfect Squares.

Section-plan addition: 7.3 Coprime Multiplication.

Scope gap recorded: finite-stage tail periodicity and survivor-index Fourier
cycle-integral comparison are not developed here; Section 12 states the
distinct coordinates explicitly. They are structural extensions, not claimed
open number-theoretic theorems.

Guideline audit: full CONTRIBUTING, PROOF_GUIDE Voice/Style and VOCABULARY
read against early finished articles. Once-only verification status, linked
property-group preview, framing plus chapter summaries and abstract markup
are enforced. No mathematical fence changed in the house-prose unit.

Source-audit caution: CONTRIBUTING cites Hardy-Wright 1979 section15.1 for
Eratosthenes, but that pinpoint is not reliable. Do not copy it. The article
uses a whole-book reference without a pinpoint, alongside inspected DLMF27.18.
Google Books metadata endpoint was inaccessible; no unavailable book page was
claimed inspected. Correcting the wider guideline/older articles is outside
this draft unit. No mathematical or executable change is made for this credit.

Math-markup check: normalized fenced statements unchanged after spacing,
proof-end symbols, recap-label columns and bound B-to-X alpha-renaming.
Pair height B(t) is retained; compact bounds use X consistently.

Lifecycle checkpoint: the Markdown, LaTeX package and existing PDF basename
were renamed with the required draft prefix, preserving every artifact.
The final gates passed using just arxiv-pdf/parity draft-continuous-divisor-sieve.
