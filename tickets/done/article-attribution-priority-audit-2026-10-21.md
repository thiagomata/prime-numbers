# Article attribution and historical-priority audit

Created: 2026-10-21
Status: Targeted reference implementation complete; broader priority questions remain open

## START HERE

Answer the user's question: do the articles present established mathematics
as discoveries? Inspect actual framing and compare explicit claims with earlier
sources. The first phase was a read-only review and internal findings
report. User authorization on2026-10-22 extends this work to implementing
correct references in article Markdown and PDFs. Use existing just arxiv-pdf
and arxiv-parity recipes; do not introduce another PDF-generation method.

## Goal

Give an evidence-based assessment of classical content, earlier equivalent
results, formalization contributions, and unresolved originality. Identify
concrete wording/citation problems without alleging intent or assigning
unverified historical priority. Preserve the original wave research program.

## Strategy

Implementation phase: five small article units, each with green build/parity
baseline before edits and repeated green gates after faithful MD-to-LaTeX/bib
sync: modulo (Gauss1801), sieve-sequence (Holt-Rudd2014), gap-dynamics
(Holt-Rudd, classical analytic sources, qualified novelty), survival-frontiers
(inherited gap-count attribution), relaxed-almost-prime (qualified wording,
existing Chen references preserved). Add corresponding source credits to the
two detailed guides; they have no independent PDFs. Change no mathematical
statements, Scala/Python source or executable instructions. Check affected PDF
pages visually, including bibliography flow and absence of image-only pages.
Related conversion work: sieve-sequence-arxiv-latex-2026-09-07.md and
gap-dynamics-arxiv-latex-completion-2026-09-12.md. No headings are being added,
so hardcoded section numbers and section plans remain unchanged.

Prior review phase: review titles, abstracts, introductions, conclusions, bibliography and central
claims in ten primary articles: chapter2/modulo; chapter3/list;
chapter4/cycle, integral, integral-cycle; chapter5/euclid-theorem;
chapter6/sieve-sequence, gap-dynamics, relaxed-almost-prime;
chapter7/survival-frontiers. Review sieve-sequence-detailed and
survival-frontiers-detailed as two supplements, not two additional independent
theorem articles. Read surrounding proofs for any overlap asserted.

Classify each finding as explicit historical novelty language, missing credit
for an established result, correctly framed formal verification, elementary
consequence/application, or variant whose priority remains unresolved. Start
exact source comparisons with Holt-Rudd gap cycles and counts. Verify claimed
historical ages using original sources or scholarly editions; modern textbook
support alone does not identify a first discoverer. Record a durable report
under properties/sieve-sequence/research/ with article line locators and source
roles. That review phase made no publication edits; no new mathematical lemmas
are planned in the implementation phase either.

## Related Work

- [Continuous-wave research and note-level attribution](../active/continuous-wave-twin-research.md).
- [Detailed article editions](../active/detailed-side-versions-last-two-articles-2026-10-03.md):
  earlier point-of-use classical citations and synchronized arXiv work.
- [Survival-frontiers review](../active/survival-frontiers-article-review-2026-09-13.md):
  corrected scope and conditional probability assumptions.
- [Earlier draft literature review](../../articles/notes/review-draft-articles-2026-08-15.md):
  raised bibliography/positioning gaps but also corrected overbroad analogies.
- [Current-note attribution inventory](../../properties/sieve-sequence/research/continuous-sieve-attribution.md).

## Current State

2026-10-22: All five existing just build/parity baselines passed. Logs are
/private/tmp/attribution-baseline-<article>.log for modulo, sieve-sequence,
gap-dynamics, survival-frontiers and relaxed-almost-prime. Compile gates were
clean; parity retains preexisting sieve figure-URL and gap figure-URL/math-tag
warnings, with SUMMARY PASS. Modulo MD/TeX/Bib now credit Gauss1801. Its final
build/parity passed (/private/tmp/attribution-final-modulo.log), and affected
pages1,11 were rendered and visually checked. Sieve Sequence and its detailed
MD guide now credit Holt-Rudd's earlier mechanisms, preserving the distinct
linear Stainless contracts. Final Sieve build/parity passed with the same
baseline SVG-URL warning (/private/tmp/attribution-final-sieve-sequence.log);
pages2,7,15 were visually checked. Gap Dynamics citations and novelty framing
are synchronized; /private/tmp/attribution-final-gap-dynamics.log passes with
only baseline parity advisories. Pages2,4,6,10,26,27 were visually checked;
the analytic-source sentence grammar was repaired before final validation.
Survival Frontiers MD/TeX/Bib and detailed guide now credit the earlier
real-sieve recurrence while preserving companion assumptions. Stale Gap
section labels/anchors are corrected. Final build/parity is clean
(/private/tmp/attribution-final-survival-frontiers.log); pages7,29,35,41
were visually checked, with no low-text figure-page candidates. Relaxed
almost-prime proof-status wording is qualified identically in MD/main.tex; its
final build/parity passes and title page is visually clean. All five targeted
article units and both guide credits are complete. Final logs are
/private/tmp/attribution-final-<article>.log. All builds are clean; Sieve and
Gap retain only the recorded baseline parity advisories. Fenced math/code
blocks in all seven MD files are unchanged from HEAD; scoped whitespace,
citation anchors and expected author names in PDFs pass. Whole-PDF low-text
painted-page scan finds only Gap page10, visually checked as two related
figure/caption blocks. No Scala/Python edits or gates belong to this work.
Earlier read-only review state follows, describing that completed phase.

Reviewed the ten primary articles' key framing and conclusion prose, selected
theorem/proof bodies, and the two supplemental-guide introductions. The report
is saved at properties/sieve-sequence/research/article-attribution-priority-audit.md
and passed independent semantic/mechanical review. Snapshot is1c99c1bf.
Sieve Sequence explicitly disclaims the wheel idea; Euclid credits IX.20.
Gap Dynamics has verified earlier global-count/mechanism overlap with
Holt-Rudd, while its broad new-results framing lacks that source positioning.
Its specific signed/local variants remain priority-unresolved. At that audit-only snapshot, no publication
files had changed. Report/ticket checks passed17 local links and whitespace/fences.
The earlier attribution ledger's source label was corrected separately from
Theorem2.1 to the actual Lemma2.1, with an exact one-line green diff.
Work remains on feature/imaginay_function; unrelated dirty source, Python,
registry, cluster-data and draft-article work must remain untouched.

## Assumptions, Alternatives and Validation

- A new implementation/proof artifact can be a contribution without a new
  mathematical theorem. Check each article's stated contribution separately.
- 'We prove' is not by itself a historical first-discovery claim. Read abstract,
  scope, prior-work discussion and conclusion before classifying it.
- A matched complete-period formula does not prove all local variants known.
  Compare domains, parameters, boundaries and conclusions in source bodies.
- Existing citations may be adequate for one input but not all claimed results.
- An abstract-only audit would be faster but could produce false accusations;
  inspect matched claims and proof context before recording an overlap.
- Validation: independent Critic source/reasoning review and Monitor scope
  review; internal Markdown whitespace/link/locator checks. Runtime, Stainless
  and LaTeX gates do not apply while publications and executable files remain
  unchanged. Any later article edits must include arXiv sync/build/parity.

## What is Learned

The concern is not uniform across the corpus. Some articles already distinguish
formal verification from discovery. Gap-cycle counting has directly relevant
earlier research; cite that overlap precisely, not as proof that every custom
signed-boundary result was already known. Historical priority is a separate
claim from proof correctness and proof verification.
Gauss1801 sectionI arts.2–7 directly supplies centuries-old examples of the
congruence laws and one-representative-per-block result. This establishes
earlier exposition, not Gauss's priority for every fact. Holt-Rudd2014 includes
the product(q-2), expansion/closure and the four-closure constellation
mechanism. Total242-count comparison must retain the no-new-occurrence bridge.
The18/7 fixed-wheel calculation and exact sieve histogram identification have
not been established as original or as previously published. Standard tools
such as telescoping and quadratic inequalities must be separated from their
particular sieve applications. Existing Kochen-Stone/Chen citations were
observed in articles; this audit did not independently revalidate every cited
external theorem or machine-checked contract.

## Failed Paths

- Completion lifecycle move initially failed because tickets/done did not exist.
  The active ticket remained intact. Created the README-mandated directory
  before the same-target retry, with a no-overwrite destination guard.

- Initial lookup assumed articles/README.md existed; it does not. No files
  changed. Use rg --files and the chapter inventory instead. Retry that path
  only if an index is actually added.
- No mathematical or historical approach has failed yet. Do not repeat the
  earlier review's rejected shortcuts: the relaxed weight is not automatically
  the standard Chen weight, and companion allocation models are not simply
  Cramer's model by analogy.
- Some source routes were unavailable: Library of Congress returned403, one
  ETH individual-page request timed out, and the Kochen-Stone DOI was not
  accessible through the web tool. The ETH sectionI PDF worked and was read
  directly for Gauss. Treat the Kochen-Stone entry only as an observed article
  citation in this pass. Retry failed routes only with another working viewer
  or source; do not claim inspection of unavailable content.
- Modulo PDF inspection helper initially called unavailable pdftotext; no
  build or article edit failed. Retried only the inspection with bundled
  pypdf plus existing pdftoppm; affected-page rendering and review passed.
  Use that working viewer path; retry pdftotext only if it is installed.

## Open Concerns

Some local/signed formulas may be elementary applications or genuinely distinct
variants; neither novelty nor prior equivalence is assumed. This first pass
does not certify every theorem across the full literature. Existing article
arXiv PDFs were not rebuilt for the initial read-only audit; the later
authorized five-article correction phase has now rebuilt them green.

## Next Action

No work remains in the authorized five-article reference implementation.
Exact signed/local historical priority and exhaustive literature coverage are
not certified. The original continuous-wave research program remains a
separate pending task. The audit report is retained as its dated historical
snapshot rather than rewritten to conceal the original findings.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-21 | User explicitly asks whether the articles package old mathematics as discoveries. Initial framing is mixed, so a blanket verdict is unsafe. | Created dedicated audit ticket; exact ten-article scope and two supplements distinguished; publication edits excluded from this review unit. |
| 2026-10-21 | Foundation articles mostly frame classical mathematics as formalization; Gap Dynamics needs direct prior-work positioning and qualified novelty language. Exact signed/local priority remains unresolved. | Saved independently reviewed claim-level report with verified Gauss/Euclid/Holt-Rudd source comparisons;17 local links and document checks green. Corrected one older ledger locator; publication sources/media/code unchanged. |
| 2026-10-22 | User authorizes article MD/PDF corrections using existing just LaTeX builds. | Opened five-article synchronized implementation phase; no new math or generation method; green baseline and post-edit parity/build gates required per unit. |
| 2026-10-22 | All five publication baselines are green; existing parity warnings concern old figure URLs/text extraction only. | Modulo Gauss source credit synchronized and rebuilt green, affected pages visually checked; recorded working pypdf/pdftoppm inspection fallback. Sieve source credit next. |
| 2026-10-22 | Earlier gap-cycle mechanisms and this linear Stainless formalization need distinct credit. | Sieve MD/TeX/Bib and detailed-guide citations synchronized; clean build, parity PASS with baseline warning only, and pages2/7/15 visually green. Gap Dynamics next. |
| 2026-10-22 | Gap global counts and constellation mechanisms have prior sources; exact signed/local priority remains open. | Synchronized citations and qualified framing, repaired one sentence, rebuilt clean with baseline parity advisories, and visually checked pages2/4/6/10/26/27. Survival next. |
| 2026-10-22 | Survival inherits the real-sieve count, not companion placement or mixing premises, from earlier work. | Synchronized source credit and corrected obsolete Gap section links; final build/parity clean and pages7/29/35/41 visually green. Relaxed wording next. |
| 2026-10-22 | Proof correctness, verification status and historical originality are distinct. | Completed all five synchronized MD/LaTeX/PDF units and both guide credits; final existing builds/parity and visual checks green, math/code unchanged. Precise local priority remains unresolved. |
| 2026-10-22 | Lifecycle destination directory was absent although documented. | First rename left source intact; created done directory and retried only the ticket move, preserving outbound targets. |
