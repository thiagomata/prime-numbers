# arXiv parity automation (MD <-> LaTeX <-> PDF)

**Created:** 2026-09-13
**Status:** In progress
**Depends on:** `arxiv-sync` rule (AGENTS.md), `arxiv-pdf` zero-warning gate
(justfile), `integral-cycle-arxiv-latex-2026-09-06.md` (manual parity
precedent), `articles/arxiv/CONVERSION_GUIDE.md` §5 (parity definition)

## Goal

One command that machine-checks, per article package, that the arXiv
LaTeX edition and the built PDF are in sync with the Markdown source
edition. Replaces the manual parity passes recorded in each conversion
ticket ("41/41 subsections, 16/16 listings" done by hand).

## Strategy

Chain of gates rather than direct MD-vs-PDF diff (PDF text extraction is
lossy: hyphenation, camel-case breaks, spacing):

1. MD <-> tex content parity (headings bidirectional, verified-function
   identifiers, math-block bracketed tags) — the faithful-conversion
   invariant from CONVERSION_GUIDE §1.
2. tex -> PDF via the existing `just arxiv-pdf` build (exit 0 + clean
   log, already machine-enforced).
3. Freshness: `output/pdf/<article>.pdf` mtime must postdate the MD and
   every tex/bib source (catches stale builds and MD-edited-but-tex-not).
4. PDF text smoke: identifiers (and tags, warn-level) must appear in the
   gs text layer with whitespace stripped.

Guide-documented intentional substitutions are built in as allowed
absences (Abstract/References headings -> LaTeX front matter/bibliography;
Appendix B -> dropped as GitHub-only). URLs are warn-level (per-article
substitutions exist). Per-article extras can be exempted via an optional
`.parity-skip` file.

## Current State

- DONE: `python/tools/arxiv_parity.py` + `just arxiv-parity [article]`
  recipe. Six checks per package: freshness (git-corrected content time
  vs md/tex/bib sources), bidirectional headings, identifiers in tex,
  identifiers in PDF text, math labels in tex, math labels in PDF text
  (warn); URLs warn-level.
- DONE (repo-standard refactor, 2026-09-13): the tool was originally at
  `scripts/arxiv-parity.py` (never committed); it now lives in
  `python/tools/` alongside the other repo tools and follows
  python/ARCHITECTURE.md Convention 1 — pure no-I/O normalization and
  extraction functions, with `main()` as the only I/O runner. Covered by
  `python/tests/test_arxiv_parity.py` (26 tests: every normalization
  quirk plus two end-to-end synthetic-package runs). Full suite 275
  green (`just empirical-test`); `just arxiv-parity` PASS on all eight
  packages. Doc references synced: CONVERSION_GUIDE §5 now cites the
  new path, python/README.md tools/ listing and test counts updated
  (249 -> 275 in README.md and ARCHITECTURE.md).
- Referenced from AGENTS.md rule `arxiv-sync` and CONVERSION_GUIDE §5.

## Post-commit hardening (2026-09-13, PR #35 review round)

- REAL BUG (freshness): the comparison was asymmetric — sources used
  git-corrected commit time, the pdf used raw working-tree mtime. Every
  package FAILed freshness after the first commit session (pdf built
  before the commit always reads older). Fixed: `effective_time(pdf)`
  on both sides; regression test
  `test_freshness_compares_content_time_on_both_sides`.
- NEW CHECK (dangling-a, FAIL-level): sentence-surgery tripwire
  `find_dangling_articles` flags a sentence-final 'A' left
  paragraph-final (the gap-dynamics de-draft removed "A supplementary
  record ..." sentences and left 14 stray "A"s in 6 tex files; they
  rendered in the published PDF). Wrapped sentences ("...quantity. A\n
  weighted ...") are exempt via lookahead; a paragraph genuinely ending
  in a standalone "A" ("Plan A") would false-positive — none exists in
  the current packages.
- New false-negative class recorded: tex-only PROSE surgery is invisible
  to headings/identifiers/labels/URLs checks; the dangling-a tripwire is
  the first prose-level guard. Found by the owner's manual PR review,
  not by the gate — keep manual line-level review in the loop.

## Real defects the tool found (fixed this session)

- `articles/arxiv/integral-cycle/sections/08-appendix.tex`: a stray
  `\section{Scala Verification Code}` line had REPLACED the A.9 listing's
  closing `}.holds` — the published PDF rendered a bogus code line and
  lost the listing terminator. Restored `}.holds`.

## Real desyncs found

NONE. The two initial "real fail" candidates both dissolved under
inspection (2026-09-13) and required NO article changes:

- cycle "missing label `[Modulo Idempotence + Distributivity over
  Addition]`": the label IS in the tex, split inside a `\substack{...\\
  ...}` construct (05-cycle-properties.tex:396-397). Script gap, class 6:
  plain_tex now joins `\\` line breaks and strips `\substack`.
- gap-dynamics "extra tex section Research Map": the de-drafting pass in
  the gap-dynamics ticket ALREADY unhooked sections/14-appendix-b-research-map
  from main.tex (file kept on disk per never-destroy). Script gap, class 5:
  the parity script now derives its tex source list from main.tex's
  \input / \IfFileExists assembly instead of globbing sections/ —
  unhooked-but-kept files no longer count. (Watch the double capture:
  `\IfFileExists{X}{\input{X}}` names each file twice — dedupe.)

## Final scoreboard (2026-09-13, after all six false-positive classes fixed)

PASS: cycle, euclid-theorem, gap-dynamics, integral-cycle, integral,
list, modulo, sieve-sequence — the whole repo is in md <-> tex <-> PDF
sync. Remaining WARNs are documented intentional substitutions or benign
extraction quirks: verify.log URLs (Appendix B, silencable per-package via
.parity-skip), doi.org link rendered via bib doi field (cycle), 2
gap-dynamics labels (PDF superscript reordering / math-text hyphenation),
1 list label (`++` construct).

## False-positive classes found and eliminated (2026-09-13, same session)

- "Stale PDFs" on 6 packages (cycle, euclid, integral, list, modulo,
  sieve-sequence): ALL were mtime artifacts — branch operations rewrite
  file mtimes without changing bytes; git verified every package's
  content commits predate its PDF build and the working tree is clean.
  The FIRST report in this ticket claiming 6 stale PDFs was WRONG.
  Fix: git-aware freshness (unmodified file => content time = last
  commit time; dirty file => mtime).
- modulo pdf-ids "missing from PDF": the 2 ModIdempotence identifiers
  live in the md ONLY as link URLs (display text is prose); the tex
  preserves them as pinned-release hrefs, so they never render as PDF
  text — by design. Fix: identifiers occurring only inside URLs are
  validated against tex only.
- list/modulo url warns (10 and 25 URLs): release link pinning — tex
  pins source links to the article's release tag
  (`blob/modulo-article-v1.0.0/`, `blob/list-article-v1.0.0/`) while md
  uses `blob/master/` (documented substitution, CONVERSION_GUIDE §4).
  Fix: ref-agnostic URL comparison (`blob/<ref>/` -> `blob/*/`).
- Remaining known warn-level quirks (left as warnings, not chased):
  verify.log URL (intentional, per-package `.parity-skip`), doi.org
  link rendered via bib `doi` field (cycle), cross-article md#anchor
  links converted to hardcoded refs (cycle), raw-SVG figure URLs
  (gap-dynamics/sieve-sequence, now in their `.parity-skip`), 2
  gap-dynamics labels whose PDF extraction reorders superscripts or
  hyphenates math text, 1 list label (`++` construct).

## What is Learned

- Compare md <-> TEX sources, not md <-> PDF text: gs txtwrite hyphenates
  prose ("Gen-er-a-tion") and breaks identifiers at allowbreak points, so
  PDF text is only reliable for whitespace-stripped identifier/label smoke
  checks.
- Whole-file whitespace-stripped haystack matching makes split content
  match: a label the conversion split across two `equation*` displays is
  still found contiguous once newlines are stripped.
- LaTeX encodes § as `\S` and cross-refs as `Subsection~N.M`; both must
  be normalized to the md's `§N.M` form before comparing.
- `\texorpdfstring{...}{...}` titles need brace-matched unwapping (nested
  `\texttt{}` braces defeat a one-level regex) BEFORE splitting off
  ` --- ` identifier suffixes; the suffix separator can be ` -- ` in the
  plain-text argument.
- Headings must be extracted from listing-stripped tex: a `\section` inside
  a `lstlisting` is source text (this is how the A.9 corruption hid from
  the manual audits).
- Tag extraction needs a junk filter: md math blocks contain bracketed
  list literals (`[v_0, v_1, \dots]`) and index expressions
  (`[(k+j) \bmod n]`); real labels carry `[A-Z][a-z]` or are `[Q.E.D.]`.
- The log-output appendix (md Appendix B / tex verification-log section)
  is handled differently per package; normalize both sides out of parity.
- The zero-warning build gate and the parity gate compose into a chain:
  md <-> tex (parity script) + tex -> PDF (build, log-clean) + freshness
  (mtime ordering) = md <-> PDF assurance without diffing PDF text.
- `plain_tex` must preserve case: main() matches mixed-case identifiers
  (`assertNextPosition`, `...Properties`) against its output verbatim;
  lowercasing belongs to `heading_title` only. The mid-refactor test
  expecting `plain_tex("B\\'ezout") == "bézout"` had a typo in the
  expectation (dropped the capital B) — fixed to `Bézout`, not the
  function.

## Failed Paths

- First-pass tag extraction with no filter: 22 false positives on
  integral-cycle alone (list literals, index expressions) — fixed with the
  label filter, not by weakening the gate.
- One-level texorpdfstring regex: failed on cycle's nested `\texttt`
  title, producing a mangled heading — fixed with brace-matched scanner.
- String match `"verification log" in title` never fired because
  normalized titles are whitespace-stripped (`verificationlog`) — fixed.

## Open Concerns

- list's 11 missing scala URLs: possibly real sync debt from the citation
  hierarchy work; needs the list ticket's attention.
- Freshness uses mtime: a `git checkout`-style restore (or rebase) can
  set older mtimes and mask staleness — acceptable trade-off, the content
  checks remain.

## Next Action

- The earlier next steps (stale-PDF rebuilds, desync triage) are all
  resolved — see the Final scoreboard and false-positive-classes sections
  above. Remaining: commit the repo-standard refactor (tool + tests +
  justfile + doc-reference sync). Optional follow-ups: give the list
  package's 11 scala URLs a decision in the list ticket, and extend
  `.parity-skip` usage notes into CONVERSION_GUIDE if a ninth package
  converts.
