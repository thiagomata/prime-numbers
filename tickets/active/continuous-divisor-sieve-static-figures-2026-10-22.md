# Static figures for the continuous divisor-sieve draft

Created: 2026-10-22
Status: Complete — figure rendering gap closed; article displays all three
graphs in the Markdown edition and builds/parity green

## START HERE

Create paper-ready static graphs inspired by the existing animations, then
integrate them into the article Markdown and matching LaTeX/PDF. Preserve the
mathematical statements and unrelated dirty work. Establish scoped baselines
before code or article changes.

## Goal

Three reproducible vector figures with PNG previews, meaningful Python tests,
accurate captions and source provenance, synchronized MD/TeX, and a clean
existing just PDF/parity build with inspected figure-page layout.

## Strategy

Plot (1) bare W4 and activated a4 W4 on [2,12], protecting 4 while raising
later multiples; (2) completed prime and pair heights on [2,31], covering both
endpoints through 33; (3) additive and bounded pair heights on [2,19], covering
endpoints through 21. Reuse the animation's teal/gold/coral roles with darker
print-safe colors on white, plus line-style redundancy. Mark contacts from an
independent integer oracle, not floating-point zero tests. Compute sampled
curves from the definitions, not screenshots or generated illustrations.

Use a standalone plotting module independent of Manim imports, with local
dependency/reproduction instructions and unit tests of arithmetic, sampling,
renderer contents and exported files. Use the available Python plotting
runtime without editing the already-dirty project metadata. Add one figure
at a time to MD/TeX with nearby explanatory prose and full captions. Build
with existing just arxiv-pdf and arxiv-parity commands only.

## Related Work

- [Article consolidation](../done/continuous-divisor-sieve-article-2026-10-22.md).
- [Original animation](continuous-complex-sieve-manim.md).
- [Two-gap animation](continuous-two-gap-focused-animation.md).
- [Wave mathematics](continuous-wave-twin-research.md).
- [Article source](../../articles/chapter6/draft-continuous-divisor-sieve.md).
- [Animation source](../../presentations/continuous-complex-sieve/uniform_prime_twins.py).

## Current State

Scoped baselines green: 8 existing chart tests, 1024 animation integer checks,
and clean article PDF/parity (18 headings, 48 labels, 9 URLs). Critic and
Monitor approved the standalone tool/test unit. Added its source, adjacent
stdlib tests and local reproduction/dependency documentation. Seven arithmetic,
sampling, renderer and export tests pass; CLI help and ordinary import pass.
Source post-review and canonical export pre-review passed. Exported the nine
canonical assets and inspected all PNG and vector-PDF previews. Added all three
figures to the Markdown and matching LaTeX package; the article now builds to
17 pages and parity passes. Figure pages have nearby explanatory prose and
captions; no image-only page was produced.

## What is Learned

The animation module imports Manim on ordinary import, so use an independent
static module with formula provenance. Stage 33 is a safe complete cutoff
for both plotted endpoints through 33; stage 21 covers starts through 19.
Show imaginary height against real input, explicitly distinguishing pair
start t from endpoint t+2. A plot illustrates a proved representation, not a
new distribution claim or a numerical certificate on all real inputs.

## Failed Paths

Initial inventory searched a nonexistent root tests directory; tests are under
python/tests. Bundled Python lacks Matplotlib and pytest, so its first baseline
attempt failed before any source edit. Resolved under the reviewed baseline
retry: system Python has NumPy 2.5.3/Matplotlib 3.11.2; core python/.venv has
pytest for existing tests. Use a writable MPLCONFIGDIR to avoid cache warnings.

## Open Concerns

Keep contact classification exact, make every integer part of the sample
grid, avoid removable-singularity artifacts, and retain the shifted endpoint
range. Dense labels need print-scale inspection. Each figure page must have
nearby prose/equations rather than a lone image. Do not change existing dirty
Python metadata or any Scala source.

## Validation

Before edits: Python runtime/dependency/import checks, closest existing chart
unit gate and animation numerical CLI check; current article just build/parity.
After new module: meaningful unit tests plus import and CLI export checks.
After each article insertion: existing just arxiv-pdf/parity, clean compile
log, MD/TeX math-preservation and caption checks. Inspect every figure and all
changed PDF pages; verify vector exports, contact sets and no clipped labels.
No Scala or Stainless gate applies to this plotting/document-only task.

## Next Action

None. The thread is committed as44956e10 and pushed to
origin/feature/imaginay_function: the article, the full arXiv package
with the rebuilt PDF, the standalone figure generator with tests, the
exported assets, both tickets, and the research-note link. The
Markdown figure-rendering gap was found and closed on 2026-10-28:
the three figure links pointed at the vector PDFs, which Markdown viewers
do not render, while the exported PNG previews sat only in the
presentation output. The PNGs are now colocated with the package PDFs and
the Markdown links repointed (TeX keeps the vector PDFs). Figure 1's
alt text was additionally made bracket-free after nested square brackets
broke its rendering. The PDF was rebuilt and
`just arxiv-parity draft-continuous-divisor-sieve` passes all gates
(freshness, 18 headings, 48 labels, 9 URLs).

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-28 | Square brackets inside an image alt text (here the interval `[2,12]`) break image rendering in some Markdown viewers while leaving the caption visible; Figures 2 and 3 rendered because their alt texts are bracket-free. The same nesting also defeats naive link-check regexes, so the earlier check silently skipped Figure 1. | Rewrote Figure 1's alt text bracket-free ("from 2 to 12"); verified no other article image carries nested brackets; rebuilt the PDF and re-ran parity, all gates PASS. |
| 2026-10-28 | Relative `![...](...pdf)` image links render as nothing in GitHub/Markdown viewers, so a PDF-linked figure is invisible in the Markdown edition even though the LaTeX edition is correct. | Colocated the three PNG previews in the package figures dir, repointed the three Markdown links to `.png`, rebuilt the PDF for the freshness gate, and re-ran parity: all PASS. |
| 2026-10-22 | Static panels can reuse the animation's mathematical and color language while remaining independent of its GPU/Manim runtime. | Opened this scoped three-figure ticket with exact window/cutoff and validation requirements. |
| 2026-10-22 | Available runtimes have different dependencies; no install or core metadata change is necessary. | Corrected the failed environment baseline, then added the approved standalone plotting/test unit. |
| 2026-10-22 | All seven standalone tests pass, including exact contacts and real vector exports. | Passed source review; began the separately gated canonical asset export. |
