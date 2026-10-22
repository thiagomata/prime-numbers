# Continuous complex sieve — ManimGL plot

Created: 2026-10-20
Status: Complete

## START HERE

Render the user's continuous prime-contact curve with 3b1b ManimGL. First
establish an isolated rendering environment; then implement and validate one
standalone scene under presentations/continuous-complex-sieve/.

## Goal

Deliver a reproducible animation showing the continuous curve and successive
prime filters, preserving prime contacts and lifting composite contacts.

## Strategy

Use ManimGL, not Manim Community, as explicitly requested. Prefer a temporary
virtual environment and avoid modifying existing package metadata. Plot real
coordinate t against the imaginary height on a finite window. Use unweighted
filters for visibility: activation makes the full series locally finite and
preserves the same contact set as the weighted construction.

## Related Tickets

- [Continuous complex sieve notes](../future/continuous-complex-sieve.md):
  mathematical construction, activation, convergence and contact proof.
- [Sieve property landscape](../future/sieve-property-landscape.md): broader
  research context; this plot is not a new verified sieve theorem.

## Current State

ManimGL 1.7.2 and setuptools 80.10.2 are installed in
`/private/tmp/continuous-sieve-manim-venv` (Python 3.13). CLI help passes.
User authorized continuation. Import and CLI now pass with the explicit cache
configuration `/private/tmp/continuous-sieve-manim.yml` and audioop-lts 0.2.2.
Standalone OpenGL passes with desktop GPU access (OpenGL 4.1, Apple M1 Pro).
Standalone scene added at presentations/continuous-complex-sieve/continuous_sieve.py.
Numerical CLI passes 396 integer checks over four stages; final contacts are
exactly the primes through 31. Activation continuity and noninteger samples
pass, and the sampled maximum height is 3.0196 within the plotted range 3.5.
Compilation and configured scene import pass. Final video rendered successfully:
presentations/continuous-complex-sieve/output/continuous-sieve.mp4 (H.264,
1280x720, 30 fps, 774 frames, 25.8 seconds). Initial, intermediate and final
frames inspected; formula correction checked in the final render. Poster at
output/continuous-sieve.png. README and identical persistent manim.yml saved;
configuration equality, configured import and CLI checks pass.
Existing unrelated modifications remain untouched. Ticket-only failure
recording passed Critic and Monitor pre-execution review.

## Expected State

A standalone scene, documented rendering command, numerical validation of
integer contacts and selected noninteger samples, and a rendered video with
visually inspected representative frames.

## Assumptions and Validation

- ManimGL can be installed in an isolated environment: inspect installation
  results and check import plus CLI help before scene implementation.
- An OpenGL context can render in this desktop environment: run the requested
  scene and inspect the output. Rendering failure is a non-green gate.
- Numerical height matches the analytical detector: compare integer heights
  with an independent divisibility oracle and check noninteger positivity.
- Unweighted height fits the scene: bound by number of filters plus one and
  visually inspect stage labels, curve, integer markers and the final frame.

## Alternatives and Risks

Weighted filters match the displayed geometric-series variant but make later
composites hard to see; unweighted filters are mathematically justified by
local finiteness. Use the requested ManimGL rather than substituting another
renderer. Installation may need network access or native dependencies;
rendering may need a usable OpenGL context. Do not silently replace ManimGL.

## Validation

Python-only gates: baseline NumPy/FFmpeg availability; isolated ManimGL import
and CLI; scene numerical checks and import/compile; video render, ffprobe,
and representative frame inspection. No Scala or Stainless gates apply.
Every modifying operation requires Critic/Monitor review. Three failed
attempts at one micro-goal require stopping and asking for help.

## What is Learned

The upstream README names the package manimgl and requires OpenGL and FFmpeg.
LaTeX is optional: use plain text scene labels to avoid that dependency.
No new .holds lemma is planned; proof-code search requirements are inapplicable.
ManimGL 1.7.2 parses --fps as a string; omit it and use the integer default.
Plain ASCII a_p/D_p avoids unsupported subscript-p glyphs in the available
font. The activated unweighted finite sum makes composites visible without
altering the contact set. Local finiteness justifies continuous continuation.

## Failed Paths

1. Sandbox pip installation: DNS/network access blocked the package index.
   Retrying the same target with approved network access resolved the download.
2. Installed ManimGL import: `ModuleNotFoundError: No module named
   'pkg_resources'`. Python 3.13 venv does not include setuptools. Installing
   setuptools 80.10.2 resolved this specific missing dependency. Upstream
   setuptools documents removal of pkg_resources in version 82; the chosen
   conservative cap was setuptools<81.
3. Import after dependency correction: `PermissionError: [Errno 1] Cache
   directory "/Users/thiagomata/Library/Caches/manim" does not exist and could
   not be created`. XDG_CACHE_HOME does not redirect this macOS appdirs path.
   A future explicit Manim configuration setting directories.cache to a
   writable temporary directory should address the observed cause, but is
   untested and has not been executed. Three-attempt rule requires user
   direction before another setup attempt.
4. After user continuation, cache correction exposed missing audioop/pyaudioop
   in pydub on Python 3.13. Installing audioop-lts 0.2.2 resolved import.
5. Sandbox OpenGL check could not choose a pixel format. The identical check
   with approved desktop GPU access passed; future renders require escalation.
6. First render failed at initial animation with int/string division because
   --fps 30 is parsed as a string in installed ManimGL 1.7.2. Omitting the flag
   resolved it; the default YAML supplies integer 30. Reconsider only if the
   upstream version fixes argument parsing.
7. Second render encoded successfully but visual QA found unsupported
   subscript-p glyphs. Replacing only those glyphs with ASCII a_p/D_p resolved
   it; third render and final-frame visual QA passed. Unicode subscripts could
   be reconsidered with a font that demonstrably supports them.

## Open Concerns

ManimGL setup and scene render are green. Mathematical contact
arguments are not Stainless-verified. Numerical tolerances are for plotting
validation, not proofs of primality.

## Next Action

Done. Deliver the video, final-frame preview and reproducible scene source.
No Scala or article publication changes are required for this animation.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-10-20 | ManimGL absent; FFmpeg and NumPy available. | Recorded isolated setup and Python-only validation plan. |
| 2026-10-20 | Sandbox blocked package download. | Approved network retry installed ManimGL in the temporary venv. |
| 2026-10-20 | ManimGL 1.7.2 imports pkg_resources, absent from the fresh venv. | Installed setuptools 80.10.2; CLI help passes. |
| 2026-10-20 | Default macOS Manim cache ignores XDG_CACHE_HOME and is outside writable roots. | Stopped after third setup failure; recorded explicit temporary-cache proposal without executing it. |
| 2026-10-20 | User authorized continuation; explicit cache configuration and audioop-lts resolve import. | Import and CLI pass. |
| 2026-10-20 | GPU access is required for the standalone OpenGL context. | Escalated check passes on Apple M1 Pro; setup green, scene cleared for implementation. |
| 2026-10-20 | Independent integer oracle agrees with all four plotted stages; primes remain contacts. | Numerical CLI, compilation and configured scene import pass; render next. |
| 2026-10-20 | Installed ManimGL parses explicit FPS as a string. | Removed the flag; render uses verified default of 30 fps. |
| 2026-10-20 | Rendered fonts lack the chosen subscript-p glyph. | Single-label ASCII correction; numerical/import gates and final render pass. |
| 2026-10-20 | Final contacts match primes through 31; layout and formula visually checked. | Saved 25.8-second video, poster, persistent configuration and reproduction instructions; complete. |
