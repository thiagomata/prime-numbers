# Continuous complex sieve — ManimGL animation

- [Animation: 25.8 seconds, 1280x720, 30 fps](output/continuous-sieve.mp4)
- [Final frame](output/continuous-sieve.png)
- [Scene source](continuous_sieve.py)

The animation starts with Z(t) = t + i sin²(pi t) on 2 <= t <= 31.
It then adds the filters for 2, 3 and 5. Each filter raises later multiples
off the real axis while leaving its own prime in place. Together these
filters remove every composite in the displayed window. The final contacts
are 2, 3, 5, 7, 11, 13, 17, 19, 23, 29 and 31.

The plotted height is

```math
\operatorname{Im}Z_P(t)=\sin^2(\pi t)+
\sum_{p\in P}\min(1,\max(0,t-p))
\left|\frac1p\sum_{\ell=0}^{p-1}e^{2\pi i\ell t/p}\right|^2.
```

Unweighted filters make lifted composites easier to see than geometrically
shrinking weights. Positive weights preserve the same contact set. In the
infinite continuation, activation makes the unweighted sum locally finite,
so it still defines a continuous curve. The finite animation stops at filter
5; it does not depict all filters of the infinite construction on this window.
Curves are sampled, with every displayed integer explicitly included.

The squared wave is a normalized **Fejér kernel**: credit Lipót Fejér's
[1900 paper](https://history-of-approximation-theory.com/fpapers/fej1OCR.pdf).
Roots-of-unity orthogonality is classical; Rodrigo Raya and Manuel Eberl's
[AFP development](https://isa-afp.org/entries/Gauss_Sums.html) provides a modern
formalization. The sieve of Eratosthenes and the divisor-function identities
behind the heights are classical too; modern references are
[DLMF27.18](https://dlmf.nist.gov/27.18) and
[DLMF27.3](https://dlmf.nist.gov/27.3).
The specific activated interpolation has unestablished historical priority.
See the [claim-level attribution inventory](../../properties/sieve-sequence/research/continuous-sieve-attribution.md).

## Reproduce

Use [3b1b ManimGL](https://github.com/3b1b/manim), distinct from Manim Community.
Tested on macOS with Python 3.13, OpenGL 4.1 / Apple M1 Pro, FFmpeg,
ManimGL 1.7.2, setuptools 80.10.2 and audioop-lts 0.2.2. LaTeX is not required.

Run commands from the repository root. The isolated environment used for
this render can be recreated with:

```bash
python3.13 -m venv /private/tmp/continuous-sieve-manim-venv
/private/tmp/continuous-sieve-manim-venv/bin/pip install 'manimgl==1.7.2' 'setuptools==80.10.2' 'audioop-lts==0.2.2'
```

Check the mathematical samples without importing ManimGL:

```bash
/private/tmp/continuous-sieve-manim-venv/bin/python presentations/continuous-complex-sieve/continuous_sieve.py --check
```

Render with the saved configuration:

```bash
MPLCONFIGDIR=/private/tmp/continuous-sieve-mpl /private/tmp/continuous-sieve-manim-venv/bin/manimgl \
  presentations/continuous-complex-sieve/continuous_sieve.py ContinuousSieve \
  -w -r 1280x720 \
  --config_file presentations/continuous-complex-sieve/manim.yml \
  --video_dir presentations/continuous-complex-sieve/output \
  --file_name continuous-sieve
```

The saved YAML is identical to the configuration used to render the video;
its import and CLI checks also pass. It directs Manim's cache to a writable
temporary directory. Desktop GPU access is required in the Codex sandbox.
Avoid the --fps flag with ManimGL 1.7.2: this release parses it as a string;
the default configuration already supplies an integer frame rate of 30.

## Validation and limits

The numerical check compares 396 integer heights across four stages with an
independent integer-arithmetic oracle. It also checks the final contacts
against trial division, noninteger midpoint heights, activation boundaries,
integer sampling and the plotted height bound. Compilation, scene import,
video metadata and representative rendered frames were checked.

These checks support the visualization; they are not Stainless verification
of the analytic construction, a numerical certificate of all real-axis
contacts, or evidence of a faster prime-generation algorithm.

## Two-gap focused animation

- [Linked animation: 25 seconds, 1920x1080, 30 fps](output/two-gap-focused.mp4)
- [Final frame](output/two-gap-focused.png)
- [Standalone source](two_gap_focused.py)

This second scene links the continuous pair-contact curve
T(t)=t+i[H(t)+H(t+2)], the ordered focused cells [2,R,2,R,...], and the
separator histogram. It applies incoming filter7 to the expanded complete
period [11,221), of length210, after filters2,3,5. The curve zoom is [41,101];
the focused row and histogram use the full period, including cyclic wrap.
The finite curve is unweighted; positive weights preserve its contacts.

| Separator R | Before filter7 | After filter7 |
|---|---:|---:|
| 4 | 7 | 3 |
| 10 | 14 | 8 |
| 16 | 0 | 2 |
| 28 | 0 | 2 |

There are21 initial two-gaps and15 surviving two-gaps. The six removed starts
are47,77,89,119,131,161. Three occur in the displayed zoom:47,77,89.
Before filtering, R=10 is bad for7 because7 divides R+4; R=4 is good.
Badness permits deletion of both neighboring pairs but does not force it.
Fourteen bad separators among21 give a cyclic lower bound of4 surviving
two-gaps; the actual transition leaves15.

Earlier work by **Fred B. Holt and Helgi Rudd**,
[*Eratosthenes sieve and the gaps between primes*](https://arxiv.org/abs/1408.6002)
(2014), section2 and Corollary6.3, describes gap-cycle expansion/closure and
the complete-period 2-gap count recurrence. Here the old period has3 pairs;
expansion gives7*3=21 and filtering leaves(7-2)*3=15. The factor applies to
the old period's count. This credits the earlier cycle/count result; the
particular focused-separator histogram and lower-bound calculation need their
own derivations and are not attributed to that paper by this citation.

The contacts are surviving pairs at distance two, not a claim that all
endpoints are prime. After installing7, endpoints below the next head's
square, 11²=121, are prime when they belong to the current stream; the full
period extends beyond that safe range. The bad-separator and histogram
statements are mathematical/numerical checks, not Stainless verification.

Using the same environment and configuration described above:

```bash
/private/tmp/continuous-sieve-manim-venv/bin/python presentations/continuous-complex-sieve/two_gap_focused.py --check
```

```bash
MPLCONFIGDIR=/private/tmp/continuous-sieve-mpl /private/tmp/continuous-sieve-manim-venv/bin/manimgl \
  presentations/continuous-complex-sieve/two_gap_focused.py TwoGapFocused \
  -w -r 1920x1080 \
  --config_file presentations/continuous-complex-sieve/manim.yml \
  --video_dir presentations/continuous-complex-sieve/output \
  --file_name two-gap-focused
```

Validation checks integer contacts against independent gcd arithmetic,
hand-pinned histograms, separator phase and period reconstruction, the analytic
bad-channel detector, cyclic survival bound, noninteger midpoint samples and
zoom removal markers. Compilation/import, encoded video metadata and four
representative rendered frames also passed inspection.

## Uniform all-integer prime and twin-contact curves

- [Animation: 35.53 seconds, 1920x1080, 30 fps](output/uniform-prime-twins.mp4)
- [Final plot of both limiting functions](output/uniform-prime-twins.png)
- [Timed narration and expanded explanation](uniform-prime-twins-narration.md)
- [Standalone source](uniform_prime_twins.py)
- [Mathematical definition and proofs](../../properties/sieve-sequence/uniform-continuous-divisor-sieve.md)

This scene applies every integer filter2,3,4,...,32, including composites.
It plots two complex-valued functions of real t on [2,31]:

```math
F_M(t)=t+i h_M(t),\qquad
T_M(t)=t+i\bigl(h_M(t)+h_M(t+2)\bigr).
```

At finite stages, real-axis contacts are candidates. In the final upper
panel, contacts are precisely the prime values through31. In the final lower
panel, contacts are precisely starts3,5,11,17,29 of the twin pairs
(3,5),(5,7),(11,13),(17,19),(29,31). These are zero imaginary heights, not
zeros of the entire complex-valued function. Both panels use the same
horizontal scale; their vertical scales differ and have explicit tick labels.

The final curves are exact restrictions of the infinite uniform construction,
apart from graphical/numerical sampling. The lower panel evaluates heights
through t+2=33. Every filter indexed33 or greater is inactive throughout those
inputs, so filters through32 suffice for the complete continuous shape.
No approximation by omitting active infinite terms is involved.

### Viewing guide

- Approximately0–4seconds: no filters; every integer starts as a contact.
- Approximately4–14seconds: filters2 through6, including composite4 and6.
  Composite steps increase some heights without removing new integer contacts.
  The p-squared captions refer specifically to the top panel: a pair start
  can disappear earlier when its second endpoint is struck.
- Approximately14–28seconds: advance through the remaining integer filters.
  Integer contacts already settled after filter5 in this bounded window;
  the subsequent filters continue changing heights and the continuous shape.
- Approximately29–35seconds: display both limiting curves and their selected
  primes/twin starts. The lower curve touches at a start only when both
  endpoint heights vanish; subtraction would also admit equal positive heights.

Using the same environment and saved configuration:

```bash
/private/tmp/continuous-sieve-manim-venv/bin/python presentations/continuous-complex-sieve/uniform_prime_twins.py --check
```

```bash
MPLCONFIGDIR=/private/tmp/continuous-sieve-mpl /private/tmp/continuous-sieve-manim-venv/bin/manimgl \
  presentations/continuous-complex-sieve/uniform_prime_twins.py UniformPrimeTwins \
  -w -r 1920x1080 \
  --config_file presentations/continuous-complex-sieve/manim.yml \
  --video_dir presentations/continuous-complex-sieve/output \
  --file_name uniform-prime-twins
```

Validation passed1024 integer-stage comparisons with direct proper-divisor
counts, final divisor-count and trial-primality checks, composite-step contact
invariance, activation boundary and noninteger midpoint checks, plot bounds,
and exact local stabilization after adding filters33 through35. Compilation,
configured import, encoded metadata and four representative frames passed.
The illustration establishes no new prime-distribution or twin-prime
infinitude result; mathematical proofs are documented separately without
requiring Stainless formalization.
