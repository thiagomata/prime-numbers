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
