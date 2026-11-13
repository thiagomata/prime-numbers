# Static continuous divisor-sieve figures

These computed figures accompany [the article](../../../articles/chapter6/draft-continuous-divisor-sieve.md)
and reuse the teal/gold/coral roles of [the animation](../uniform_prime_twins.py),
with darker colors, white backgrounds and redundant marker/line styles for print.
They require NumPy and Matplotlib, not Manim. Dependencies are pinned locally
in `requirements.txt`; no change to the project's core Python package is needed.

From the repository root, with those dependencies available:

```sh
MPLCONFIGDIR=/private/tmp/continuous-divisor-mpl python3 -m unittest discover -s presentations/continuous-complex-sieve/figures -p 'test_*.py'
MPLCONFIGDIR=/private/tmp/continuous-divisor-mpl python3 presentations/continuous-complex-sieve/figures/static_figures.py --output-dir presentations/continuous-complex-sieve/figures/output --pdf-dir articles/arxiv/draft-continuous-divisor-sieve/figures
```

The exporter writes vector SVG/PDF and 200 dpi PNG previews. Article PDF
generation remains `just arxiv-pdf draft-continuous-divisor-sieve`, followed
by `just arxiv-parity draft-continuous-divisor-sieve`.

## Mathematical provenance

`wave` evaluates the finite exponential mean in Section 2, avoiding the
removable singularities of the sine quotient. `contribution` and `height`
implement Section 3; `pair_height` implements Section 8; the bounded product
implements Section 11. Only floating-point roundoff is clipped to the known
unit interval for waves/amplitudes. The baseline sine term is retained.

- `activated-filter-4`: bare W4 versus a4 W4 on [2,12]. This shows one
  filter contribution, not the full prime height.
- `prime-twin-contacts`: h(t) and B(t) on [2,31], using filters through 33
  to cover both endpoints, including the endpoint 33 of the final pair.
- `additive-bounded-twins`: B(t) versus 1-A(t) on [2,19], using filters
  through 21. The panels intentionally use different vertical scales.

Each integer is explicitly included in the continuous plotting grid (160
samples per unit). Markers come from exact proper-divisor counts, independent
of the floating-point curves. Pair contacts mark the start t of (t,t+2).
The completed cutoff is ceil(upper+2); higher filters vanish throughout the
plotted windows. These are illustrations of the article's proofs, not
numerical proofs over the real line or evidence for infinitely many twins.

Tests compare wave samples, finite stages, full divisor counts, pinned prime
and twin sets, shifted stability and bounded integer values. They also check
grid endpoints, renderer contact locations/layout and actual vector exports.
