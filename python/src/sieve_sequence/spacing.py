"""Pure, no-I/O measurement library for the implied-spacing view of the
four trajectories in four_lines.py.

A raw survivor *count* trending toward zero reads, visually, as extinction --
even when the underlying process never actually stops (see
properties/sieve-sequence/realized-filter-adversariality-score.md, the
"N_random here is not the same model" note). The implied *spacing* between
consecutive 2-gaps is the reciprocal of that same information, and reads
correctly: it grows (2-gaps get rarer) but stays finite for as long as the
process keeps producing them. Only a genuine extinction -- the count hitting
exactly zero -- shows up here, as an actual infinity, not an optical illusion
from a shrinking count.

This module does not introduce a new model. It is a reciprocal-scaling
transform of the four_lines.py trajectories, anchored so it agrees exactly
with the direct density computation for the random trajectory (verified in
tests/test_spacing.py) -- see "Why This Is Not A New Model" below.

This module is pure (no I/O); spacing_cli.py does all I/O,
tests/test_spacing.py exercises it against hand-derived ground truth.
"""

from __future__ import annotations

from typing import List

from sympy import primerange


def density_at(Q_r: int) -> float:
    """Exact complete-period density of post-filter 2-gap starts once every
    prime up to and including Q_r is installed:

      delta(Q_r) = (1/2) * prod_{3<=s<=Q_r, s prime} (1 - 2/s).

    This is the same delta_q used in
    candidates/short-window-discrepancy.md and window.discrepancy_main_term,
    computed independently here (self-contained, matching this codebase's
    existing convention of a small local density loop per module rather than
    a shared cross-module helper -- see window.py's discrepancy_main_term and
    lineage.py's post_filter_E_q, which each already do the same).

    The one difference from those two: this includes Q_r itself in the
    product (primerange(3, Q_r + 1)), because it answers "density right
    after this layer's filter installed," matching what N_X(layer) already
    means in the four-lines CSV. The other two answer "density strictly
    before installing q," which is what their own call sites need.
    """
    dens = 0.5
    for s in primerange(3, Q_r + 1):
        dens *= (1.0 - 2.0 / s)
    return dens


def implied_spacing(n0: float, counts: List[float], ref_spacing: float) -> List[float]:
    """Convert a trajectory of survivor counts into implied average spacing
    between consecutive 2-gaps.

    spacing(Q) = ref_spacing * n0 / count(Q)

    ref_spacing is the real spacing (1/density) at the anchor point; n0 is
    the anchor's own count. Scaling by n0/count(Q) is exactly the reciprocal
    of the trajectory's own shrink factor, so this never needs to know
    *which* trajectory it is -- friendly, random, adversarial, or empirical
    all use the identical transform.

    Returns float('inf') exactly where count is 0: a genuine extinction
    point, not a numerical artifact. Raises ValueError on a negative count
    (not a valid trajectory value).
    """
    if n0 <= 0:
        raise ValueError(f"n0 must be positive, got {n0}")
    if ref_spacing <= 0:
        raise ValueError(f"ref_spacing must be positive, got {ref_spacing}")
    out = []
    for c in counts:
        if c < 0:
            raise ValueError(f"count must be non-negative, got {c}")
        if c == 0:
            out.append(float("inf"))
        else:
            out.append(ref_spacing * n0 / c)
    return out


# ---------------------------------------------------------------------------
# Why This Is Not A New Model
# ---------------------------------------------------------------------------
#
# For the random trajectory specifically, this transform is provably
# identical to computing 1/density_at(Q) directly, not just a plausible
# rescaling. Sketch (verified numerically in tests/test_spacing.py):
#
#   N_random(Q) = n0 * prod_{anchor<r<=Q} (1 - 2/r)     [four_lines.py]
#   density_at(Q) = density_at(anchor) * prod_{anchor<r<=Q} (1 - 2/r)
#
# so N_random(Q)/n0 = density_at(Q)/density_at(anchor), hence
#
#   implied_spacing(n0, N_random(Q), 1/density_at(anchor))
#     = (1/density_at(anchor)) * n0 / N_random(Q)
#     = (1/density_at(anchor)) * density_at(anchor)/density_at(Q)
#     = 1/density_at(Q).
#
# The friendly and adversarial spacings inherit their meaning from the same
# transform applied to counts that are themselves already fully specified
# (and, for adversarial, already proved) in four_lines.py -- this module
# adds no new assumption beyond what building those counts already required.
