"""Pure, no-I/O measurement library for the friendly/random/adversarial/
empirical trajectory comparison.

See properties/sieve-sequence/realized-filter-adversariality-score.md,
section "Three Compounding Trajectories: Running The Score Forward", for the
full derivation. Anchored at a real starting count N_0 (a measured
G_r_window from a lineage chain, see data/candidates/lineage-Q{Q}.csv),
this module projects three trajectories forward across the same sequence of
filters r_0 < r_1 < ... < r_{n-1} used by that chain:

  friendly     f=0 at every step      -- flat ceiling, N_0 unchanged
  random       f=2/r at every step    -- C_p=1/2 compounded (Mertens-type)
  adversarial  f=1 up to proved cap   -- N_0 minus the proved worst_case_A
                                          capacity, summed and floored at 0

All three are projections under a stated per-step assumption, not proofs
about the real sequence -- see the file above for the status of each. This
module does not compute the real (empirical) trajectory; that is read
directly from the lineage CSV by the CLI, unchanged.

This module is pure (no I/O); four_lines_cli.py does all I/O,
tests/test_four_lines.py exercises it against hand-derived ground truth.
"""

from __future__ import annotations

import math

from typing import List

from .window import worst_case_A


def friendly_trajectory(n0: float, num_layers: int) -> List[float]:
    """N_friendly(Q) = N_0 for every layer -- the trivial ceiling (f=0 always).

    Returns one value per layer, length num_layers, all equal to n0.
    """
    return [float(n0)] * num_layers


def random_trajectory(n0: float, rs: List[int]) -> List[float]:
    """N_random compounded across rs: N_0 * prod_{r in rs}(1 - 2/r).

    rs is the ordered sequence of filters installed from the anchor onward
    (rs[0] is the first filter installed AFTER the anchor's population was
    measured). Returns one value per layer, length len(rs), each the running
    product up to and including that layer's filter.
    """
    out = []
    n = float(n0)
    for r in rs:
        n *= (1.0 - 2.0 / r)
        out.append(n)
    return out


def log_growth_trajectory(n0: float, rs: List[int], c: float = 1.0) -> List[float]:
    """N_c compounded across rs for the log-growth relative-hazard family
    w_r = 1 + c*log(r) (draft article Property IV, section 5.2):

      N_c = N_0 * prod_{r in rs} (1 - 2*(1 + c*ln r)/r).

    c=0 reduces to random_trajectory exactly (w_r=1). c=1 is the article's
    square-window frontier: the slowest-growing relative factor whose
    square-window expectation tends to zero, the threshold this chart draws
    against the real sieve. Requires 2*(1 + c*ln r) < r for every r in rs,
    i.e. every per-filter destruction fraction stays below 1.
    """
    out = []
    n = float(n0)
    for r in rs:
        w_r = 1.0 + c * math.log(r)
        n *= (1.0 - 2.0 * w_r / r)
        out.append(n)
    return out


def adversarial_trajectory(n0: float, Q: int, rs: List[int]) -> List[float]:
    """N_adversarial compounded across rs: N_0 minus the running sum of the
    proved worst-case capacity worst_case_A(r, Q), floored at 0.

    worst_case_A(p, q) (from window.py) counts accepted multiples of p in the
    window [q, q^2); here q=Q is held fixed across all layers (the lineage
    experiment's fixed-future-window framing), so worst_case_A(r, Q) is
    exactly the proved upper bound on how many of the anchor's surviving
    2-gaps filter r can destroy in this same fixed window.
    """
    out = []
    remaining = float(n0)
    for r in rs:
        remaining = max(0.0, remaining - worst_case_A(r, Q))
        out.append(remaining)
    return out


def mixture_trajectory(n0: float, rs: List[int], score: float) -> List[float]:
    """N_s compounded across rs for an intermediate score s in [0,1], via the
    inverse of C_p(f) (realized-filter-adversariality-score.md):

      f(s,r) = 2*s*d_p                    for 0 <= s <= 1/2
      f(s,r) = d_p + (1-d_p)*(2*s-1)      for 1/2 <= s <= 1

    with d_p = 2/r. score=0.5 reproduces random_trajectory exactly;
    score=0 reproduces friendly_trajectory (f=0 at every step); score=1
    reproduces the degenerate always-f=1 case (zeroes at the first step),
    NOT adversarial_trajectory (which uses the proved capacity cap instead
    of literal f=1 -- see the module docstring).
    """
    if not (0.0 <= score <= 1.0):
        raise ValueError(f"score must be in [0,1], got {score}")
    out = []
    n = float(n0)
    for r in rs:
        d_p = 2.0 / r
        if score <= 0.5:
            f = 2.0 * score * d_p
        else:
            f = d_p + (1.0 - d_p) * (2.0 * score - 1.0)
        n *= (1.0 - f)
        out.append(n)
    return out
