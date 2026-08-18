"""Pure, no-I/O fixed-cohort hazard measurement library.

Tracks ONE initial population of 2-gap starts in the fixed window W_Q = [Q, Q^2)
through every prime filter r < Q. At each layer, marks a cohort member as
destroyed exactly when either endpoint is divisible by r, then removes it from
the active cohort.

This module is pure (no I/O); a future CLI and chart generator will use it.
"""

from __future__ import annotations

import math
from typing import List, Tuple

from sympy import primerange


def init_fixed_cohort(Q: int) -> List[int]:
    """All 2-gap starts in W_Q = [Q, Q^2) after filter 2 is installed.

    After filter 2, the accepted set is all odd integers in [Q, Q^2).
    2-gap starts are odd x such that x+2 < Q^2 (so x+2 is also in the window).
    """
    lo = Q
    hi = Q * Q
    # odd numbers in [lo, hi): start at first odd >= lo
    start = lo if (lo % 2 == 1) else lo + 1
    # all odd x where x+2 < hi -> x < hi-2 -> x <= hi-3 (if hi-3 is odd)
    stop = hi - 2
    return list(range(start, stop, 2))


def apply_cohort_filter(
    cohort: List[int], r: int
) -> Tuple[List[int], List[int]]:
    """Filter the active cohort by prime r.

    A 2-gap start x is destroyed iff x % r == 0 or (x+2) % r == 0.
    Returns (destroyed, survivors) as sorted lists.
    """
    destroyed = []
    survivors = []
    for x in cohort:
        if (x % r == 0) or ((x + 2) % r == 0):
            destroyed.append(x)
        else:
            survivors.append(x)
    return destroyed, survivors


def layer_hazard_row(
    cohort_before: List[int], r: int, L_initial: int
) -> dict:
    """One row of the per-layer hazard measurement for filter r.

    cohort_before: active 2-gap starts before installing r.
    r: the incoming prime filter (r >= 3).
    L_initial: the size of the original cohort at filter 2.

    Returns a dict with:
      L_before, destroyed, L_after,
      f_real, f_random, w_real,
      h_real, h_random
    """
    L_before = len(cohort_before)
    destroyed, survivors = apply_cohort_filter(cohort_before, r)
    L_after = len(survivors)
    K = len(destroyed)

    f_real = K / L_before if L_before > 0 else 0.0
    f_random = 2.0 / r
    w_real = f_real / f_random if f_random > 0 else float("inf")

    h_real = -math.log(L_after / L_before) if L_after > 0 and L_before > 0 else float("inf")
    h_random = -math.log(1.0 - 2.0 / r)

    return {
        "r": r,
        "L_before": L_before,
        "destroyed": K,
        "L_after": L_after,
        "f_real": f_real,
        "f_random": f_random,
        "w_real": w_real,
        "h_real": h_real,
        "h_random": h_random,
    }


def build_hazard_run(Q: int) -> list:
    """Chain explicit cohort through all filters r < Q, accumulating hazard.

    Returns a list of dicts, one per layer (r >= 3), each containing all
    per-layer fields from layer_hazard_row plus cumulative fields:
      D_real, D_random, excess_hazard, c_eff,
      survival_real, survival_random.

    Stops early if the cohort goes extinct.
    """
    from sympy import primerange

    all_primes = list(primerange(2, Q))
    cohort = init_fixed_cohort(Q)
    L_initial = len(cohort)

    D_real = 0.0
    D_random = 0.0
    rows = []

    for r in all_primes[1:]:  # skip r=2 (already applied in init)
        row = layer_hazard_row(cohort, r, L_initial)

        D_real += row["h_real"]
        D_random += row["h_random"]

        excess = D_real - D_random
        c_eff = excess / (2.0 * math.log(r)) if r >= 3 and D_real != float("inf") else float("inf")
        surv_real = row["L_after"] / L_initial
        surv_random = math.exp(-D_random)

        row["D_real"] = D_real
        row["D_random"] = D_random
        row["excess_hazard"] = excess
        row["c_eff"] = c_eff
        row["survival_real"] = surv_real
        row["survival_random"] = surv_random

        rows.append(row)

        if row["L_after"] == 0:
            break
        cohort = apply_cohort_filter(cohort, r)[1]

    return rows
