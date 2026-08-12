"""Pure, no-I/O measurement library for the lineage experiment.

Fixes a future square window W_Q = [Q, Q^2). Tracks the 2-gap population of W_Q
through every intermediate prime filter r < Q, one layer at a time. At each
layer measures the ACTUAL STATED CONDITION of candidates #4, #10, #12, #13, #14
(correcting the proxies the single-transition window pass used).

Design decisions (see tickets/active/lineage-experiment-2026-07-23.md):
  - Reading A: each layer's population is the actual accepted set of the stage
    (integers in [Q,Q^2) coprime to all primes < r), updated as filters install.
  - sigma_r(k) is defined from the whole-period gap cycle. For 2 <= k <= 10
    once {2,3,5,7} are installed, the proved exact stable table avoids
    materializing M_r; earlier stages enumerate their small periods exactly.
    Full-period diagnostics such as T_r, sigma_r_T, and the cyclic destroyed
    run remain gated by M_r.
  - #4 cyclic destroyed run is over the FULL PERIOD M_r (per the candidate
    note "Order the pre-filter 2-gap starts cyclically"), computed exactly at
    the pilot. The window-linear run is also reported for comparison.

This module is pure (no I/O); lineage_cli.py does all I/O,
tests/test_lineage.py exercises it against hand-derived ground truth.
"""

from __future__ import annotations

from typing import List, Tuple

import numpy as np
from sympy import primepi


# ---------------------------------------------------------------------------
# Window population (Reading A: actual accepted set of the current stage)
# ---------------------------------------------------------------------------

def window_survivors(Q: int, primes_below_r: List[int]) -> List[int]:
    """Accepted values of the stage in the fixed window [Q, Q^2).

    These are integers v in [Q, Q^2) coprime to every prime in primes_below_r
    (the primes installed so far, i.e. all primes < the current layer's head r).
    As filters install, primes_below_r grows and this set shrinks -- that is
    Reading A (the actual accepted set per layer), not a frozen population.
    """
    lo = Q
    hi = Q * Q
    size = hi - lo
    is_ok = np.ones(size, dtype=bool)
    for p in primes_below_r:
        if p <= 1:
            continue
        rem = lo % p
        start = 0 if rem == 0 else (p - rem)
        if start < size:
            is_ok[start::p] = False
    idx = np.flatnonzero(is_ok)
    return (idx + lo).tolist()


def two_gap_starts(survivors: List[int]) -> np.ndarray:
    """Left endpoints x of 2-gaps (x, x+2) in the sorted survivor list."""
    if len(survivors) < 2:
        return np.empty(0, dtype=np.int64)
    arr = np.asarray(survivors, dtype=np.int64)
    return arr[:-1][(arr[1:] - arr[:-1]) == 2]


# ---------------------------------------------------------------------------
# #14 sigma_r(k): min span of k consecutive shots (WHOLE PERIOD, exact)
# ---------------------------------------------------------------------------
# Per hereditary-shot-spacing-capacity.md lines 17-80:
#   - accepted cofactor residues 0<=e_0<...<e_{T_r-1}<M_r (one full period)
#   - cyclic cofactor gaps g_i (with wrap g_{T-1} = M_r + e_0 - e_{T-1})
#   - shots h = r*(e_i + n*M_r); consecutive shot gaps Delta_i = r*g_i
#   - sigma_r(k) = min over i of sum_{t=0..k-2} Delta_{i+t}  (periodic indices)
#     = r * min over i of (sum of k-1 consecutive cyclic cofactor gaps)
# This requires the FULL PERIOD M_r. Feasible only while M_r is small.


def full_period_cofactor_gaps(primes_below_r: List[int]) -> Tuple[List[int], int]:
    """Return (cyclic cofactor gaps g, modulus M_r) for the full period of the
    stage whose installed filters are primes_below_r.

    M_r = product of primes_below_r. The cofactor residues are the integers in
    [0, M_r) coprime to every prime in primes_below_r; g_i are their cyclic
    adjacent differences (g_{T-1} wraps via M_r).

    GATED: materializing the size-M array is only feasible for small M. Raises
    ValueError for M > 5e7. Callers that only need sigma_r for small k should
    use sigma_r_for_layer (which uses the stable table and never calls this for
    large M). This function is for diagnostics (T_r, sigma_r_T) at small M only.
    """
    M = 1
    for p in primes_below_r:
        M *= p
    if M > 50_000_000:
        raise ValueError(f"M={M} too large to materialize; use sigma_r_for_layer for small k")
    # cofactor residues in [0, M): values coprime to every filter prime.
    # NOTE: must mark index 0 too (0 is divisible by every prime). is_ok[p::p]
    # starts at index p and skips 0; use is_ok[0::p] (= is_ok[::p]) instead.
    is_ok = np.ones(M, dtype=bool)
    for p in primes_below_r:
        is_ok[0::p] = False
    residues = np.flatnonzero(is_ok).tolist()  # e_0 < e_1 < ... < e_{T-1}
    T = len(residues)
    if T == 0:
        return [], M
    gaps = []
    for i in range(T - 1):
        gaps.append(int(residues[i + 1] - residues[i]))
    gaps.append(int(M + residues[0] - residues[T - 1]))  # wrap
    return gaps, M


def sigma_r_for_layer(
    k: int, r: int, primes_strictly_below_r: List[int]
) -> Tuple[int, int]:
    """sigma_r(k) for incoming filter r, given the stage before installing r.

    primes_strictly_below_r = all primes < r (the installed filters of the
    stage whose cofactor gaps we use). The shot multiplier is r.

    Returns (sigma_r(k), M) where M is the period modulus before installing r.

    Two paths:
      - If {2,3,5,7} are all installed, use the PROVEN STABLE small-k values
        (see sigma_r_stable). These are exact, O(1), and independent of M -- so
        there is no primorial wall for the small k that #14's interval premise
        needs. The proof is not finite wheel agreement: the exact {2,3,5,7}
        wheel realizes D(k), filtering monotonicity makes the minimum span
        non-decreasing, and an admissible pattern of diameter D(k), translated
        by CRT, supplies the matching upper bound for every larger wheel. Finite
        later-wheel comparisons are regression evidence only.
      - Otherwise (an early stage missing one of {2,3,5,7}), compute exactly
        from the full period, which is small at those early stages.
    """
    if {2, 3, 5, 7}.issubset(set(primes_strictly_below_r)):
        stable = sigma_r_stable(k)
        if stable is not None:
            M = 1
            for p in primes_strictly_below_r:
                M *= p
            return r * stable, M
    # early stage: exact from full period (small M here)
    gaps, M = full_period_cofactor_gaps(primes_strictly_below_r)
    T = len(gaps)
    if T == 0:
        raise ValueError("no cofactor residues")
    if not (2 <= k <= T):
        raise ValueError(f"k={k} out of range [2, {T}]")
    g = np.asarray(gaps, dtype=np.int64)
    doubled = np.concatenate([g, g])
    win = k - 1
    csum = np.concatenate([[0], np.cumsum(doubled)])
    window_sums = csum[win:win + T] - csum[:T]
    min_span_cofactor = int(window_sums.min())
    return r * min_span_cofactor, M


# Exact stable values of sigma_r(k)/r for 2 <= k <= 10. The {2,3,5,7}
# wheel realizes D(k). Filtering monotonicity preserves D(k) as a lower bound,
# while an admissible pattern of diameter D(k), translated by CRT, gives the
# matching upper bound for every larger primorial wheel. Equality observed in
# later finite wheels is regression evidence for the implementation, not the
# proof. Do not extrapolate beyond the proved table.
_SIGMA_STABLE = {2: 2, 3: 6, 4: 8, 5: 12, 6: 16, 7: 20, 8: 26, 9: 30, 10: 32}


def sigma_r_stable(k: int):
    """The exact stable sigma_r(k)/r for 2 <= k <= 10 once {2,3,5,7} are
    installed, or None beyond the proved table. Exactness follows from D(k):
    filtering supplies the lower bound and an admissible-pattern CRT witness
    supplies the matching upper bound. Finite later-wheel comparisons are
    regression evidence only."""
    return _SIGMA_STABLE.get(k)


# ---------------------------------------------------------------------------
# #4 cyclic destroyed run (over the FULL PERIOD M_r) and window-linear run
# ---------------------------------------------------------------------------

def cyclic_destroyed_run_full_period(
    r: int, primes_strictly_below_r: List[int]
) -> Tuple[int, int]:
    """#4 as stated: longest cyclic run of consecutively-destroyed 2-gap starts,
    over the FULL PERIOD ordering of 2-gap starts of the stage before r.

    A 2-gap start x (in the full period [0, M_r)) is destroyed by r iff
    x = 0 mod r or x+2 = 0 mod r. We order the full-period 2-gap starts
    cyclically and return the longest run of destroyed ones (wrapping).

    Returns (longest_cyclic_run, M). Respects the frontier (M <= 5e7).
    """
    M = 1
    for p in primes_strictly_below_r:
        M *= p
    if M > 50_000_000:
        raise ValueError(f"M={M} too large; respect frontier")
    is_ok = np.ones(M, dtype=bool)
    for p in primes_strictly_below_r:
        is_ok[0::p] = False  # mark index 0 too (0 divisible by every prime)
    residues = np.flatnonzero(is_ok)  # e_i, full period
    # full-period 2-gap starts: x where x and x+2 are both residues (mod M)
    rset = set(int(x) for x in residues)
    starts = np.array(
        sorted(x for x in residues if ((int(x) + 2) % M) in rset),
        dtype=np.int64,
    )
    n = len(starts)
    if n == 0:
        return 0, M
    destroyed = ((starts % r) == 0) | (((starts + 2) % r) == 0)
    # cyclic longest run of True
    if destroyed.all():
        return n, M
    # break into runs; handle wrap by concatenating and splitting on any False
    best = run = 0
    # iterate twice to handle wrap (start in a non-destroyed region)
    first_false = next((i for i in range(n) if not destroyed[i]), None)
    if first_false is None:
        return n, M
    order = np.roll(destroyed, -first_false)  # start at a False
    for d in order:
        if d:
            run += 1
            best = max(best, run)
        else:
            run = 0
    return best, M


def window_linear_destroyed_run(
    window_starts: np.ndarray, r: int
) -> int:
    """The window-linear run (what the single-transition pass measured).
    Reported alongside the cyclic one for comparison, NOT as the candidate."""
    n = len(window_starts)
    if n == 0:
        return 0
    destroyed = ((window_starts % r) == 0) | (((window_starts + 2) % r) == 0)
    best = run = 0
    for d in destroyed:
        if d:
            run += 1
            best = max(best, run)
        else:
            run = 0
    return int(best)


# ---------------------------------------------------------------------------
# #10 post-filter discrepancy (correcting the pre/post error)
# ---------------------------------------------------------------------------

def post_filter_E_q(
    post_survivors: List[int], primes_strictly_below_q: List[int], q: int
) -> Tuple[float, float]:
    """#10 as stated: E_q = |S_q ∩ W_q| - main_term, using the POST-filter count.

    |S_q ∩ W_q| = number of 2-gaps among post-filter survivors in [Q,Q^2).
    main_term = |W_q| * delta_q, delta_q = (1/2) prod_{3<=r<Q prime}(1 - 2/r).
    Returns (E_q, main_term).
    """
    from sympy import primerange
    starts = two_gap_starts(post_survivors)
    post_count = len(starts)
    dens = 0.5
    for rp in primerange(3, q):
        dens *= (1.0 - 2.0 / rp)
    main = (q * q - q) * dens
    return float(post_count) - main, main


# ---------------------------------------------------------------------------
# #12 margin (candidate's own condition) and #13 one-sided margin
# ---------------------------------------------------------------------------

def candidate_12_margin(
    window_starts: np.ndarray, r: int
) -> Tuple[float, float, float, int]:
    """#12 as stated: the candidate's sufficient condition is
        nu * E  <  N * (1 - nu/p)
    where N = |window 2-gap starts|, nu = number of DISTINCT forbidden start
    residue classes mod r (for the word (2): {0, -2}, so nu=2 when r does not
    divide 2), and E is the max residue-class excess (the 'E_p(J,w)' of the note;
    here approximated by the worst-class deviation, which is an upper bound on
    the harmful excess).

    Returns (lhs = nu*E, rhs = N*(1 - nu/r), margin = rhs - lhs, N).
    A positive margin means the sufficient condition holds.
    """
    N = len(window_starts)
    if N == 0 or r <= 0:
        return 0.0, 0.0, 0.0, 0
    nu = 2 if (r % 2 != 0) else 1  # word (2): forbidden classes 0 and -2
    classes = window_starts % r
    counts = np.bincount(classes.astype(np.int64), minlength=r)
    expected = N / r
    E = float(np.max(np.abs(counts.astype(float) - expected)))  # max deviation
    lhs = nu * E
    rhs = N * (1 - nu / r)
    return lhs, rhs, rhs - lhs, N


def candidate_13_one_sided_margin(
    pre_survivors: List[int], r: int
) -> Tuple[float, float, float, int, int, int]:
    """#13 as stated: the sufficient condition is
        H * (2L/N + b_+) < L
    where V = pre-survivors (anchors, |V|=N), D = filter hits (|D|=H),
    L = complete 2-gaps with both endpoints in V, c(v)=1 iff v is a 2-gap
    endpoint, and b_+ = max(0, mean_hit - mean_all) is the HARMFUL one-sided
    bias (a large negative signed bias is harmless).

    Returns (lhs = H*(2L/N + b_+), rhs = L, margin = rhs - lhs, H, N, L).
    Positive margin means the sufficient condition holds.
    """
    surv = np.asarray(pre_survivors, dtype=np.int64)
    N = len(surv)
    if N == 0:
        return 0.0, 0.0, 0.0, 0, 0, 0
    hits = surv[surv % r == 0]
    H = len(hits)
    starts = two_gap_starts(pre_survivors)
    L = len(starts)  # complete 2-gaps with both endpoints in V
    surv_set = set(int(v) for v in surv)
    def c(v: int) -> int:
        return 1 if ((v - 2) in surv_set) or ((v + 2) in surv_set) else 0
    mean_all = sum(c(int(v)) for v in surv) / N
    mean_hit = (sum(c(int(v)) for v in hits) / H) if H > 0 else 0.0
    b_plus = max(0.0, mean_hit - mean_all)
    lhs = H * (2 * L / N + b_plus)
    rhs = float(L)
    return lhs, rhs, rhs - lhs, H, N, L


# ---------------------------------------------------------------------------
# Per-layer summary
# ---------------------------------------------------------------------------

def layer(
    Q: int, r: int, primes_strictly_below_r: List[int]
) -> dict:
    """All per-layer measurements for installing filter r on the fixed window
    W_Q = [Q, Q^2), given the stage before r (filters = primes_strictly_below_r).

    Population is Reading A: survivors in [Q,Q^2) coprime to primes_strictly_below_r.
    """
    pre = window_survivors(Q, primes_strictly_below_r)   # accepted set before r
    # after installing r: coprime to primes_strictly_below_r AND to r
    post = [v for v in pre if v % r != 0]
    pre_starts = two_gap_starts(pre)
    post_starts = two_gap_starts(post)
    G_r = len(pre_starts)
    surviving = len(post_starts)
    destroyed_mask = ((pre_starts % r) == 0) | (((pre_starts + 2) % r) == 0)
    destroyed = int(np.count_nonzero(destroyed_mask))

    out = {
        "Q": Q, "r": r, "layer_head": r,
        "n_filters_before": len(primes_strictly_below_r),
        "G_r_window": G_r,
        "destroyed": destroyed,
        "surviving": surviving,
    }
    # sigma_r for small k: load-bearing for #14, uses the STABLE TABLE once
    # {2,3,5,7} are installed -> O(1), no M-array, no wall. Always available.
    try:
        out["sigma_r_2"], _ = sigma_r_for_layer(2, r, primes_strictly_below_r)
    except ValueError:
        out["sigma_r_2"] = None

    # Diagnostics that genuinely need the full period (cyclic run, T_r, sigma_r_T):
    # gated to small M. At large M these are None -- reported as unmeasured, not
    # proxied. sigma_r_2 above is NOT affected (stable table).
    out["cyclic_run_full_period"] = None
    out["M_r"] = None
    out["T_r"] = None
    out["sigma_r_T"] = None
    try:
        gaps, M = full_period_cofactor_gaps(primes_strictly_below_r)
        out["M_r"] = M
        out["T_r"] = len(gaps)
        out["sigma_r_T"], _ = sigma_r_for_layer(len(gaps), r, primes_strictly_below_r)
        cyc_run, _ = cyclic_destroyed_run_full_period(r, primes_strictly_below_r)
        out["cyclic_run_full_period"] = cyc_run
    except ValueError:
        pass  # large M: diagnostics stay None, sigma_r_2 still valid via stable table
    out["window_linear_run"] = window_linear_destroyed_run(pre_starts, r)

    # #10 post-filter discrepancy (post = after this layer's filter r; uses q=Q)
    E, main = post_filter_E_q(post, primes_strictly_below_r + [r], Q)
    out["post_E_q"] = E
    out["post_main_term"] = main

    # #12 and #13 margins
    lhs12, rhs12, margin12, N12 = candidate_12_margin(pre_starts, r)
    out["c12_lhs"] = lhs12
    out["c12_rhs"] = rhs12
    out["c12_margin"] = margin12
    lhs13, rhs13, margin13, H13, N13, L13 = candidate_13_one_sided_margin(pre, r)
    out["c13_lhs"] = lhs13
    out["c13_rhs"] = rhs13
    out["c13_margin"] = margin13
    out["c13_H"] = H13
    out["c13_N"] = N13
    out["c13_L"] = L13
    return out
