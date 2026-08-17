"""Pure, no-I/O measurement library for the candidate stress-test.

This module contains the testable core. The thin runner (window_cli.py)
does all I/O; everything here is a pure function over its arguments so that
tests/test_window.py can exercise it directly.

Convention (article-authoritative, gap-dynamics.md S9)
------------------------------------------------------
For a consecutive-prime transition (p, q) with q the next prime after p:

  W = [q, q^2)            square-safe window
  primes < p              the installed filters (the current stage)
  pre-filter survivors    integers in W coprime to every prime < p
  install filter p        removes the pre-filter survivors that are 0 (mod p)
  post-filter survivors   coprime to every prime < q  (the certified-prime pool)

A 2-gap (x, x+2) among post-filter survivors in W is a genuine twin-prime
certificate, because any composite < q^2 has a prime factor < q, which would be
an installed filter and so could not be a survivor.

A 2-gap (x, x+2) of PRE-filter survivors is destroyed by installing p exactly
when x = 0 (mod p) or x+2 = 0 (mod p). This is counted directly from the
survivor list -- no probabilistic model, no assumption about the filter's
behaviour.
"""

from __future__ import annotations

from typing import List

import numpy as np
from sympy import primepi


def sieve_window(q: int, filter_primes: List[int]) -> np.ndarray:
    """Return a boolean numpy array is_surv over the half-open window [q, q^2).

    is_surv[i] is True exactly when the integer value q + i is coprime to every
    prime in filter_primes. The window has length q^2 - q.

    filter_primes must be primes strictly less than q (the installed filters of
    the stage). Values marked False are multiples of at least one filter prime.

    Uses a NumPy boolean array; each prime's multiples are marked by a strided
    slice assignment, which is both fast and hard to get wrong.
    """
    lo = q
    hi = q * q  # window is [q, q^2), so values are lo..hi-1
    size = hi - lo
    is_surv = np.ones(size, dtype=bool)
    for p in filter_primes:
        if p <= 1:
            continue
        # first multiple of p that is >= lo
        rem = lo % p
        start = 0 if rem == 0 else (p - rem)
        if start < size:
            is_surv[start::p] = False
    return is_surv


def survivors_list(q: int, filter_primes: List[int]) -> List[int]:
    """Return the sorted list of pre-filter survivors in [q, q^2)."""
    is_surv = sieve_window(q, filter_primes)
    lo = q
    # nonzero indices, offset back to absolute integer values
    idx = np.flatnonzero(is_surv)
    return (idx + lo).tolist()


def count_two_gaps(survivors: List[int]) -> int:
    """Count adjacent pairs (a, b) in the sorted survivor list with b - a == 2.

    These are the 2-gaps present in the given survivor list. With `survivors`
    being the PRE-filter list this is G_local; with the POST-filter list this is
    the surviving count.
    """
    if len(survivors) < 2:
        return 0
    arr = np.asarray(survivors, dtype=np.int64)
    diffs = arr[1:] - arr[:-1]
    return int(np.count_nonzero(diffs == 2))


def post_filter_survivors(
    pre_survivors: List[int], p: int
) -> List[int]:
    """Return the subset of pre_survivors that survive installing filter p.

    A value survives iff it is not 0 (mod p).
    """
    arr = np.asarray(pre_survivors, dtype=np.int64)
    return arr[arr % p != 0].tolist()


def actual_destroyed_two_gaps(pre_survivors: List[int], p: int) -> int:
    """Count pre-filter 2-gaps destroyed by installing filter p.

    A 2-gap (x, x+2) of pre-filter survivors is destroyed iff at least one
    endpoint is removed by p, i.e. x = 0 (mod p) or x+2 = 0 (mod p). Counted
    directly from the survivor list.

    Note: post-filter-3 the two gaps (x,x+2) and (x+2,x+4) cannot both be
    pre-filter 2-gaps (one of x,x+2,x+4 is 0 mod 3), so removing a single value
    destroys at most one 2-gap. Hence actual_destroyed == number of destroyed
    endpoints that are an endpoint of a 2-gap. We count destroyed 2-gaps
    directly by scanning adjacent pairs.
    """
    if len(pre_survivors) < 2 or p <= 0:
        return 0
    arr = np.asarray(pre_survivors, dtype=np.int64)
    left = arr[:-1]
    right = arr[1:]
    is_two_gap = (right - left) == 2
    # destroyed iff left endpoint 0 mod p OR right endpoint 0 mod p
    left_hit = (left % p) == 0
    right_hit = (right % p) == 0
    destroyed = is_two_gap & (left_hit | right_hit)
    return int(np.count_nonzero(destroyed))


def worst_case_A(p: int, q: int) -> int:
    """Worst-case bound on the number of 2-gaps filter p can destroy in W.

    This is the exact count of ACCEPTED multiples of p in [q, q^2) from
    gap-dynamics.md S9:

        K      = floor((q^2 - 1) / p)
        A(p,q) = pi(K) - pi(p - 1)

    where pi is the prime-counting function. A multiple pk in [q, q^2) was
    accepted by every old filter (every prime < p) exactly when k has no prime
    divisor below p; Bertrand gives q < 2p so K < p^2 and such a k is prime.
    Thus the accepted multipliers are exactly the primes k with p <= k <= K.

    Computed with sympy.primepi (tested). This is the worst case because one
    removed accepted value destroys at most one 2-gap (post filter 3), so the
    real destruction is at most A(p,q).
    """
    if q <= p:
        return 0
    K = (q * q - 1) // p
    if K < p:
        return 0
    return int(primepi(K) - primepi(p - 1))


def transition(p: int, q: int, primes_below_p: List[int]) -> dict:
    """Compute all per-transition measurements for (p, q).

    primes_below_p must be every prime strictly less than p (the installed
    filters of the stage headed at p).

    Returns a dict with all core and candidate-specific columns. Each candidate
    column is computed by a dedicated, unit-testable function above so that
    tests/test_window.py can exercise it directly.

    Power notes (which candidate each column tests, and how strongly) are
    documented in README.md. Two columns are NOT full candidate validations:
      - destroyed / waste_ratio test only the PER-LAYER building block of #14,
        not the multi-layer hereditary chain.
      - residue_max_dev (#12) is a small-sample measurement of a
        whole-distribution claim, hence low-power.
    """
    pre = survivors_list(q, primes_below_p)  # pre-filter survivors in W=[q,q^2)
    post = post_filter_survivors(pre, p)     # after installing filter p

    g_local = count_two_gaps(pre)
    surviving = count_two_gaps(post)
    a_worst = worst_case_A(p, q)
    destroyed = actual_destroyed_two_gaps(pre, p)

    surplus = g_local - a_worst
    waste_ratio = (a_worst - destroyed) / a_worst if a_worst > 0 else float("nan")

    return {
        "p": p,
        "q": q,
        "window_len": q * q - q,
        # core
        "G_local": g_local,
        "A_worst": a_worst,
        "surplus": surplus,
        "destroyed": destroyed,
        "surviving": surviving,
        "waste_ratio": waste_ratio,
        # candidate-specific (see README for power notes)
        "max_cluster_in_width_p": max_cluster_in_width_p(pre, p),       # #3
        "max_cons_destroyed_run": max_cons_destroyed_run(pre, p),       # #4
        "d_head": head_to_first_start(post, q),                        # #8
        "E_q": discrepancy_E(pre, p, q, g_local),                      # #10
        "main_term": discrepancy_main_term(p, q),                      # #10
        "destruction_rate": destroyed / g_local if g_local > 0 else float("nan"),  # #11
        "gap_2_over_p": 2.0 / p,                                        # #11
        "residue_max_dev": residue_balance_max_dev(pre, p),            # #12 (low power)
        "endpoint_bias": endpoint_bias_of_hit_set(pre, p),             # #13
    }


# ---------------------------------------------------------------------------
# Candidate-specific measurements (#3, #4, #8, #10, #12, #13)
# ---------------------------------------------------------------------------
# #11 (random-like) is already covered by destruction_rate / gap_2_over_p above.


def _two_gap_starts(survivors: List[int]) -> np.ndarray:
    """Left endpoints x of 2-gaps (x, x+2) in the sorted survivor list."""
    if len(survivors) < 2:
        return np.empty(0, dtype=np.int64)
    arr = np.asarray(survivors, dtype=np.int64)
    starts = arr[:-1][(arr[1:] - arr[:-1]) == 2]
    return starts


def max_cluster_in_width_p(survivors: List[int], p: int) -> int:
    """#3 Protected-cluster: largest set of 2-gap starts within a window < p wide.

    Returns the maximum number of 2-gap starts contained in any half-open
    interval of length < p. Post-filter-3, distinct 2-gaps are endpoint-
    disjoint, so >= 2 such starts in a width-<p window means at most one filter
    hit (two multiples of p are >= p apart) can land among them, so at least one
    survives. (For p >= 5 only; the pre-filter at p == 3 is not yet endpoint-
    disjoint, so this column is meaningful only for p >= 5.)
    """
    starts = _two_gap_starts(survivors)
    n = len(starts)
    if n == 0:
        return 0
    # sliding window: for each left index i, find the largest j>i with
    # starts[j] - starts[i] < p. Linear scan.
    best = 1
    j = 0
    for i in range(n):
        if j < i:
            j = i
        while j + 1 < n and int(starts[j + 1]) - int(starts[i]) < p:
            j += 1
        best = max(best, j - i + 1)
    return best


def max_cons_destroyed_run(survivors: List[int], p: int) -> int:
    """#4 Bounded-consecutive-destruction: longest run of consecutively-
    destroyed 2-gap starts, in the cyclic order of 2-gap starts.

    A 2-gap start x is 'destroyed' iff x = 0 (mod p) or x+2 = 0 (mod p). We scan
    the ordered list of 2-gap starts and return the longest consecutive run of
    destroyed ones. The candidate needs this to be bounded.
    """
    starts = _two_gap_starts(survivors)
    n = len(starts)
    if n == 0:
        return 0
    destroyed_mask = ((starts % p) == 0) | (((starts + 2) % p) == 0)
    # longest run of True in the linear order (cyclic wrap not measured: the
    # window is absolute, not cyclic, so a linear run is the right notion here)
    best = run = 0
    for d in destroyed_mask:
        if d:
            run += 1
            best = max(best, run)
        else:
            run = 0
    return int(best)


def head_to_first_start(post_survivors: List[int], q: int) -> int:
    """#8 Distinguished-head-spacer: forward distance from head q to the first
    post-filter 2-gap start s >= q. The candidate needs d_head <= q^2 - q - 3.

    Returns q^2 - q (window length, i.e. "no such start in W") if none exists.
    """
    starts = _two_gap_starts(post_survivors)
    if len(starts) == 0:
        return q * q - q  # sentinel: no start in window
    starts = np.asarray(starts, dtype=np.int64)
    ge_q = starts[starts >= q]
    if len(ge_q) == 0:
        return q * q - q
    return int(ge_q[0]) - q


def discrepancy_main_term(p: int, q: int) -> float:
    """#10 main term: |W| * delta_q, the expected count under complete-period
    density. delta_q = (1/2) * prod_{3<=r<q prime} (1 - 2/r).
    """
    from sympy import primerange
    dens = 0.5
    for r in primerange(3, q):
        dens *= (1.0 - 2.0 / r)
    return (q * q - q) * dens


def discrepancy_E(
    pre_survivors: List[int], p: int, q: int, g_local: int
) -> float:
    """#10 discrepancy: E_q = observed_count - main_term.

    observed_count here is G_local (pre-filter 2-gaps in W); the candidate
    statement is about the post-filter count but the pre-filter count is the
    quantity a window sieve directly yields. The README notes this convention.
    Positivity of (observed - main_term) above -main_term is the candidate.
    """
    return float(g_local) - discrepancy_main_term(p, q)


def residue_balance_max_dev(survivors: List[int], p: int) -> float:
    """#12 Local-pattern-residue-balance (LOW POWER): for the word w=(2),
    N_{w,a} = number of 2-gap starts congruent to a mod p; returns
    max_a |N_{w,a} - N_w/p|. The candidate wants this small. One window is a
    small sample of the whole residue distribution, so this is a weak test.
    """
    starts = _two_gap_starts(survivors)
    n = len(starts)
    if n == 0 or p <= 0:
        return 0.0
    classes = starts % p
    counts = np.bincount(classes.astype(np.int64), minlength=p)
    expected = n / p
    return float(np.max(np.abs(counts.astype(float) - expected)))


def endpoint_bias_of_hit_set(survivors: List[int], p: int) -> float:
    """#13 Uniform-local-observable-sampling: endpoint bias of the filter hit set.

    Let V = the pre-filter survivors (anchors), D = the subset removed by p
    (the hit set, |D| = H), and c(v) = 1 iff v is an endpoint of a 2-gap, else
    0. Then endpoint bias = |(1/H) sum_D c(v) - (1/N) sum_V c(v)|. The candidate
    wants this <= eta_p small. Post-filter-3 (p>=5) 2-gaps are endpoint-
    disjoint, so sum_V c(v) = 2 * G_local.
    """
    surv = np.asarray(survivors, dtype=np.int64)
    n = len(surv)
    if n == 0:
        return 0.0
    hits = surv[surv % p == 0]
    h = len(hits)
    # c(v): v is an endpoint of a 2-gap iff v-2 or v+2 is also a survivor.
    surv_set = set(int(v) for v in surv)
    def c(v: int) -> int:
        return 1 if ((v - 2) in surv_set) or ((v + 2) in surv_set) else 0
    c_all = sum(c(int(v)) for v in surv)
    c_hit = sum(c(int(v)) for v in hits)
    mean_all = c_all / n
    mean_hit = c_hit / h if h > 0 else 0.0
    return abs(mean_hit - mean_all)
