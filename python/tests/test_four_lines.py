"""Green-gate test suite for the four_lines (friendly/random/adversarial/
mixture trajectory) library.

Run:  pytest python/tests/test_four_lines.py

Ground truth for random_trajectory and mixture_trajectory is
hand-computed rational arithmetic (no prime-counting needed). Ground truth
for adversarial_trajectory cross-checks against window.worst_case_A directly
(already an established, tested primitive) -- this suite tests the new
compounding/orchestration logic, not worst_case_A's own correctness.
"""

import math

from sieve_sequence import four_lines as lib
from sieve_sequence.window import worst_case_A


def close(a, b, tol=1e-9):
    return abs(a - b) <= tol


# ---------------------------------------------------------------------------
# friendly_trajectory
# ---------------------------------------------------------------------------

def test_friendly():
    print("test_friendly")
    out = lib.friendly_trajectory(395, 5)
    assert len(out) == 5, f"friendly length==5: len={len(out)}"
    assert all(v == 395.0 for v in out), f"friendly all equal n0: out={out}"


# ---------------------------------------------------------------------------
# random_trajectory: hand-computed exact compounding
# ---------------------------------------------------------------------------

def test_random_hand_derived():
    print("test_random_hand_derived")
    # n0=100, rs=[5,7]:
    #   after r=5: 100*(1-2/5) = 100*0.6 = 60
    #   after r=7: 60*(1-2/7)  = 60*(5/7) = 300/7
    out = lib.random_trajectory(100.0, [5, 7])
    assert close(out[0], 60.0), f"random layer0 == 60: got {out[0]}"
    assert close(out[1], 300.0 / 7.0), f"random layer1 == 300/7: got {out[1]}"
    assert len(out) == 2, f"random length==2: len={len(out)}"


def test_random_monotone_decreasing():
    print("test_random_monotone_decreasing")
    out = lib.random_trajectory(5049.0, [3, 5, 7, 11, 13])
    # each factor (1-2/r) is in (0,1) for r>2, so the sequence strictly
    # decreases and always stays positive.
    assert all(
        out[i] < out[i - 1] for i in range(1, len(out))
    ), f"random strictly decreasing: out={out}"
    assert all(v > 0 for v in out), f"random stays positive: out={out}"


# ---------------------------------------------------------------------------
# log_growth_trajectory: the c=1 frontier projection
# ---------------------------------------------------------------------------

def test_log_growth_c_zero_matches_random():
    print("test_log_growth_c_zero_matches_random")
    # c=0 means w_r = 1 exactly, so the log-growth trajectory must reproduce
    # random_trajectory term for term.
    n0, rs = 5049.0, [3, 5, 7, 11, 13]
    a = lib.log_growth_trajectory(n0, rs, c=0.0)
    b = lib.random_trajectory(n0, rs)
    assert all(
        close(x, y) for x, y in zip(a, b)
    ), f"c=0 == random_trajectory: c0={a} random={b}"


def test_log_growth_frontier_hand_derived():
    print("test_log_growth_frontier_hand_derived")
    # n0=100, rs=[29]: factor = 1 - 2*(1 + ln 29)/29, computed with the same
    # natural log the model uses.
    n0, r = 100.0, 29
    factor = 1.0 - 2.0 * (1.0 + math.log(r)) / r
    out = lib.log_growth_trajectory(n0, [r])
    assert close(out[0], n0 * factor), f"frontier single layer: got {out[0]}"
    # two layers, running product:
    rs = [29, 31]
    out2 = lib.log_growth_trajectory(n0, rs)
    expected = n0 * factor * (1.0 - 2.0 * (1.0 + math.log(31)) / 31)
    assert close(out2[1], expected), f"frontier running product: got {out2[1]}"


def test_log_growth_frontier_below_random_stays_positive():
    print("test_log_growth_frontier_below_random_stays_positive")
    # On the real Q=101 chain (anchored layer 7, future filters r=29..97), the
    # c=1 frontier must sit strictly below the random projection and stay
    # positive the whole way (f_r < 1 at every r).
    Q = 101
    rs = [29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    n0 = 361.0
    frontier = lib.log_growth_trajectory(n0, rs)
    random_ = lib.random_trajectory(n0, rs)
    assert all(
        frontier[i] < random_[i] for i in range(len(frontier))
    ), f"frontier strictly below random: frontier={frontier} random={random_}"
    assert all(v > 0 for v in frontier), f"frontier stays positive: frontier={frontier}"
    # every per-filter destruction fraction stays below 1:
    assert all(
        (2.0 * (1.0 + math.log(r)) / r) < 1.0 for r in rs
    ), "frontier f_r < 1 at every r"


# ---------------------------------------------------------------------------
# adversarial_trajectory: cross-check against worst_case_A directly
# ---------------------------------------------------------------------------

def test_adversarial_matches_worst_case_A():
    print("test_adversarial_matches_worst_case_A")
    Q = 101
    rs = [3, 5, 7, 11]
    n0 = 5049.0
    out = lib.adversarial_trajectory(n0, Q, rs)
    expected = []
    remaining = n0
    for r in rs:
        remaining = max(0.0, remaining - worst_case_A(r, Q))
        expected.append(remaining)
    assert out == expected, f"adversarial matches manual running sum: got {out}, expected {expected}"
    assert all(
        out[i] <= out[i - 1] for i in range(1, len(out))
    ), f"adversarial non-increasing: out={out}"


def test_adversarial_floors_at_zero():
    print("test_adversarial_floors_at_zero")
    Q = 101
    # tiny n0: the very first filter's proved capacity (worst_case_A(3,101),
    # in the thousands) vastly exceeds it, so the trajectory must hit exactly
    # 0.0 at layer 0 and stay there, never going negative.
    out = lib.adversarial_trajectory(5.0, Q, [3, 5, 7])
    assert all(v == 0.0 for v in out), f"adversarial floors at 0: out={out}"


# ---------------------------------------------------------------------------
# mixture_trajectory: boundary agreement with the other three
# ---------------------------------------------------------------------------

def test_mixture_score_half_matches_random():
    print("test_mixture_score_half_matches_random")
    n0, rs = 5049.0, [3, 5, 7, 11, 13]
    a = lib.mixture_trajectory(n0, rs, 0.5)
    b = lib.random_trajectory(n0, rs)
    assert all(
        close(x, y) for x, y in zip(a, b)
    ), f"mixture(0.5) == random_trajectory: mixture={a} random={b}"


def test_mixture_score_zero_is_flat():
    print("test_mixture_score_zero_is_flat")
    n0, rs = 395.0, [23, 29, 31]
    out = lib.mixture_trajectory(n0, rs, 0.0)
    assert all(close(v, n0) for v in out), f"mixture(0) flat at n0: out={out}"


def test_mixture_score_one_zeroes_immediately():
    print("test_mixture_score_one_zeroes_immediately")
    # score=1 => f=1 at the very first step (see module docstring: this is
    # the degenerate always-f=1 case, distinct from adversarial_trajectory's
    # proved-capacity version).
    out = lib.mixture_trajectory(395.0, [23, 29, 31], 1.0)
    assert all(v == 0.0 for v in out), f"mixture(1) all zero: out={out}"


def test_mixture_rejects_out_of_range_score():
    print("test_mixture_rejects_out_of_range_score")
    raised = False
    try:
        lib.mixture_trajectory(100.0, [5], 1.5)
    except ValueError:
        raised = True
    assert raised, "mixture(1.5) raises ValueError"