"""Green-gate test suite for the four_lines (friendly/random/adversarial/
mixture trajectory) library.

Run:  python3 test_four_lines.py

Exits 0 if every assertion holds, 1 otherwise, matching test_lineage.py's
convention. Ground truth for random_trajectory and mixture_trajectory is
hand-computed rational arithmetic (no prime-counting needed). Ground truth
for adversarial_trajectory cross-checks against window.worst_case_A directly
(already an established, tested primitive) -- this suite tests the new
compounding/orchestration logic, not worst_case_A's own correctness.
"""

import sys

from sieve_sequence_empirical import four_lines as lib
from sieve_sequence_empirical.window import worst_case_A

FAILURES = []


def check(name, cond, detail=""):
    if cond:
        print(f"  PASS  {name}")
    else:
        print(f"  FAIL  {name}  {detail}")
        FAILURES.append(name)


def close(a, b, tol=1e-9):
    return abs(a - b) <= tol


# ---------------------------------------------------------------------------
# friendly_trajectory
# ---------------------------------------------------------------------------

def test_friendly():
    print("test_friendly")
    out = lib.friendly_trajectory(395, 5)
    check("friendly length==5", len(out) == 5, f"len={len(out)}")
    check("friendly all equal n0", all(v == 395.0 for v in out), f"out={out}")


# ---------------------------------------------------------------------------
# random_trajectory: hand-computed exact compounding
# ---------------------------------------------------------------------------

def test_random_hand_derived():
    print("test_random_hand_derived")
    # n0=100, rs=[5,7]:
    #   after r=5: 100*(1-2/5) = 100*0.6 = 60
    #   after r=7: 60*(1-2/7)  = 60*(5/7) = 300/7
    out = lib.random_trajectory(100.0, [5, 7])
    check("random layer0 == 60", close(out[0], 60.0), f"got {out[0]}")
    check("random layer1 == 300/7", close(out[1], 300.0 / 7.0), f"got {out[1]}")
    check("random length==2", len(out) == 2, f"len={len(out)}")


def test_random_monotone_decreasing():
    print("test_random_monotone_decreasing")
    out = lib.random_trajectory(5049.0, [3, 5, 7, 11, 13])
    # each factor (1-2/r) is in (0,1) for r>2, so the sequence strictly
    # decreases and always stays positive.
    check("random strictly decreasing", all(
        out[i] < out[i - 1] for i in range(1, len(out))
    ), f"out={out}")
    check("random stays positive", all(v > 0 for v in out), f"out={out}")


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
    check("adversarial matches manual running sum", out == expected,
          f"got {out}, expected {expected}")
    check("adversarial non-increasing", all(
        out[i] <= out[i - 1] for i in range(1, len(out))
    ), f"out={out}")


def test_adversarial_floors_at_zero():
    print("test_adversarial_floors_at_zero")
    Q = 101
    # tiny n0: the very first filter's proved capacity (worst_case_A(3,101),
    # in the thousands) vastly exceeds it, so the trajectory must hit exactly
    # 0.0 at layer 0 and stay there, never going negative.
    out = lib.adversarial_trajectory(5.0, Q, [3, 5, 7])
    check("adversarial floors at 0", all(v == 0.0 for v in out), f"out={out}")


# ---------------------------------------------------------------------------
# mixture_trajectory: boundary agreement with the other three
# ---------------------------------------------------------------------------

def test_mixture_score_half_matches_random():
    print("test_mixture_score_half_matches_random")
    n0, rs = 5049.0, [3, 5, 7, 11, 13]
    a = lib.mixture_trajectory(n0, rs, 0.5)
    b = lib.random_trajectory(n0, rs)
    check("mixture(0.5) == random_trajectory", all(
        close(x, y) for x, y in zip(a, b)
    ), f"mixture={a} random={b}")


def test_mixture_score_zero_is_flat():
    print("test_mixture_score_zero_is_flat")
    n0, rs = 395.0, [23, 29, 31]
    out = lib.mixture_trajectory(n0, rs, 0.0)
    check("mixture(0) flat at n0", all(close(v, n0) for v in out), f"out={out}")


def test_mixture_score_one_zeroes_immediately():
    print("test_mixture_score_one_zeroes_immediately")
    # score=1 => f=1 at the very first step (see module docstring: this is
    # the degenerate always-f=1 case, distinct from adversarial_trajectory's
    # proved-capacity version).
    out = lib.mixture_trajectory(395.0, [23, 29, 31], 1.0)
    check("mixture(1) all zero", all(v == 0.0 for v in out), f"out={out}")


def test_mixture_rejects_out_of_range_score():
    print("test_mixture_rejects_out_of_range_score")
    raised = False
    try:
        lib.mixture_trajectory(100.0, [5], 1.5)
    except ValueError:
        raised = True
    check("mixture(1.5) raises ValueError", raised)


def main():
    print("four_lines library: green gate")
    print()
    test_friendly()
    test_random_hand_derived()
    test_random_monotone_decreasing()
    test_adversarial_matches_worst_case_A()
    test_adversarial_floors_at_zero()
    test_mixture_score_half_matches_random()
    test_mixture_score_zero_is_flat()
    test_mixture_score_one_zeroes_immediately()
    test_mixture_rejects_out_of_range_score()
    print()
    if FAILURES:
        print(f"RESULT: FAIL  ({len(FAILURES)} failing checks)")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
