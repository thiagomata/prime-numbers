"""Green-gate test suite for the spacing (implied-spacing-view) library.

Run:  python3 test_spacing.py

Matches test_four_lines.py's convention. The load-bearing check here is
test_random_spacing_matches_direct_density: it verifies, not just asserts,
the module docstring's claim that implied_spacing is a reciprocal-scaling
transform of four_lines.random_trajectory, provably identical to computing
1/density_at(Q) directly -- not a second, independent model that might
disagree.
"""

import sys

from sieve_sequence_empirical import four_lines
from sieve_sequence_empirical import spacing as lib

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
# density_at: hand-derived
# ---------------------------------------------------------------------------

def test_density_at_hand_derived():
    print("test_density_at_hand_derived")
    # primes in [3,4): {3}. dens = 0.5 * (1-2/3) = 0.5/3
    d3 = lib.density_at(3)
    check("density_at(3) == 0.5/3", close(d3, 0.5 / 3.0), f"got {d3}")
    # primes in [3,6): {3,5}. dens = 0.5 * (1/3) * (3/5) = 0.1
    d5 = lib.density_at(5)
    check("density_at(5) == 0.1", close(d5, 0.1), f"got {d5}")


def test_density_at_strictly_decreasing():
    print("test_density_at_strictly_decreasing")
    ds = [lib.density_at(q) for q in (3, 5, 7, 11, 13)]
    check("density_at strictly decreasing", all(
        ds[i] < ds[i - 1] for i in range(1, len(ds))
    ), f"ds={ds}")
    check("density_at stays positive", all(d > 0 for d in ds), f"ds={ds}")


# ---------------------------------------------------------------------------
# implied_spacing: hand-derived and edge cases
# ---------------------------------------------------------------------------

def test_implied_spacing_hand_derived():
    print("test_implied_spacing_hand_derived")
    out = lib.implied_spacing(100.0, [50.0, 25.0], 2.0)
    check("spacing[0] == 4", close(out[0], 4.0), f"got {out[0]}")
    check("spacing[1] == 8", close(out[1], 8.0), f"got {out[1]}")


def test_implied_spacing_zero_count_is_infinite():
    print("test_implied_spacing_zero_count_is_infinite")
    out = lib.implied_spacing(100.0, [10.0, 0.0, 5.0], 1.0)
    check("finite before extinction", out[0] == 10.0, f"got {out[0]}")
    check("infinite at zero count", out[1] == float("inf"), f"got {out[1]}")
    check("finite after (would-be) extinction still computed", out[2] == 20.0, f"got {out[2]}")


def test_implied_spacing_rejects_bad_input():
    print("test_implied_spacing_rejects_bad_input")
    for label, call in [
        ("n0<=0", lambda: lib.implied_spacing(0.0, [1.0], 1.0)),
        ("ref_spacing<=0", lambda: lib.implied_spacing(1.0, [1.0], 0.0)),
        ("negative count", lambda: lib.implied_spacing(1.0, [-1.0], 1.0)),
    ]:
        raised = False
        try:
            call()
        except ValueError:
            raised = True
        check(f"{label} raises ValueError", raised)


# ---------------------------------------------------------------------------
# The load-bearing check: transform agrees with direct density computation
# ---------------------------------------------------------------------------

def test_random_spacing_matches_direct_density():
    print("test_random_spacing_matches_direct_density")
    anchor_r = 23
    rs = [29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
    n0 = 361.0
    counts = four_lines.random_trajectory(n0, rs)
    ref_spacing = 1.0 / lib.density_at(anchor_r)
    transformed = lib.implied_spacing(n0, counts, ref_spacing)
    direct = [1.0 / lib.density_at(r) for r in rs]
    check("transform == direct 1/density_at(Q) at every layer", all(
        close(t, d, tol=1e-6) for t, d in zip(transformed, direct)
    ), f"transformed={transformed}\ndirect={direct}")


def test_friendly_spacing_is_flat():
    print("test_friendly_spacing_is_flat")
    n0 = 361.0
    friendly = four_lines.friendly_trajectory(n0, 5)
    ref_spacing = 1.0 / lib.density_at(23)
    out = lib.implied_spacing(n0, friendly, ref_spacing)
    check("friendly spacing constant", all(close(v, ref_spacing) for v in out), f"out={out}")


def main():
    print("spacing library: green gate")
    print()
    test_density_at_hand_derived()
    test_density_at_strictly_decreasing()
    test_implied_spacing_hand_derived()
    test_implied_spacing_zero_count_is_infinite()
    test_implied_spacing_rejects_bad_input()
    test_random_spacing_matches_direct_density()
    test_friendly_spacing_is_flat()
    print()
    if FAILURES:
        print(f"RESULT: FAIL  ({len(FAILURES)} failing checks)")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
