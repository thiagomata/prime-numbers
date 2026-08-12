"""Green-gate test suite for the phase_transition library.

Run:  python3 test_phase_transition.py

Matches the established convention (test_four_lines.py, test_spacing.py).
Ground truth: hand-computed values already spot-checked directly in
conversation (see draft article section 5.1/5.2 boxed formulas), plus
structural identities that must hold regardless of the specific numbers
(c=0 reduces to fixed w=1; the log-growth family crosses from divergent to
convergent trend exactly where the article says it does).
"""

import math
import sys

from sympy import primerange

from sieve_sequence_empirical import phase_transition as lib

FAILURES = []


def check(name, cond, detail=""):
    if cond:
        print(f"  PASS  {name}")
    else:
        print(f"  FAIL  {name}  {detail}")
        FAILURES.append(name)


def close(a, b, tol=1e-6):
    return abs(a - b) <= tol


# ---------------------------------------------------------------------------
# Window occupancy: fixed w
# ---------------------------------------------------------------------------

def test_fixed_w_hand_derived():
    print("test_fixed_w_hand_derived")
    # Q=1000, w=1: lambda ~ Q^2/(ln Q)^2 = 1e6/(6.9078)^2 = 20958.9...
    log10_lambda = lib.log10_window_occupancy_fixed_w(3.0, 1.0)
    expected = math.log10((1000.0 ** 2) / (math.log(1000.0) ** 2))
    check("w=1, Q=1000 matches direct computation", close(log10_lambda, expected),
          f"got {log10_lambda}, expected {expected}")


def test_fixed_w_eventually_recovers_for_large_w():
    print("test_fixed_w_eventually_recovers_for_large_w")
    # w=10 dips negative at moderate Q (per conversation: log10(lambda) < 0
    # around log10(Q)=10) then must recover to positive by log10(Q)=50,
    # since Q^2 eventually beats any fixed power of ln(Q).
    dip = lib.log10_window_occupancy_fixed_w(10.0, 10.0)
    recovered = lib.log10_window_occupancy_fixed_w(50.0, 10.0)
    check("w=10 is negative (dipped) at log10(Q)=10", dip < 0, f"got {dip}")
    check("w=10 has recovered positive by log10(Q)=50", recovered > 0, f"got {recovered}")
    check("w=10 keeps climbing from Q=50 to Q=100", lib.log10_window_occupancy_fixed_w(100.0, 10.0) > recovered)


def test_fixed_w_always_eventually_diverges():
    print("test_fixed_w_always_eventually_diverges")
    # Property III: for ANY finite w, log10(lambda) -> +infinity as
    # log10(Q) -> infinity (since the Q^2 term dominates linearly in
    # log10(Q) while the (ln Q)^(2w) term only grows like log(log10_Q)).
    for w in (1.0, 3.0, 6.0, 10.0, 50.0):
        far = lib.log10_window_occupancy_fixed_w(1000.0, w)
        farther = lib.log10_window_occupancy_fixed_w(10000.0, w)
        check(f"w={w} still climbing at huge log10(Q)", farther > far,
              f"far={far}, farther={farther}")


# ---------------------------------------------------------------------------
# Window occupancy: log-growth family w_r = 1 + c*log(r)
# ---------------------------------------------------------------------------

def test_log_growth_c_zero_matches_fixed_w_one():
    print("test_log_growth_c_zero_matches_fixed_w_one")
    for log10_Q in (2.0, 3.0, 5.0, 8.0):
        a = lib.log10_window_occupancy_log_growth(log10_Q, 0.0)
        b = lib.log10_window_occupancy_fixed_w(log10_Q, 1.0)
        check(f"c=0 == fixed w=1 at log10(Q)={log10_Q}", close(a, b), f"{a} vs {b}")


def test_log_growth_hand_derived():
    print("test_log_growth_hand_derived")
    # Q=1000, c=0.5: lambda ~ Q^(2-1)/(ln Q)^2 = 1000/(6.9078)^2 = 20.958...
    log10_lambda = lib.log10_window_occupancy_log_growth(3.0, 0.5)
    expected = math.log10(1000.0 / (math.log(1000.0) ** 2))
    check("c=0.5, Q=1000 matches direct computation", close(log10_lambda, expected),
          f"got {log10_lambda}, expected {expected}")


def test_log_growth_threshold_at_c_equals_one():
    print("test_log_growth_threshold_at_c_equals_one")
    # c<1: diverges (increasing without bound). c>1: tends to 0 (decreasing).
    for c, should_increase in [(0.3, True), (0.7, True), (1.5, False)]:
        near = lib.log10_window_occupancy_log_growth(4.0, c)
        far = lib.log10_window_occupancy_log_growth(8.0, c)
        if should_increase:
            check(f"c={c} (<1) diverges: far > near", far > near, f"near={near}, far={far}")
        else:
            check(f"c={c} (>1) decays: far < near", far < near, f"near={near}, far={far}")


# ---------------------------------------------------------------------------
# Constant adversarial share: locally fatal for every alpha>0
# ---------------------------------------------------------------------------

def test_constant_share_eventually_fatal():
    print("test_constant_share_eventually_fatal")
    near = lib.log10_window_occupancy_constant_share(2.0, 0.01)
    far = lib.log10_window_occupancy_constant_share(6.0, 0.01)
    farther = lib.log10_window_occupancy_constant_share(15.0, 0.01)
    check("constant share decreasing well before log10(Q)=6", far < near, f"{near} -> {far}")
    check("constant share keeps decreasing (not recovering)", farther < far, f"{far} -> {farther}")


def test_constant_share_worse_than_any_fixed_w():
    print("test_constant_share_worse_than_any_fixed_w")
    # At a large enough Q, the constant-share curve must fall below even a
    # generous fixed-w curve, since w_r ~ alpha*r/2 grows without bound.
    log10_Q = 10.0
    share = lib.log10_window_occupancy_constant_share(log10_Q, 0.01)
    fixed = lib.log10_window_occupancy_fixed_w(log10_Q, 50.0)
    check("constant share below fixed w=50 at log10(Q)=10", share < fixed,
          f"share={share}, fixed_w50={fixed}")


# ---------------------------------------------------------------------------
# Head probability and its cumulative sum over real primes
# ---------------------------------------------------------------------------

def test_head_probability_hand_derived():
    print("test_head_probability_hand_derived")
    p = lib.head_probability_log_growth(1000.0, 0.5)
    expected = 1.0 / ((1000.0 ** 1.0) * (math.log(1000.0) ** 2))
    check("c=0.5, Q=1000 matches direct computation", close(p, expected), f"{p} vs {expected}")


def test_cumulative_head_sum_diverges_below_half_converges_above():
    print("test_cumulative_head_sum_diverges_below_half_converges_above")
    primes = list(primerange(3, 2_000_000))
    for c, label in [(0.3, "below 1/2"), (0.7, "above 1/2")]:
        partial_100k = sum(lib.head_probability_log_growth(p, c) for p in primes if p < 100_000)
        partial_2m = sum(lib.head_probability_log_growth(p, c) for p in primes)
        ratio = partial_2m / partial_100k
        if c < 0.5:
            check(f"c={c} ({label}): sum still growing substantially", ratio > 1.5,
                  f"ratio={ratio:.3f}")
        else:
            check(f"c={c} ({label}): sum nearly flat (converging)", ratio < 1.15,
                  f"ratio={ratio:.3f}")


def main():
    print("phase_transition library: green gate")
    print()
    test_fixed_w_hand_derived()
    test_fixed_w_eventually_recovers_for_large_w()
    test_fixed_w_always_eventually_diverges()
    test_log_growth_c_zero_matches_fixed_w_one()
    test_log_growth_hand_derived()
    test_log_growth_threshold_at_c_equals_one()
    test_constant_share_eventually_fatal()
    test_constant_share_worse_than_any_fixed_w()
    test_head_probability_hand_derived()
    test_cumulative_head_sum_diverges_below_half_converges_above()
    print()
    if FAILURES:
        print(f"RESULT: FAIL  ({len(FAILURES)} failing checks)")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
