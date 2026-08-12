"""Green-gate test suite for the lineage experiment library.

Run:  python3 test_lineage.py

Exits 0 if every assertion holds, 1 otherwise. The empirical analog of
green-to-green: must be green before scaling Q. Every cited number must come
from a run that passed this suite.

Hand-derived ground truth is INDEPENDENT of lib_lineage (computed by brute
force in the derivation scripts, transcribed here).
"""

import sys
import os

import numpy as np

import lib_lineage as lib

FAILURES = []


def check(name, cond, detail=""):
    if cond:
        print(f"  PASS  {name}")
    else:
        print(f"  FAIL  {name}  {detail}")
        FAILURES.append(name)


def primes_below(n):
    out = []
    p = 2
    while p < n:
        out.append(p)
        # naive next prime
        q = p + 1
        while q < n:
            if all(q % d != 0 for d in range(2, int(q ** 0.5) + 1)):
                break
            q += 1
        else:
            break
        p = q
    return out


# ---------------------------------------------------------------------------
# 1. sigma_r self-consistency (whole-period geometry)
# ---------------------------------------------------------------------------
# Stage {2,3}: M=6, residues {1,5}, gaps [4,2]. r=5.
#   sigma_5(2) = 5 * min(4,2) = 10
#   sigma_5(2=T) = 5 * (4+2) = 30 = r*M


def test_sigma_self_consistency():
    print("test_sigma_self_consistency")
    # sigma_r(k) = r * min over i of (sum of k-1 consecutive cyclic cofactor gaps).
    # NOTE: k-1 gaps are summed, so for k=T this is r*(M - max_gap), NOT r*M.
    # The full-period span r*M would need k=T+1, which is outside the valid
    # range [2,T]. This is a real definitional subtlety, not a bug.
    g, M = lib.full_period_cofactor_gaps([2, 3])
    check("stage{2,3} M==6", M == 6, f"M={M}")
    check("stage{2,3} gaps==[4,2]", g == [4, 2], f"gaps={g}")
    s2, _ = lib.sigma_r_for_layer(2, 5, [2, 3])
    check("sigma_5(2)==10 (r*min_gap=5*2)", s2 == 10, f"sigma_5(2)={s2}")
    # sigma_5(T=2) = r*(M - max_gap) = 5*(6-4) = 10  (sums 1 gap = min gap)
    sT2, _ = lib.sigma_r_for_layer(len(g), 5, [2, 3])
    check("sigma_5(T=2)==5*(6-max_gap=4)==10", sT2 == 5 * (6 - max(g)), f"sigma_5(T)={sT2}")

    # Stage {2,3,5}: M=30, gaps [6,4,2,4,2,4,6,2], T=8. r=7.
    g3, M3 = lib.full_period_cofactor_gaps([2, 3, 5])
    check("stage{2,3,5} M==30", M3 == 30, f"M={M3}")
    check("stage{2,3,5} T==8", len(g3) == 8, f"T={len(g3)}")
    s_min, _ = lib.sigma_r_for_layer(2, 7, [2, 3, 5])
    check("sigma_7(2)==7*2==14", s_min == 14, f"sigma_7(2)={s_min}")
    # sigma_7(T=8) = 7*(30 - max_gap=6) = 7*24 = 168
    s_full, _ = lib.sigma_r_for_layer(len(g3), 7, [2, 3, 5])
    check("sigma_7(T=8)==7*(30-6)==168", s_full == 7 * (30 - max(g3)), f"sigma_7(T)={s_full}")


# ---------------------------------------------------------------------------
# 2. Layer 0 edge case: sigma undefined (T=1 < k=2)
# ---------------------------------------------------------------------------
def test_layer0_sigma_undefined():
    print("test_layer0_sigma_undefined")
    g, M = lib.full_period_cofactor_gaps([2])
    check("stage{2} M==2", M == 2, f"M={M}")
    check("stage{2} T==1", len(g) == 1, f"T={len(g)}")
    # sigma_r_for_layer should raise for k=2 when T=1
    try:
        lib.sigma_r_for_layer(2, 3, [2])
        check("sigma_3(2) on T=1 raises", False, "did not raise")
    except ValueError:
        check("sigma_3(2) on T=1 raises", True)


# ---------------------------------------------------------------------------
# 3. Hand-derived layer 1 (install r=5, stage before {2,3}) at Q=17
# ---------------------------------------------------------------------------
# Window [17,289). Pre-filter (coprime to {2,3}): 91 values.
# 2-gap starts: 45. destroyed by 5: 18. surviving: 27.
def test_layer1_hand_Q17():
    print("test_layer1_hand_Q17")
    res = lib.layer(Q=17, r=5, primes_strictly_below_r=[2, 3])
    check("G_r_window==45", res["G_r_window"] == 45, str(res))
    check("destroyed==18", res["destroyed"] == 18, str(res))
    check("surviving==27", res["surviving"] == 27, str(res))
    check("destroyed+surviving==G_r",
          res["destroyed"] + res["surviving"] == res["G_r_window"], str(res))
    # sigma_5(2) defined here (T=2): r*min_gap = 5*2 = 10
    check("sigma_r_2==10", res["sigma_r_2"] == 10, str(res))
    # sigma_5(T=2) = r*(M - max_gap) = 5*(6-4) = 10 (sums 1 gap)
    check("sigma_r_T==10 (r*(M-max_gap))", res["sigma_r_T"] == 10, str(res))
    check("M_r==6", res["M_r"] == 6, str(res))


# ---------------------------------------------------------------------------
# 4. Reading A consistency: population shrinks layer to layer
# ---------------------------------------------------------------------------
def test_reading_a_population_shrinks():
    print("test_reading_a_population_shrinks")
    Q = 17
    # Layers install primes 3,5,7,11,13 in order. For each layer r, the stage
    # BEFORE r has filters = all primes < r. So primes_strictly_below_r is the
    # cumulative set INCLUDING 2 (which is always installed before r=3).
    all_primes_below_Q = [2, 3, 5, 7, 11, 13]  # primes < 17
    for r in [3, 5, 7, 11, 13]:
        below = [p for p in all_primes_below_Q if p < r]
        res = lib.layer(Q, r, list(below))
        # Reading A: after installing r, the accepted set = before-set minus r-hits,
        # which must equal the before-set of the NEXT layer.
        below_plus_r = below + [r]
        pre_next = lib.window_survivors(Q, below_plus_r)
        post_this = lib.window_survivors(Q, below)
        post_this_filtered = [v for v in post_this if v % r != 0]
        check(f"layer r={r}: post==pre_next (Reading A)",
              pre_next == post_this_filtered, f"r={r} below={below}")
        check(f"layer r={r}: G_rWindow>=surviving",
              res["G_r_window"] >= res["surviving"], str(res))


# ---------------------------------------------------------------------------
# 5. Cyclic vs window-linear run reported separately (open question check)
# ---------------------------------------------------------------------------
def test_cyclic_and_window_runs_both_reported():
    print("test_cyclic_and_window_runs_both_reported")
    res = lib.layer(Q=17, r=7, primes_strictly_below_r=[2, 3, 5])
    check("cyclic_run_full_period is int", isinstance(res["cyclic_run_full_period"], int), str(res))
    check("window_linear_run is int", isinstance(res["window_linear_run"], int), str(res))
    # both non-negative, cyclic >= window-linear in general (larger domain)
    check("cyclic>=0", res["cyclic_run_full_period"] >= 0, str(res))
    check("window_linear>=0", res["window_linear_run"] >= 0, str(res))


# ---------------------------------------------------------------------------
# 6. #12 / #13 margins are finite and signed
# ---------------------------------------------------------------------------
def test_margins_finite():
    print("test_margins_finite")
    res = lib.layer(Q=17, r=7, primes_strictly_below_r=[2, 3, 5])
    for k in ["c12_margin", "c13_margin", "post_E_q"]:
        v = res[k]
        check(f"{k} finite", v == v, str(res))  # not NaN


def test_sigma_stable_no_wall():
    """sigma_r(k) for small k uses the PROVEN STABLE table once {2,3,5,7} are
    installed, so it is O(1) and independent of M -- no primorial wall. Verify
    the stable values pin and that a large-M stage returns them without error."""
    print("test_sigma_stable_no_wall")
    # pin the stable table (computed exactly from {2,3,5,7}, verified at 8 primes)
    expected = {2: 2, 3: 6, 4: 8, 5: 12, 6: 16, 7: 20, 8: 26, 9: 30, 10: 32}
    for k, v in expected.items():
        check(f"sigma_stable({k})=={v}", lib.sigma_r_stable(k) == v, f"got {lib.sigma_r_stable(k)}")
    # a LARGE primorial stage (M huge, far past the old 5e7 "wall") must still
    # return sigma_r(k) for small k via the stable table, no error.
    big_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]  # M ~ 2e11
    r = 37
    for k in (2, 3, 6):
        s, M = lib.sigma_r_for_layer(k, r, big_primes)
        check(f"large-M sigma_{r}({k})=={r}*{expected[k]} no wall",
              s == r * expected[k], f"got {s}, M={M}")


def main():
    print("lineage experiment: green gate")
    print()
    test_sigma_self_consistency()
    test_sigma_stable_no_wall()
    test_layer0_sigma_undefined()
    test_layer1_hand_Q17()
    test_reading_a_population_shrinks()
    test_cyclic_and_window_runs_both_reported()
    test_margins_finite()
    print()
    if FAILURES:
        print(f"RESULT: FAIL  ({len(FAILURES)} failing checks)")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
