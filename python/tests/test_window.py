"""Green-gate test suite for the candidate stress-test library.

Run:  pytest python/tests/test_window.py

The empirical analog of `green-to-green`: it must be green before adding any
measurement column and re-run (still green) after.

Every number cited anywhere (README, FINDINGS, articles) must come from a run
that passed this suite.
"""

import os

import sympy
from sympy import isprime, nextprime

from sieve_sequence import window as lib


def primes_below(n: int):
    """Every prime strictly less than n, ascending."""
    out = []
    p = 2
    while p < n:
        out.append(p)
        p = int(nextprime(p))
    return out


# ---------------------------------------------------------------------------
# 1a. Hand check: q=5, p=3  (the transition that INSTALLS filter 3)
# ---------------------------------------------------------------------------
# W = [5, 25); installed filters below p=3 are just {2}; install 3.
# Pre-filter survivors (coprime to {2}) in W: 5,7,9,11,13,15,17,19,21,23.
# With only {2} installed, EVERY adjacent odd pair differs by 2, so
#   G_local == 9   (all 9 adjacent pairs are 2-gaps).
# Install 3: remove 9,15,21. Post-filter: 5,7,11,13,17,19,23.
#   2-gaps among those: (5,7),(11,13),(17,19)  -> surviving == 3.
# Destroyed: a 2-gap is destroyed iff an endpoint is 0 mod 3. The endpoints
#   9,15,21 each belong to TWO pre-filter 2-gaps (e.g. 9 is in (7,9) and
#   (9,11)), because filter 3 is NOT yet installed in the pre-filter stage, so
#   2-gaps still share endpoints here. Hence destroyed == 6 (NOT 3).
#   This is why the "one strike destroys at most one 2-gap" bound (and thus
#   destroyed <= A_worst) only holds for p >= 5; see 1b.
# A_worst: K = floor(24/3) = 8; A = pi(8) - pi(2) = 4 - 1 = 3.
# Identity: destroyed + surviving = 6 + 3 = 9 = G_local.  Holds (counting).


def test_hand_check_q5_p3():
    print("test_hand_check_q5_p3")
    res = lib.transition(p=3, q=5, primes_below_p=primes_below(3))
    assert res["surviving"] == 3, f"surviving==3: {res}"
    assert res["G_local"] == 9, f"G_local==9 (all odd pairs are 2-gaps): {res}"
    assert res["destroyed"] == 6, f"destroyed==6 (each mult of 3 kills two gaps): {res}"
    assert res["A_worst"] == 3, f"A_worst==3: {res}"
    assert res["surplus"] == 6, f"surplus==6 (G_local-A): {res}"
    assert res["destroyed"] == 2 * res["A_worst"], f"destroyed==2*A_worst (p=3 double-count): {res}"
    assert res["destroyed"] + res["surviving"] == res["G_local"], f"destroyed+surviving==G_local: {res}"


# ---------------------------------------------------------------------------
# 1b. Hand check: q=7, p=5  (first CLEAN transition: filter 3 already installed)
# ---------------------------------------------------------------------------
# W = [7, 49); installed filters below p=5 are {2,3}; install 5.
# Pre-filter survivors (coprime to {2,3}, i.e. 1 or 5 mod 6) in W:
#   7,11,13,17,19,23,25,29,31,35,37,41,43,47  (14 values).
# 2-gaps (adjacent diff 2): (11,13),(17,19),(23,25),(29,31),(35,37),(41,43)
#   -> G_local == 6.
# Install 5: remove 25,35. Post-filter:
#   7,11,13,17,19,23,29,31,37,41,43,47.
#   2-gaps: (11,13),(17,19),(29,31),(41,43) -> surviving == 4.
# Destroyed: endpoints 0 mod 5 are 25,35. (23,25) and (35,37) -> destroyed == 2.
# A_worst: K = floor(48/5) = 9; A = pi(9) - pi(4) = 4 - 2 = 2.
# Now filter 3 IS installed in the pre-filter stage, so 2-gaps are
#   endpoint-disjoint and one removal destroys at most one gap:
#   destroyed (2) <= A_worst (2). waste_ratio == 0 (exactly worst-case).


def test_hand_check_q7_p5():
    print("test_hand_check_q7_p5")
    res = lib.transition(p=5, q=7, primes_below_p=primes_below(5))
    assert res["G_local"] == 6, f"G_local==6: {res}"
    assert res["surviving"] == 4, f"surviving==4: {res}"
    assert res["destroyed"] == 2, f"destroyed==2: {res}"
    assert res["A_worst"] == 2, f"A_worst==2: {res}"
    assert res["surplus"] == 4, f"surplus==4: {res}"
    # The clean-transition bound: destroyed <= A_worst holds for p >= 5.
    assert res["destroyed"] <= res["A_worst"], f"destroyed<=A_worst (p>=5 isolation): {res}"
    assert res["destroyed"] + res["surviving"] == res["G_local"], f"destroyed+surviving==G_local: {res}"


# ---------------------------------------------------------------------------
# 2. Structural identities over a range of transitions
# ---------------------------------------------------------------------------

def test_structural_identities():
    print("test_structural_identities")
    p = 3
    q = int(nextprime(p))
    transitions = 0
    while transitions < 60:  # p up to a few hundred
        res = lib.transition(p=p, q=q, primes_below_p=primes_below(p))
        # (a) window length is exactly q^2 - q
        assert res["window_len"] == q * q - q, f"window_len==q^2-q @p={p}: {res}"
        # (b) surviving never negative
        assert res["surviving"] >= 0, f"surviving>=0 @p={p}: {res}"
        # (c) destroyed in [0, G_local]
        assert 0 <= res["destroyed"] <= res["G_local"], f"0<=destroyed<=G_local @p={p}: {res}"
        # (d) worst-case destruction bound. For p >= 5 (filter 3 already in the
        #     pre-filter stage) 2-gaps are endpoint-disjoint so one removal
        #     destroys at most one gap: destroyed <= A_worst. For p == 3 the
        #     pre-filter still has overlapping 2-gaps (no filter 3 yet), so a
        #     removal can kill two gaps and the bound is destroyed <= 2*A_worst.
        bound = res["A_worst"] if p >= 5 else 2 * res["A_worst"]
        assert res["destroyed"] <= bound, f"destroyed<=bound @p={p}: {res}"
        # (e) the load-bearing identity: destroyed + surviving == G_local
        #     holds for p > 2 because the two endpoints of a 2-gap differ by 2 < p
        assert res["destroyed"] + res["surviving"] == res["G_local"], f"destroyed+surviving==G_local @p={p}: {res}"
        transitions += 1
        p = q
        q = int(nextprime(p))


# ---------------------------------------------------------------------------
# 3. surviving>0  <=>  a twin-prime pair exists in [q, q^2)
# ---------------------------------------------------------------------------
# A 2-gap among POST-filter survivors in W certifies a twin-prime pair, because
# both endpoints are < q^2 and coprime to every prime < q. So surviving>0 should
# agree exactly with "there is a twin prime pair (n, n+2) with q <= n and
# n+2 < q^2". Cross-check against sympy.isprime directly.


def test_surviving_means_twin_prime():
    print("test_surviving_means_twin_prime")
    p = 3
    q = int(nextprime(p))
    transitions = 0
    while transitions < 40:
        res = lib.transition(p=p, q=q, primes_below_p=primes_below(p))
        # brute-force ground truth: any twin pair (n, n+2) with q<=n, n+2<q^2
        hi = q * q
        has_twin = any(
            isprime(n) and isprime(n + 2) for n in range(q, hi - 1)
        )
        assert (res["surviving"] > 0) == has_twin, f"surviving>0 == has_twin @p={p},q={q}: surviving={res['surviving']} has_twin={has_twin}"
        transitions += 1
        p = q
        q = int(nextprime(p))


# ---------------------------------------------------------------------------
# 4. Cross-check G_local convention internally
# ---------------------------------------------------------------------------
# The canonical experiment uses [q, q^2). Recomputing its G_local through both
# sieving and a survivor-list difference checks internal consistency and guards
# against a bug shared by only one of those paths.


def test_g_local_self_consistent():
    print("test_g_local_self_consistent")
    p = 3
    q = int(nextprime(p))
    for _ in range(30):
        res = lib.transition(p=p, q=q, primes_below_p=primes_below(p))
        # recompute G_local by an independent path: count_two_gaps over a freshly
        # sieved list, but sieved by a different code path (pure python, no numpy)
        lo, hi = q, q * q
        surv = []
        for v in range(lo, hi):
            if all(v % r != 0 for r in primes_below(p)):
                surv.append(v)
        g_local_independent = sum(
            1 for a, b in zip(surv, surv[1:]) if b - a == 2
        )
        assert res["G_local"] == g_local_independent, f"G_local matches independent sieve @p={p}: {res['G_local']} vs {g_local_independent}"
        p = q
        q = int(nextprime(p))


# ---------------------------------------------------------------------------
# 5. Candidate-specific columns, hand-verified at q=7, p=5
# ---------------------------------------------------------------------------
# Pre-filter survivors (coprime to {2,3}) in [7,49):
#   7,11,13,17,19,23,25,29,31,35,37,41,43,47
# 2-gap starts: 11,17,23,29,35,41  (G_local == 6)
# p = 5, so "width < 5" means differences in {0,1,2,3,4}.
#   starts spaced: 17-11=6, 23-17=6, 29-23=6, 35-29=6, 41-35=6. All gaps are 6.
#   => no two starts within width <5 (need diff <5 but all diffs are 6).
#   => max_cluster_in_width_p == 1.
# destroyed starts (x=0 or x+2=0 mod 5): x=23 (25), x=35. So 23 and 35 destroyed,
#   not adjacent in the start list (29 sits between). => max_cons_destroyed_run == 1.
# head_to_first_start: post-filter 2-gap starts are 11,17,29,41; first >=7 is 11;
#   d_head = 11 - 7 = 4.


def test_candidate_columns_q7_p5():
    print("test_candidate_columns_q7_p5")
    res = lib.transition(p=5, q=7, primes_below_p=primes_below(5))
    assert res["max_cluster_in_width_p"] == 1, f"max_cluster_in_width_p==1: {res}"
    assert res["max_cons_destroyed_run"] == 1, f"max_cons_destroyed_run==1: {res}"
    assert res["d_head"] == 4, f"d_head==4: {res}"
    # #11 random-like: destruction_rate == destroyed/G_local == 2/6 == 1/3;
    #   gap_2_over_p == 2/5 == 0.4. So real destruction (0.333) is below the
    #   uniform-residue benchmark (0.4) here.
    assert abs(res["destruction_rate"] - (1.0 / 3.0)) < 1e-12, f"destruction_rate==1/3: {res}"
    assert abs(res["gap_2_over_p"] - 0.4) < 1e-12, f"gap_2_over_p==0.4: {res}"
    # main_term > 0 and E_q is a finite number
    assert res["main_term"] > 0, f"main_term>0: {res}"
    assert res["E_q"] == res["E_q"], f"E_q finite: {res}"  # not NaN
    # residue_max_dev and endpoint_bias are finite and >= 0
    assert res["residue_max_dev"] >= 0, f"residue_max_dev>=0: {res}"
    assert res["endpoint_bias"] >= 0, f"endpoint_bias>=0: {res}"


# ---------------------------------------------------------------------------
# 6. Cross-check against the independent gaps.csv (different generation path)
# ---------------------------------------------------------------------------
# gaps.csv (presentation repo's generate_gaps.py) is a pure-Python walk-forward
# survivor list, independent of this tool's NumPy sieve. It is a fixed 4000-gap
# PREFIX per stage. Its limit is NOT that it fails to reach the window early --
# because gaps are small, the 4000-gap prefix reaches q^2 for stages up to head
# ~1123 (187 of 200 stages). So for those stages it is a valid independent
# survivor-set cross-check over the FULL window [q, q^2). Beyond ~head 1123 it
# stops reaching q^2 and the cross-check becomes partial.
#
# If gaps.csv is not present at the expected path, this test is SKIPPED (not
# failed): it is a cross-check against an external file, not a self-contained
# invariant.

GAPS_CSV_CANDIDATES = [
    "/Users/thiagomata/github/thiagomata/prime-numbers-presentation/"
    "presentations/sieve-sequence-visualization/figures/out/gaps.csv",
    # allow override for portability
    os.environ.get("GAPS_CSV", ""),
]


def _find_gaps_csv():
    for path in GAPS_CSV_CANDIDATES:
        if path and os.path.exists(path):
            return path
    return None


def test_cross_check_gaps_csv():
    print("test_cross_check_gaps_csv")
    path = _find_gaps_csv()
    if path is None:
        print("  SKIP  gaps.csv not found (external cross-check, optional)")
        return
    import csv
    rows = list(csv.DictReader(open(path)))
    bystage = {}
    for r in rows:
        bystage.setdefault(int(r["stage_index"]), []).append(int(r["survivor"]))
    heads_map = {int(r["head"]): int(r["stage_index"]) for r in rows}

    # cross-check a spread of heads where the prefix is known to reach q^2
    for head in (7, 13, 31, 53, 101, 223, 521, 887):
        if head not in heads_map:
            continue
        q = int(sympy.nextprime(head))
        lo, hi = q, q * q
        mine = lib.survivors_list(q=q, filter_primes=primes_below(head))
        mine_win = [v for v in mine if lo <= v < hi]
        gsv = bystage[heads_map[head]]
        gsv_win = [v for v in gsv if lo <= v < hi]
        # only assert equality if gaps.csv actually reaches the window end;
        # otherwise assert mine_win is a prefix of gsv_win (partial coverage)
        if gsv and gsv[-1] >= hi - 1:
            assert mine_win == gsv_win, f"survivors==gaps.csv over full window @head={head}: mine={len(mine_win)} gaps={len(gsv_win)}"
        else:
            assert gsv_win == mine_win[: len(gsv_win)], f"survivors prefix==gaps.csv (partial) @head={head}: mine={len(mine_win)} gaps={len(gsv_win)}"


# ---------------------------------------------------------------------------
# 6. Second hand example: q=11, p=7  (independently derived, NOT via lib.py)
# ---------------------------------------------------------------------------
# W = [11, 121); installed filters below p=7 are {2,3,5}; install 7.
# Pre-filter survivors (coprime to {2,3,5}, the units mod 30) in [11,121):
#   11,13,17,19,23,29,31,37,41,43,47,49,53,59,61,67,71,73,77,79,83,89,91,97,
#   101,103,107,109,113,119   (30 values).
# 2-gap starts: 11,17,29,41,47,59,71,77,89,101,107   -> G_local == 11.
# Destroyed by installing 7 (start x with x=0 or x+2=0 mod 7): 47,77,89
#   -> destroyed == 3.  Surviving starts: 11,17,29,41,59,71,101,107 -> surviving == 8.
# A_worst: K=floor(120/7)=17; A = pi(17)-pi(6) = 7-3 = 4.
# max_cluster_in_width_p (largest set of starts within width <7):
#   consecutive start diffs: 17-11=6 (<7, pair), then 29-17=12 (breaks).
#   So the only within-width-7 cluster is {11,17}; size 2. -> 2.
# max_cons_destroyed_run: in start order [11,17,29,41,47,59,71,77,89,101,107],
#   destroyed are 47,77,89. 77 and 89 are NOT adjacent (101 sits... no: order is
#   ...,77,89,101,... so 77 and 89 ARE adjacent in start-order). Wait: 47 then 59
#   (59 not destroyed) breaks the first; 77 then 89 both destroyed -> run of 2.
#   -> 2.
# d_head: post-filter 2-gap starts >= 11; first is 11 itself -> d_head == 0.


def test_hand_check_q11_p7():
    print("test_hand_check_q11_p7")
    res = lib.transition(p=7, q=11, primes_below_p=primes_below(7))
    assert res["G_local"] == 11, f"G_local==11: {res}"
    assert res["surviving"] == 8, f"surviving==8: {res}"
    assert res["destroyed"] == 3, f"destroyed==3: {res}"
    assert res["A_worst"] == 4, f"A_worst==4: {res}"
    assert res["max_cluster_in_width_p"] == 2, f"max_cluster_in_width_p==2: {res}"
    assert res["max_cons_destroyed_run"] == 2, f"max_cons_destroyed_run==2: {res}"
    assert res["d_head"] == 0, f"d_head==0: {res}"
    assert res["destroyed"] + res["surviving"] == res["G_local"], f"destroyed+surviving==G_local: {res}"


# ---------------------------------------------------------------------------
# 7. Exact pinning of #12/#13 at q=7, p=5 (independently derived)
# ---------------------------------------------------------------------------
# 2-gap starts: 11,17,23,29,35,41 (G_local=6).
# #12 residue classes mod 5 of the starts: 11->1, 17->2, 23->3, 29->4, 35->0,
#   41->1.  Counts {0:1,1:2,2:1,3:1,4:1}, expected = 6/5 = 1.2.
#   max |count - 1.2| = |2 - 1.2| = 0.8  -> residue_max_dev == 0.8.
# #13 endpoint bias: hits (multiples of 5 among pre survivors) = {25,35}.
#   c(v)=1 iff v-2 or v+2 is a survivor.
#   c_all: endpoints among the 14 pre survivors = 12 (each 2-gap contributes 2
#   endpoints, 6 gaps * 2 = 12, endpoint-disjoint post-filter-3).
#   c_hit: c(25)=1 (23 is survivor), c(35)=1 (37 is survivor) -> c_hit=2.
#   mean_all = 12/14, mean_hit = 2/2 = 1.  bias = |1 - 12/14| = 2/14 = 1/7.


def test_candidate_columns_exact_q7_p5():
    print("test_candidate_columns_exact_q7_p5")
    res = lib.transition(p=5, q=7, primes_below_p=primes_below(5))
    assert abs(res["residue_max_dev"] - 0.8) < 1e-12, f"residue_max_dev==0.8 (#12): {res}"
    assert abs(res["endpoint_bias"] - (1.0 / 7.0)) < 1e-12, f"endpoint_bias==1/7 (#13): {res}"