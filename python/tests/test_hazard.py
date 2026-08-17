"""Green-gate test suite for the fixed-cohort hazard library.

Run:  pytest python/tests/test_hazard.py

The empirical analog of green-to-green: must be green before adding derived columns or chart code.

Hand-derived ground truth matches the verified Q=17 values from test_lineage.py.
"""

from sieve_sequence import lineage as lib
from sieve_sequence import hazard


def test_explicit_cohort_Q17():
    """Explicit cohort transition matches Reading A at every layer for Q=17.

    Hand-derived ground truth (independently verified in test_lineage.py):
      - After filters {2,3}, G_r_window = 45
      - Installing r=5 destroys 18, leaves 27 survivors.
    """
    print("test_explicit_cohort_Q17")
    Q = 17

    # Step 1: initialise cohort after filter 2
    cohort_init = hazard.init_fixed_cohort(Q)
    oracle_init_starts = lib.two_gap_starts(lib.window_survivors(Q, [2]))
    assert set(cohort_init) == set(oracle_init_starts), f"init_fixed_cohort == Reading A (filter 2): init={len(cohort_init)}, oracle={len(oracle_init_starts.tolist())}"

    # Step 2: apply filter 3 via explicit cohort
    destroyed_3, cohort_after_3 = hazard.apply_cohort_filter(cohort_init, 3)
    oracle_after_3 = lib.two_gap_starts(lib.window_survivors(Q, [2, 3]))
    assert set(cohort_after_3) == set(oracle_after_3), f"after filter 3: survivors == Reading A (filters {{2,3}}): cohort={len(cohort_after_3)}, oracle={len(oracle_after_3.tolist())}"
    assert len(destroyed_3) + len(cohort_after_3) == len(cohort_init), f"destroyed + survivors == pre (filter 3): {len(destroyed_3)}+{len(cohort_after_3)} != {len(cohort_init)}"

    # Step 3: apply filter 5 — hand-derived ground truth
    cohort_before_5 = cohort_after_3
    assert len(cohort_before_5) == 45, f"pre-filter cohort size == G_r_window==45 (layer r=5): got {len(cohort_before_5)}"
    destroyed_5, cohort_after_5 = hazard.apply_cohort_filter(cohort_before_5, 5)
    assert len(destroyed_5) == 18, f"destroyed==18: got {len(destroyed_5)}"
    assert len(cohort_after_5) == 27, f"surviving==27: got {len(cohort_after_5)}"
    assert len(destroyed_5) + len(cohort_after_5) == len(cohort_before_5), f"destroyed+surviving==G_r (filter 5): {len(destroyed_5)}+{len(cohort_after_5)} != {len(cohort_before_5)}"


def test_explicit_cohort_Q17_all_layers():
    """Explicit cohort chained through all filters r<Q=17 matches Reading A
    before and after every layer. Verifies exact set equivalence (not just
    counts) at every step."""
    print("test_explicit_cohort_Q17_all_layers")
    Q = 17
    all_below = [2, 3, 5, 7, 11, 13]
    cohort = hazard.init_fixed_cohort(Q)

    for r in [3, 5, 7, 11, 13]:
        below = [p for p in all_below if p < r]
        oracle_before = lib.two_gap_starts(lib.window_survivors(Q, below))
        assert set(cohort) == set(oracle_before), f"before r={r}: cohort == Reading A: cohort={len(cohort)}, oracle={len(oracle_before.tolist())}"

        destroyed, survivors = hazard.apply_cohort_filter(cohort, r)
        assert len(destroyed) + len(survivors) == len(cohort), f"r={r}: destroyed + survivors == pre: {len(destroyed)}+{len(survivors)} != {len(cohort)}"

        oracle_after = lib.two_gap_starts(lib.window_survivors(Q, below + [r]))
        assert set(survivors) == set(oracle_after), f"after r={r}: survivors == Reading A: survivors={len(survivors)}, oracle={len(oracle_after.tolist())}"

        cohort = survivors


def test_explicit_cohort_Q101_all_layers():
    """Explicit cohort chained through all filters r<Q=101 matches Reading A
    before and after every layer. Records runtime for sweep planning."""
    print("test_explicit_cohort_Q101_all_layers")
    import time
    from sympy import primerange

    Q = 101
    t0 = time.time()
    all_below = list(primerange(2, Q))
    cohort = hazard.init_fixed_cohort(Q)

    n_layers = 0
    for r in all_below[1:]:  # skip r=2 (already in init)
        below = [p for p in all_below if p < r]
        oracle_before = lib.two_gap_starts(lib.window_survivors(Q, below))
        assert set(cohort) == set(oracle_before), f"Q=101 before r={r}: cohort == Reading A: cohort={len(cohort)}, oracle={len(oracle_before.tolist())}"

        destroyed, survivors = hazard.apply_cohort_filter(cohort, r)
        assert len(destroyed) + len(survivors) == len(cohort), f"Q=101 r={r}: destroyed + survivors == pre: {len(destroyed)}+{len(survivors)} != {len(cohort)}"

        oracle_after = lib.two_gap_starts(lib.window_survivors(Q, below + [r]))
        assert set(survivors) == set(oracle_after), f"Q=101 after r={r}: survivors == Reading A: survivors={len(survivors)}, oracle={len(oracle_after.tolist())}"

        cohort = survivors
        n_layers += 1

    elapsed = time.time() - t0
    print(f"  Q=101: {n_layers} layers verified in {elapsed:.2f}s")


def test_layer_hazard_row_partition():
    """Per-layer hazard row computes correct destruction partition."""
    print("test_layer_hazard_row_partition")
    Q = 17
    # cohort after filters {2,3}: 45 starts (hand-derived ground truth)
    cohort_after_3 = hazard.init_fixed_cohort(Q)
    _, cohort_after_3 = hazard.apply_cohort_filter(cohort_after_3, 3)
    L_initial = hazard.init_fixed_cohort(Q)
    L_initial_count = len(L_initial)

    row = hazard.layer_hazard_row(cohort_after_3, 5, L_initial_count)
    assert row["destroyed"] + row["L_after"] == row["L_before"], f"destroyed + L_after == L_before: {row['destroyed']}+{row['L_after']} != {row['L_before']}"
    assert row["destroyed"] == 18, f"destroyed==18 (hand-derived): got {row['destroyed']}"
    assert row["L_after"] == 27, f"L_after==27 (hand-derived): got {row['L_after']}"
    assert row["L_before"] == 45, f"L_before==45 (hand-derived): got {row['L_before']}"
    assert row["f_random"] == 2.0 / 5, f"f_random==2/r: got {row['f_random']}"


def test_cumulative_survivor_ratio():
    """The cumulative real hazard gives the exact remaining cohort fraction."""
    print("test_cumulative_survivor_ratio")
    import math

    for Q in [17, 101]:
        rows = hazard.build_hazard_run(Q)
        for row in rows:
            if row["L_after"] == 0:
                assert row["survival_real"] == 0.0, f"Q={Q} r={row['r']}: extinct, survival_real==0: got {row['survival_real']}"
            else:
                expected = math.exp(-row["D_real"])
                assert abs(expected - row["survival_real"]) < 1e-12, f"Q={Q} r={row['r']}: exp(-D_real) == L_after/L_initial: {expected} vs {row['survival_real']}"


def test_random_benchmark_identity():
    """The cumulative random hazard equals the product of neutral factors."""
    print("test_random_benchmark_identity")
    import math

    for Q in [17, 101]:
        rows = hazard.build_hazard_run(Q)
        # independently maintain product of (1 - 2/r)
        prod_neutral = 1.0
        for row in rows:
            r = row["r"]
            prod_neutral *= (1.0 - 2.0 / r)
            expected = math.exp(-row["D_random"])
            assert abs(expected - prod_neutral) < 1e-12, f"Q={Q} r={r}: exp(-D_random) == prod(1-2/r): {expected} vs {prod_neutral}"


def test_csv_round_trip():
    """Round-trip: write CSV, read back, verify key identities."""
    print("test_csv_round_trip")
    import csv
    import io
    import math

    for Q in [17, 101]:
        rows = hazard.build_hazard_run(Q)
        L_initial = rows[0]["L_before"] if rows else 0
        output = io.StringIO()
        writer = csv.DictWriter(output, fieldnames=[
            "Q", "layer", "r", "L_initial", "L_before", "destroyed", "L_after",
            "f_real", "f_random", "w_real", "h_real", "h_random",
            "D_real", "D_random", "excess_hazard", "c_eff",
            "survival_real", "survival_random",
        ])
        writer.writeheader()
        for idx, row in enumerate(rows):
            writer.writerow({
                "Q": Q, "layer": idx, "r": row["r"],
                "L_initial": L_initial,
                "L_before": row["L_before"], "destroyed": row["destroyed"],
                "L_after": row["L_after"],
                "f_real": row["f_real"], "f_random": row["f_random"],
                "w_real": row["w_real"],
                "h_real": row["h_real"], "h_random": row["h_random"],
                "D_real": row["D_real"], "D_random": row["D_random"],
                "excess_hazard": row["excess_hazard"], "c_eff": row["c_eff"],
                "survival_real": row["survival_real"],
                "survival_random": row["survival_random"],
            })
        output.seek(0)
        reader = csv.DictReader(output)
        read_rows = list(reader)

        assert len(read_rows) == len(rows), f"Q={Q}: row count matches: read={len(read_rows)}, built={len(rows)}"

        prev_D_real = 0.0
        prev_D_random = 0.0
        for i, rdict in enumerate(read_rows):
            r = int(rdict["r"])
            L_before = int(rdict["L_before"])
            destroyed = int(rdict["destroyed"])
            L_after = int(rdict["L_after"])
            h_real = float(rdict["h_real"])
            h_random = float(rdict["h_random"])
            D_real = float(rdict["D_real"])
            D_random = float(rdict["D_random"])

            assert destroyed + L_after == L_before, f"Q={Q} r={r}: destroyed+L_after==L_before"
            assert destroyed >= 0, f"Q={Q} r={r}: destroyed>=0"
            assert abs(D_real - (prev_D_real + h_real)) < 1e-12, f"Q={Q} r={r}: D_real==prev+h_real"
            assert abs(D_random - (prev_D_random + h_random)) < 1e-12, f"Q={Q} r={r}: D_random==prev+h_random"

            if destroyed == 0:
                assert h_real == 0.0, f"Q={Q} r={r}: zero destruction -> zero real hazard"

            prev_D_real = D_real
            prev_D_random = D_random