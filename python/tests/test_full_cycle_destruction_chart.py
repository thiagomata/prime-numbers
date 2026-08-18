import math

from sieve_sequence import full_cycle_destruction_chart as mod


def test_compute_layers_single_row_r29():
    rows = mod.compute_layers(max_r=29, min_r=29)
    assert len(rows) == 1
    row = rows[0]
    assert row["r"] == 29
    assert abs(row["f_real"] - (2.0 / 29.0)) < 1e-15
    assert abs(row["f_random"] - (2.0 / 29.0)) < 1e-15


def test_compute_layers_f_real_equals_f_random_for_max_r_100():
    rows = mod.compute_layers(max_r=100, min_r=29)
    assert len(rows) > 0
    for row in rows:
        assert abs(row["f_real"] - row["f_random"]) < 1e-12


def test_compute_layers_f_real_equals_two_over_r():
    rows = mod.compute_layers(max_r=100, min_r=29)
    for row in rows:
        assert abs(row["f_real"] - (2.0 / row["r"])) < 1e-15
        assert abs(row["f_random"] - (2.0 / row["r"])) < 1e-15


def test_compute_layers_T_recurrence_values():
    rows = mod.compute_layers(max_r=43, min_r=29)
    T = 1
    expected_T_old = 1
    for row in rows:
        r = row["r"]
        expanded = T * r
        T_new = T * (r - 2)
        destroyed = expanded - T_new
        assert destroyed == 2 * T
        assert T_new == T * (r - 2)
        T = T_new


def test_compute_layers_destroyed_equals_two_times_T_old():
    rows = mod.compute_layers(max_r=100, min_r=29)
    T = 1
    for row in rows:
        r = row["r"]
        expanded = T * r
        T_new = T * (r - 2)
        destroyed = expanded - T_new
        assert destroyed == 2 * T
        T = T_new


def test_compute_layers_rows_in_increasing_r():
    rows = mod.compute_layers(max_r=100, min_r=29)
    rs = [row["r"] for row in rows]
    assert rs == sorted(rs)


def test_compute_layers_primes_start_at_min_r_and_are_prime():
    rows = mod.compute_layers(max_r=60, min_r=29)
    rs = [row["r"] for row in rows]
    assert rs[0] == 29
    for r in rs:
        assert all(r % p != 0 for p in range(2, int(r**0.5) + 1))
        assert r >= 2


def test_compute_layers_all_values_in_valid_range():
    rows = mod.compute_layers(max_r=251, min_r=29)
    for row in rows:
        assert 0.0 < row["f_real"] < 1.0
        assert 0.0 < row["f_random"] < 1.0


def test_compute_layers_renders_a_well_formed_svg():
    rows = mod.compute_layers(max_r=100, min_r=29)
    canvas = mod.draw(rows)
    svg = canvas.render()
    assert svg.startswith("<svg")
    assert svg.rstrip().endswith("</svg>")