import math

from sieve_sequence import full_cycle_hazard_chart as mod


def test_compute_layers_max_r_7_returns_three_rows():
    rows = mod.compute_layers(max_r=7)
    assert len(rows) == 3
    assert [row["r"] for row in rows] == [3, 5, 7]


def test_compute_layers_f_real_equals_f_random_equals_two_over_r():
    rows = mod.compute_layers(max_r=100)
    assert len(rows) > 0
    for row in rows:
        assert abs(row["f_real"] - row["f_random"]) < 1e-12
        assert abs(row["f_real"] - (2.0 / row["r"])) < 1e-15


def test_compute_layers_survival_telescopes_to_one_over_r():
    rows = mod.compute_layers(max_r=7)
    by_r = {row["r"]: row["survival"] for row in rows}
    assert abs(by_r[3] - (1.0 / 3.0)) < 1e-12
    assert abs(by_r[5] - (1.0 / 5.0)) < 1e-12
    assert abs(by_r[7] - (1.0 / 7.0)) < 1e-12
    manual = (1.0 - 2.0 / 3.0) * (1.0 - 2.0 / 5.0) * (1.0 - 2.0 / 7.0)
    assert abs(manual - (1.0 / 7.0)) < 1e-12


def test_compute_layers_T_values():
    rows = mod.compute_layers(max_r=7)
    assert rows[0]["T_old"] == 1
    assert rows[0]["T_new"] == 1
    assert rows[1]["T_old"] == 1
    assert rows[1]["T_new"] == 3
    assert rows[2]["T_old"] == 3
    assert rows[2]["T_new"] == 15


def test_compute_layers_destroyed_equals_two_times_T_old():
    rows = mod.compute_layers(max_r=100)
    for row in rows:
        destroyed = row["T_old"] * row["r"] - row["T_new"]
        assert destroyed == 2 * row["T_old"]


def test_compute_layers_row_r3_expanded_and_f_real():
    rows = mod.compute_layers(max_r=7)
    row = rows[0]
    assert row["r"] == 3
    assert row["T_old"] == 1
    assert row["T_new"] == 1
    assert row["T_old"] * row["r"] == 3
    assert row["T_old"] * row["r"] - row["T_new"] == 2
    assert abs(row["f_real"] - (2.0 / 3.0)) < 1e-15


def test_compute_layers_survival_monotonically_decreasing():
    rows = mod.compute_layers(max_r=251)
    survivals = [row["survival"] for row in rows]
    assert all(
        survivals[i] < survivals[i - 1] for i in range(1, len(survivals))
    )


def test_compute_layers_all_survival_values_in_unit_interval():
    rows = mod.compute_layers(max_r=251)
    for row in rows:
        assert 0.0 < row["survival"] < 1.0


def test_compute_layers_starts_from_prime_3():
    rows = mod.compute_layers(max_r=20)
    rs = [row["r"] for row in rows]
    assert rs[0] == 3
    for r in rs:
        assert all(r % p != 0 for p in range(2, int(r**0.5) + 1))
        assert r >= 2


def test_compute_layers_rows_in_increasing_r():
    rows = mod.compute_layers(max_r=100)
    rs = [row["r"] for row in rows]
    assert rs == sorted(rs)


def test_compute_layers_renders_a_well_formed_svg():
    rows = mod.compute_layers(max_r=100)
    canvas = mod.draw(rows)
    svg = canvas.render()
    assert svg.startswith("<svg")
    assert svg.rstrip().endswith("</svg>")