import math

from sieve_sequence import full_cycle_survival_chart as mod


def test_compute_layers_single_row_r29():
    rows = mod.compute_layers(max_r=29, min_r=29)
    assert len(rows) == 1
    row = rows[0]
    assert row["r"] == 29
    assert abs(row["survival"] - (1.0 - 2.0 / 29.0)) < 1e-15
    assert abs(row["frontier"] - (1.0 - 2.0 * (1.0 + math.log(29)) / 29.0)) < 1e-15


def test_compute_layers_survival_matches_27_over_29():
    rows = mod.compute_layers(max_r=29, min_r=29)
    assert abs(rows[0]["survival"] - (27.0 / 29.0)) < 1e-15
    assert round(rows[0]["survival"], 10) == round(27.0 / 29.0, 10)


def test_compute_layers_frontier_to_10_decimals():
    rows = mod.compute_layers(max_r=29, min_r=29)
    expected = 1.0 - 2.0 * (1.0 + math.log(29)) / 29.0
    assert round(rows[0]["frontier"], 10) == round(expected, 10)


def test_compute_layers_survival_monotonically_decreasing():
    rows = mod.compute_layers(max_r=100, min_r=29)
    survivals = [row["survival"] for row in rows]
    assert all(
        survivals[i] < survials_prev
        for i, survials_prev in enumerate(survivals[:-1], start=1)
    )


def test_compute_layers_all_values_in_unit_interval():
    rows = mod.compute_layers(max_r=251, min_r=29)
    for row in rows:
        assert 0.0 < row["survival"] < 1.0
        assert 0.0 < row["frontier"] < 1.0


def test_compute_layers_primes_start_at_min_r_and_are_prime():
    rows = mod.compute_layers(max_r=60, min_r=29)
    rs = [row["r"] for row in rows]
    assert rs[0] == 29
    for r in rs:
        assert all(r % p != 0 for p in range(2, int(r**0.5) + 1))
        assert r >= 2


def test_compute_layers_rows_in_increasing_r():
    rows = mod.compute_layers(max_r=100, min_r=29)
    rs = [row["r"] for row in rows]
    assert rs == sorted(rs)


def test_compute_layers_renders_a_well_formed_svg():
    rows = mod.compute_layers(max_r=100, min_r=29)
    canvas = mod.draw(rows)
    svg = canvas.render()
    assert svg.startswith("<svg")
    assert svg.rstrip().endswith("</svg>")