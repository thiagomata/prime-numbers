import math
import re

import pytest
from sympy import primerange

from sieve_sequence import fixed_lineage_hazard_chart as mod


def _render_sample_svg(tmp_path, monkeypatch):
    monkeypatch.setattr(mod, "OUT_DIR", str(tmp_path))
    monkeypatch.setattr(mod, "DATA_DIR", str(tmp_path))
    rows = (
        "r,excess_hazard,c_eff\n"
        "3,0.5,0.25\n5,0.8,0.3\n7,1.2,0.4\n11,1.6,0.45\n"
        "13,2.0,0.5\n17,2.5,0.55\n19,3.0,0.6\n23,3.5,0.65\n"
    )
    for Q in (17, 101):
        (tmp_path / f"fixed-lineage-hazard-Q{Q}.csv").write_text(rows)
    Q_values = [17, 101]
    all_data = mod.load_rows(Q_values)
    return mod.draw(all_data, Q_values).render()


def test_sparse_log_ticks_keep_endpoints_and_limit_density():
    values = [
        3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
        53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 251, 499,
    ]
    assert mod._sparse_log_ticks(values) == [3, 7, 17, 37, 89, 251, 499]


def test_finite_series_omits_extinction_and_invalid_geometry_values():
    rows = [
        {"r": "3", "excess_hazard": "0.125"},
        {"r": "5", "excess_hazard": "inf"},
        {"r": "7", "excess_hazard": "nan"},
        {"r": "-11", "excess_hazard": "0.5"},
    ]
    assert mod._finite_series(rows, "excess_hazard") == [(3, 0.125)]


def test_draw_rejects_empty_input_explicitly():
    with pytest.raises(ValueError, match="requires at least one data row"):
        mod.draw({}, [])


def test_log_r_reference_matches_known_values():
    assert math.log(3) == pytest.approx(1.0986, abs=1e-4)
    assert math.log(7) == pytest.approx(1.9459, abs=1e-4)
    assert math.log(29) == pytest.approx(3.3673, abs=1e-4)


def test_2_log_r_reference_matches_known_values():
    assert 2 * math.log(3) == pytest.approx(2.1972, abs=1e-4)
    assert 2 * math.log(7) == pytest.approx(3.8918, abs=1e-4)


def test_reference_curves_are_monotone_increasing():
    rs = list(primerange(3, 98))
    log_seq = [math.log(r) for r in rs]
    two_log_seq = [2 * math.log(r) for r in rs]
    for a, b in zip(log_seq[:-1], log_seq[1:]):
        assert b > a
    for a, b in zip(two_log_seq[:-1], two_log_seq[1:]):
        assert b > a


def test_draw_renders_well_formed_svg(tmp_path, monkeypatch):
    svg = _render_sample_svg(tmp_path, monkeypatch)
    assert svg.startswith("<svg "), svg[:80]
    assert svg.rstrip().endswith("</svg>")


def test_draw_explains_panel_roles_and_every_line_style(tmp_path, monkeypatch):
    svg = _render_sample_svg(tmp_path, monkeypatch)
    required_labels = [
        "Observed boundary effect (zoomed)",
        "Distance from comparison scales (normalized)",
        "effective coefficient c_eff",
        "excess / (2 log r)",
        "cohort endpoint",
        "Q=17",
        "Q=101",
        "zero",
        "head scale (c=1/2)",
        "square-window scale (c=1)",
    ]
    assert all(label in svg for label in required_labels)


def test_every_polyline_stays_inside_one_plot_panel(tmp_path, monkeypatch):
    svg = _render_sample_svg(tmp_path, monkeypatch)
    point_groups = re.findall(r'<polyline points="([^"]+)"', svg)
    points = [
        tuple(float(part) for part in point.split(","))
        for group in point_groups
        for point in group.split()
    ]
    panel1 = (mod.PLOT_TOP, mod.PLOT_TOP + mod.PANEL_HEIGHT)
    panel2_top = panel1[1] + mod.PANEL_GAP
    panel2 = (panel2_top, panel2_top + mod.PANEL_HEIGHT)
    assert all(
        mod.PLOT_LEFT <= x <= mod.PLOT_LEFT + mod.PLOT_WIDTH
        and (panel1[0] <= y <= panel1[1] or panel2[0] <= y <= panel2[1])
        for x, y in points
    )


def test_svg_provenance_is_repository_relative_and_deterministic(tmp_path, monkeypatch):
    svg = _render_sample_svg(tmp_path, monkeypatch)
    assert (
        "Input: data/candidates/fixed-lineage-hazard-Q17.csv" in svg
        and "Formula: excess_hazard = D_real - D_random" in svg
        and "Formula: c_eff = excess_hazard / (2 log r)" in svg
        and "Generated:" not in svg
        and "Git commit:" not in svg
        and "/Users/" not in svg
    )


def test_data_path_returns_correct_filename():
    assert mod.data_path(17).endswith("fixed-lineage-hazard-Q17.csv")
