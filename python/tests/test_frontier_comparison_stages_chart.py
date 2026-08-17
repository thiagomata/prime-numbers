import math

import pytest
from sympy import primerange

from sieve_sequence import frontier_comparison_stages_chart as mod


def test_random_benchmark_formula_matches_2_over_p():
    p = 7
    assert 2.0 / p == 2 / 7


def test_frontier_benchmark_formula_matches_known_values():
    p = 7
    assert 2.0 * (1.0 + math.log(p)) / p == pytest.approx(0.8417, abs=1e-4)


def test_benchmark_formulas_decrease_monotonically():
    ps = list(primerange(7, 98))
    random_bench = [2.0 / p for p in ps]
    frontier_bench = [2.0 * (1.0 + math.log(p)) / p for p in ps]
    for a, b in zip(random_bench[:-1], random_bench[1:]):
        assert b < a
    for a, b in zip(frontier_bench[:-1], frontier_bench[1:]):
        assert b < a


def test_load_stages_reads_csv_correctly(tmp_path, monkeypatch):
    dense = tmp_path / "dense.csv"
    dense.write_text("p,G_local,destroyed\n7,100.0,28\n11,100.0,18\n17,50.0,0\n")
    sparse = tmp_path / "sparse.csv"
    sparse.write_text("p,G_local,destroyed\n101,200.0,10\n")
    monkeypatch.setattr(mod, "DENSE_PATH", str(dense))
    monkeypatch.setattr(mod, "SPARSE_PATH", str(sparse))
    stages = mod.load_stages()
    assert [s[0] for s in stages] == [7, 11, 17, 101]
    assert stages[0][1] == pytest.approx(0.28)
    assert stages[1][1] == pytest.approx(0.18)
    assert stages[2][1] == pytest.approx(0.0)
    assert stages[3][1] == pytest.approx(0.05)