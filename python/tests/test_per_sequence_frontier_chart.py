import pytest

from sieve_sequence import per_sequence_frontier_chart as mod


def test_primes_upto_returns_known_primes():
    assert mod.primes_upto(20) == [2, 3, 5, 7, 11, 13, 17, 19]


def test_primes_upto_handles_edge_cases():
    assert mod.primes_upto(2) == [2]
    assert mod.primes_upto(1) == []


def test_primes_upto_raises_on_zero_input():
    with pytest.raises(IndexError):
        mod.primes_upto(0)


def test_build_series_density_product_matches_hand_derivation():
    stages = [
        {"head": 3, "survivors": list(range(3, 9, 2))},
        {"head": 5, "survivors": list(range(5, 26, 2))},
    ]
    rows = mod.build_series(stages)
    assert rows[0]["main"] == pytest.approx(3.0)
    assert rows[0]["frontier"] == pytest.approx(3.0)
    assert rows[1]["main"] == pytest.approx(10.0 / 3.0)
    assert rows[1]["frontier"] == pytest.approx(10.0 / 3.0)


def test_build_series_counts_2gaps_correctly():
    stages = [
        {"head": 3, "survivors": [3, 5, 7, 9, 11]},
    ]
    rows = mod.build_series(stages)
    assert rows[0]["g2"] == 2