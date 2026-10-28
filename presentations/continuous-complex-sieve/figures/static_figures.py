"""Static illustrations of the continuous divisor-sieve article's definitions.

Curves are finite samples; contact markers use independent integer arithmetic.
Run this file with --help for export options. No Manim dependency is required.
"""

from __future__ import annotations

import argparse
from math import ceil, isqrt
from pathlib import Path

import numpy as np

TEAL = "#007F72"
GOLD = "#A06500"
CORAL = "#C04A46"
GRAY = "#6D7380"


def _integer(value: int, minimum: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, (int, np.integer)) or value < minimum:
        raise ValueError(f"{name} must be an integer at least {minimum}")


def wave(values, modulus: int) -> np.ndarray:
    """W_m = absolute square of a finite exponential mean (no singularity)."""
    _integer(modulus, 2, "modulus")
    values = np.asarray(values, dtype=float)
    phases = 2j * np.pi * values[..., None] * np.arange(modulus) / modulus
    return np.clip(np.abs(np.exp(phases).mean(axis=-1)) ** 2, 0, 1)


def contribution(values, modulus: int) -> np.ndarray:
    values = np.asarray(values, dtype=float)
    return np.clip(values - modulus, 0, 1) * wave(values, modulus)


def height(values, maximum: int) -> np.ndarray:
    _integer(maximum, 1, "maximum")
    values = np.asarray(values, dtype=float)
    result = np.sin(np.pi * values) ** 2
    for modulus in range(2, maximum + 1):
        result = result + contribution(values, modulus)
    return result


def pair_height(values, maximum: int) -> np.ndarray:
    values = np.asarray(values, dtype=float)
    return height(values, maximum) + height(values + 2, maximum)


def bounded_pair_height(values, maximum: int) -> np.ndarray:
    _integer(maximum, 1, "maximum")
    values = np.asarray(values, dtype=float)
    amplitude = np.cos(np.pi * values) ** 2
    for modulus in range(2, maximum + 1):
        amplitude *= (1 - contribution(values, modulus))
        amplitude *= (1 - contribution(values + 2, modulus))
    return np.clip(1 - amplitude, 0, 1)


def sample_grid(lower: float, upper: float, samples_per_unit: int = 160) -> np.ndarray:
    _integer(samples_per_unit, 1, "samples_per_unit")
    if not np.isfinite([lower, upper]).all() or lower < 2 or upper <= lower:
        raise ValueError("require finite 2 <= lower < upper")
    regular = np.linspace(lower, upper, ceil((upper - lower) * samples_per_unit) + 1)
    integers = np.arange(ceil(lower), int(np.floor(upper)) + 1, dtype=float)
    return np.unique(np.concatenate((regular, integers)))


def is_prime(number: int) -> bool:
    return number >= 2 and all(
        (number // divisor) * divisor != number
        for divisor in range(2, isqrt(number) + 1)
    )


def integer_height(number: int, maximum: int) -> int:
    """Independent proper-divisor oracle; not a numerical zero test."""
    return sum(
        (number // divisor) * divisor == number
        for divisor in range(2, min(number - 1, maximum) + 1)
    )


def complete_window(lower: float, upper: float) -> dict:
    values = sample_grid(lower, upper)
    maximum = ceil(upper + 2)
    integers = np.arange(ceil(lower), int(np.floor(upper)) + 1)
    exact = np.array([integer_height(int(n), maximum) for n in integers])
    exact_pairs = np.array([
        integer_height(int(n), maximum) + integer_height(int(n + 2), maximum)
        for n in integers
    ])
    return dict(t=values, maximum=maximum, integers=integers, exact=exact,
                exact_pairs=exact_pairs, h=height(values, maximum),
                pairs=pair_height(values, maximum),
                bounded=bounded_pair_height(values, maximum))


def _pyplot():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({
        "font.family": "serif", "mathtext.fontset": "stix", "font.size": 10,
        "axes.titlesize": 11, "axes.labelsize": 10, "legend.fontsize": 9,
        "svg.fonttype": "path", "pdf.fonttype": 42, "axes.spines.top": False,
        "axes.spines.right": False, "savefig.facecolor": "white",
    })
    return plt


def _axes(axis, lower, upper):
    axis.set_xlim(lower - .35, upper + .35)
    axis.axhline(0, color=GRAY, linewidth=.7)
    axis.grid(axis="y", color="#E2E5E9", linewidth=.6)
    axis.set_axisbelow(True)
    axis.set_xticks(np.arange(ceil(lower), upper + .1, 2))


def _contacts(axis, integers, exact, color):
    accepted = exact == 0
    axis.scatter(integers[~accepted], exact[~accepted], color=CORAL, marker="x",
                 s=24, linewidths=1, zorder=4, label="Rejected integer")
    axis.scatter(integers[accepted], exact[accepted], facecolor="white",
                 edgecolor=color, linewidths=1.3, s=30, zorder=5, label="Zero contact")
    for number in integers[accepted]:
        axis.annotate(str(number), (number, 0), xytext=(0, -12),
                      textcoords="offset points", ha="center", va="top",
                      fontsize=8, color=color)


def activation_figure():
    plt = _pyplot()
    figure, axis = plt.subplots(figsize=(7.2, 3.1), layout="constrained")
    values = sample_grid(2, 12)
    axis.plot(values, wave(values, 4), color=GRAY, linestyle="--", linewidth=1.2,
              label=r"Bare wave $W_4(t)$")
    axis.plot(values, contribution(values, 4), color=TEAL, linewidth=1.5,
              label=r"Activated $a_4(t)W_4(t)$")
    integers = np.arange(2, 13)
    exact = np.array([int(n > 4 and (n // 4) * 4 == n) for n in integers])
    axis.scatter(integers, exact, color=TEAL, s=20, zorder=4)
    for n, label in [(4, "4: protected"), (8, "8: raised"), (12, "12: raised")]:
        axis.annotate(label, (n, int(n > 4)), xytext=(0 if n != 12 else -4, 10),
                      textcoords="offset points", ha="center" if n != 12 else "right", fontsize=9)
    _axes(axis, 2, 12)
    axis.set_ylim(-.12, 1.3)
    axis.set_xlabel(r"Real input $t$")
    axis.set_ylabel("Single-filter contribution")
    axis.set_title("Activation protects the filter's own integer")
    axis.legend(loc="upper center", bbox_to_anchor=(.5, -.23), ncol=2, frameon=False)
    return figure


def contact_figure():
    plt = _pyplot()
    window = complete_window(2, 31)
    figure, axes = plt.subplots(2, 1, figsize=(7.2, 5.5), layout="constrained")
    specifications = [
        (window["h"], window["exact"], TEAL, r"Prime height $h(t)$", "Real input $t$"),
        (window["pairs"], window["exact_pairs"], GOLD,
         r"Twin height $B(t)=h(t)+h(t+2)$", "Pair start $t$ (other endpoint $t+2$)"),
    ]
    for axis, (curve, exact, color, title, xlabel) in zip(axes, specifications):
        axis.plot(window["t"], curve, color=color, linewidth=1.2)
        _contacts(axis, window["integers"], exact, color)
        _axes(axis, 2, 31)
        axis.set_ylim(-.17 * max(curve), 1.16 * max(curve))
        axis.set_title(title)
        axis.set_ylabel("Imaginary height")
        axis.set_xlabel(xlabel)
        axis.legend(loc="upper left", ncol=2, frameon=False)
    return figure


def bounded_figure():
    plt = _pyplot()
    window = complete_window(2, 19)
    figure, axes = plt.subplots(2, 1, figsize=(7.2, 5.3), layout="constrained")
    for axis, curve, exact, title, style in [
        (axes[0], window["pairs"], window["exact_pairs"],
         r"Additive twin height $B(t)$", "-"),
        (axes[1], window["bounded"], (window["exact_pairs"] > 0).astype(int),
         r"Bounded twin height $1-A(t)$", "--"),
    ]:
        axis.plot(window["t"], curve, color=GOLD, linewidth=1.3, linestyle=style)
        _contacts(axis, window["integers"], exact, GOLD)
        _axes(axis, 2, 19)
        axis.set_ylim(-.18 * max(curve), 1.2 * max(curve))
        axis.set_title(title)
        axis.set_ylabel("Imaginary height")
        axis.set_xlabel("Pair start $t$ (other endpoint $t+2$)")
        axis.legend(loc="upper left", ncol=2, frameon=False)
    return figure


FIGURES = {"activated-filter-4": activation_figure,
           "prime-twin-contacts": contact_figure,
           "additive-bounded-twins": bounded_figure}


def export_figures(output_dir: Path, pdf_dir: Path | None = None) -> list[Path]:
    output_dir = Path(output_dir)
    pdf_dir = Path(pdf_dir) if pdf_dir is not None else output_dir
    output_dir.mkdir(parents=True, exist_ok=True)
    pdf_dir.mkdir(parents=True, exist_ok=True)
    outputs = []
    for name, factory in FIGURES.items():
        figure = factory()
        for suffix, directory, metadata in [
            ("svg", output_dir, {"Date": None}),
            ("png", output_dir, None),
            ("pdf", pdf_dir, {"CreationDate": None, "ModDate": None}),
        ]:
            path = directory / f"{name}.{suffix}"
            figure.savefig(path, dpi=200, metadata=metadata)
            outputs.append(path)
        _pyplot().close(figure)
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).parent / "output")
    parser.add_argument("--pdf-dir", type=Path, default=None)
    args = parser.parse_args()
    for path in export_figures(args.output_dir, args.pdf_dir):
        print(path)


if __name__ == "__main__":
    main()
