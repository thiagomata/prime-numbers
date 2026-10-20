"""Exact filter-7 transition: pair contacts, focused cells, separator histogram."""

from collections import Counter
from math import gcd
import json
import sys

import numpy as np


PERIOD = 210
OLD_FILTERS = (2, 3, 5)
NEW_FILTERS = (2, 3, 5, 7)
ZOOM = np.linspace(41.0, 101.0, 2401)


def detector(t, prime):
    values = np.asarray(t, dtype=float)
    return np.abs(np.exp(2j * np.pi * values[..., None] * np.arange(prime) / prime).mean(axis=-1)) ** 2


def height(t, filters):
    values = np.asarray(t, dtype=float)
    result = np.sin(np.pi * values) ** 2
    for prime in filters:
        result = result + np.clip(values - prime, 0, 1) * detector(values, prime)
    return result


def pair_height(t, filters):
    return height(t, filters) + height(np.asarray(t) + 2, filters)


def pair_starts(filters):
    return [n for n in range(11, 221) if all(gcd(n * (n + 2), p) == 1 for p in filters)]


def separators(starts):
    return [b - a - 2 for a, b in zip(starts, starts[1:] + [starts[0] + PERIOD])]


def bad_separator(run):
    return any(gcd(run + shift, 7) == 7 for shift in (0, 2, 4))


def validate():
    failures = []
    expected_histograms = ({4: 7, 10: 14}, {4: 3, 10: 8, 16: 2, 28: 2})
    for filters, expected in zip((OLD_FILTERS, NEW_FILTERS), expected_histograms):
        starts = pair_starts(filters)
        runs = separators(starts)
        numerical = [n for n in range(11, 221) if pair_height(n, filters) < 1e-10]
        if numerical != starts or dict(Counter(runs)) != expected:
            failures.append(f"contacts/histogram mismatch for {filters}")
        if sum(r + 2 for r in runs) != PERIOD or any((r - 4) // 6 * 6 != r - 4 for r in runs):
            failures.append("cyclic separator reconstruction/phase mismatch")
        if not np.all(pair_height(np.arange(41, 101) + 0.5, filters) >= 2 - 1e-10):
            failures.append("noninteger midpoint contacts")
    old, new = pair_starts(OLD_FILTERS), pair_starts(NEW_FILTERS)
    runs = separators(old)
    lost = set(old) - set(new)
    bad_count = sum(map(bad_separator, runs))
    for index, run in enumerate(runs):
        mask = sum(float(detector(run + shift, 7)) for shift in (0, 2, 4))
        if abs(mask - int(bad_separator(run))) > 1e-10:
            failures.append("analytic bad-channel mask disagrees with gcd")
        next_start = old[(index + 1) - len(old) * ((index + 1) // len(old))]
        if old[index] in lost and next_start in lost and not bad_separator(run):
            failures.append("double destruction across a good separator")
    bound = (len(old) - bad_count + 1) // 2
    if len(old) != 21 or len(new) != 15 or len(lost) != 6 or bad_count != 14 or bound != 4:
        failures.append("pinned transition counts mismatch")
    if len(new) < bound or sorted(n for n in lost if 41 <= n <= 101) != [47, 77, 89]:
        failures.append("survival bound/zoom loss mismatch")
    if not all(np.any(ZOOM == n) for n in range(41, 102)):
        failures.append("integer samples omitted")
    if float(np.max(pair_height(ZOOM, NEW_FILTERS))) > 7:
        failures.append("curve exceeds plot height")
    if failures:
        raise ValueError("; ".join(failures))
    print(json.dumps({"status": "PASS", "before": len(old), "after": len(new),
                      "lost": sorted(lost), "bad_separators": bad_count,
                      "survival_lower_bound": bound, "histograms": expected_histograms}))


if __name__ == "__main__":
    if sys.argv[1:] == ["--check"]:
        validate()
        sys.exit(0)
    raise SystemExit("Use --check, or render this scene with manimgl.")


from manimlib import (  # noqa: E402
    Scene, Text, VMobject, VGroup, Dot, Line, Rectangle,
    FadeIn, FadeOut, Transform, ShowCreation,
)


class TwoGapFocused(Scene):
    def construct(self):
        white, muted = "#E8EDF5", "#9CAEC5"
        teal, coral, gold, blue = "#51E0B3", "#FF817C", "#FFD479", "#7EB9F5"
        old, new = pair_starts(OLD_FILTERS), pair_starts(NEW_FILTERS)
        lost = set(old) - set(new)

        def label(content, size, x, y, color=white):
            return Text(content, font="DejaVu Sans", font_size=size).set_color(color).move_to([x, y, 0])

        def point(t, h):
            return np.array([-6 + (t - 41) / 5, 0.3 + 0.23 * h, 0])

        def graph(filters):
            result = VMobject(stroke_color=teal, stroke_width=2)
            result.set_points_as_corners([point(t, h) for t, h in zip(ZOOM, pair_height(ZOOM, filters))])
            return result

        def dots(filters):
            return VGroup(*[
                Dot(point(n, pair_height(n, filters)), radius=0.045).set_color(teal)
                for n in old if 41 <= n <= 101
            ])

        def focused(starts, highlight_bad=False, highlight_lost=False):
            result = VGroup()
            runs = separators(starts)
            width = 12.6 / (2 * len(starts))
            for index, (start, run) in enumerate(zip(starts, runs)):
                colors = (coral if highlight_lost and start in lost else teal,
                          coral if highlight_bad and bad_separator(run) else blue)
                for offset, value in enumerate((2, run)):
                    x = -6.3 + (2 * index + offset + 0.5) * width
                    color = colors[offset]
                    box = Rectangle(width=width - 0.025, height=0.34,
                                    stroke_color=color, stroke_width=1,
                                    fill_color=color, fill_opacity=0.16).move_to([x, -0.85, 0])
                    result.add(box, label(str(value), 15, x, -0.85, color))
            return result

        def histogram(starts, highlight=False):
            counts = Counter(separators(starts))
            result = VGroup()
            for run, x in zip((4, 10, 16, 28), (-4.5, -1.5, 1.5, 4.5)):
                count = counts.get(run, 0)
                color = coral if highlight and bad_separator(run) else blue
                bar_height = max(0.012, count * 0.075)
                result.add(Rectangle(width=1.3, height=bar_height,
                                     stroke_color=color, fill_color=color,
                                     fill_opacity=0.65).move_to([x, -2.95 + bar_height / 2, 0]))
                result.add(label(str(count), 23, x, -2.78 + bar_height, color))
                result.add(label(f"R = {run}", 21, x, -3.18))
            return result

        self.add(label("Following the 2-gaps through a filter", 37, 0, 3.55))
        self.add(label("Pair contacts  +  ordered focused cells  +  separator distribution", 22, 0, 3.05, muted))
        stage = label("Before filter 7: 21 two-gaps in the expanded period", 26, 0, 2.58, teal)
        self.add(stage)
        self.add(label("T(t) = t + i [ H(t) + H(t+2) ]     |     curve zoom: 41–101", 22, 0, 2.12))
        self.add(Line(point(41, 0), point(101, 0), stroke_color=muted, stroke_width=1))
        self.add(label("Im T", 17, -6.45, 1.65, muted))
        for n in (41, 47, 59, 71, 77, 89, 101):
            self.add(label(str(n), 19, point(n, 0)[0], 0.02, muted))
        self.add(label("Ordered focused cycle: [2, R, 2, R, …]   |   complete period: [11, 221)", 21, 0, -0.4))
        self.add(label("Separator histogram   |   same complete period, including cyclic wrap", 21, 0, -1.45))
        caption = label("Filters 2, 3, 5 are installed. Green cells are 2-gaps; blue cells are separators.", 19, 0, -3.72)
        curve, contacts = graph(OLD_FILTERS), dots(OLD_FILTERS)
        row, bars = focused(old), histogram(old)
        self.play(ShowCreation(curve), FadeIn(contacts), FadeIn(row), FadeIn(bars), FadeIn(caption), run_time=2)
        self.wait(3)

        danger = label("Incoming 7: R = 10 is bad; R = 4 is good", 26, 0, 2.58, gold)
        explanation = label("Bad means 7 divides R, R+2 or R+4. It permits double deletion; it does not force it.", 19, 0, -3.72)
        self.play(FadeOut(stage), FadeIn(danger), FadeOut(caption), FadeIn(explanation),
                  Transform(row, focused(old, highlight_bad=True)), Transform(bars, histogram(old, highlight=True)), run_time=1.5)
        self.wait(4)

        actual = label("Six 2-gaps are hit. The curve zoom shows starts 47, 77 and 89 lifting away.", 19, 0, -3.72)
        marked = dots(OLD_FILTERS)
        for n, dot in zip((n for n in old if 41 <= n <= 101), marked):
            if n in lost:
                dot.set_color(coral)
        self.play(FadeOut(explanation), FadeIn(actual), Transform(contacts, marked),
                  Transform(row, focused(old, highlight_bad=True, highlight_lost=True)), run_time=1)
        self.wait(2)
        lifted = dots(NEW_FILTERS)
        for n, dot in zip((n for n in old if 41 <= n <= 101), lifted):
            if n in lost:
                dot.set_color(coral)
        self.play(Transform(curve, graph(NEW_FILTERS)), Transform(contacts, lifted), run_time=4)
        self.wait(1)

        final = label("After filter 7: 15 two-gaps remain; separators merge and redistribute", 25, 0, 2.58, teal)
        final_caption = label("14 bad / 21 separators guarantee at least 4 survivors. Exact result: 15 survive.", 19, 0, -3.72)
        next_row, next_bars = focused(new), histogram(new)
        self.play(FadeOut(danger), FadeIn(final), FadeOut(actual), FadeIn(final_caption),
                  FadeOut(row), FadeIn(next_row), FadeOut(bars), FadeIn(next_bars), run_time=1.5)
        self.wait(5)
