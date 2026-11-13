"""All-integer filters: exact limiting prime and twin-contact curves on [2,31]."""

import json
import sys

import numpy as np


MAX_FILTER = 32
GRID = np.linspace(2.0, 31.0, 1161)
INTEGERS = np.arange(2, 32)


def contribution(t, modulus):
    values = np.asarray(t, dtype=float)
    detector = np.exp(2j * np.pi * values[..., None] * np.arange(modulus) / modulus).mean(axis=-1)
    return np.clip(values - modulus, 0, 1) * np.abs(detector) ** 2


def stages(t, maximum=MAX_FILTER):
    """Entry M-1 is h_M; first entry is the empty-filter height h_1."""
    values = np.asarray(t, dtype=float)
    result = [np.sin(np.pi * values) ** 2]
    for modulus in range(2, maximum + 1):
        result.append(result[-1] + contribution(values, modulus))
    return np.asarray(result)


def is_prime(n):
    return n >= 2 and all((n // d) * d != n for d in range(2, int(np.sqrt(n)) + 1))


def validate():
    failures = []
    values = np.arange(2, 34)
    computed = stages(values)
    previous_prime_contacts = previous_pair_contacts = None
    for modulus, row in enumerate(computed, start=1):
        expected = np.array([
            sum((int(n) // d) * d == n for d in range(2, min(modulus, int(n) - 1) + 1))
            for n in values
        ])
        if not np.allclose(row, expected, atol=1e-10, rtol=0):
            failures.append(f"proper-divisor oracle mismatch at stage {modulus}")
        prime_contacts = tuple(int(n) for n, h in zip(INTEGERS, row[:30]) if h < 1e-10)
        pair_contacts = tuple(int(n) for n, h in zip(INTEGERS, row[:30] + row[2:]) if h < 1e-10)
        if modulus >= 4 and not is_prime(modulus):
            if prime_contacts != previous_prime_contacts or pair_contacts != previous_pair_contacts:
                failures.append(f"composite {modulus} removed a contact")
        previous_prime_contacts, previous_pair_contacts = prime_contacts, pair_contacts
    expected_primes = tuple(int(n) for n in INTEGERS if is_prime(int(n)))
    expected_twins = tuple(int(n) for n in INTEGERS if is_prime(int(n)) and is_prime(int(n) + 2))
    if previous_prime_contacts != expected_primes or previous_pair_contacts != expected_twins:
        failures.append("final contacts disagree with independent primality oracle")
    if expected_twins != (3, 5, 11, 17, 29):
        failures.append("pinned twin starts mismatch")
    complete_counts = np.array([
        sum((int(n) // d) * d == n for d in range(1, int(n) + 1)) - 2
        for n in values
    ])
    if not np.allclose(computed[-1], complete_counts, atol=1e-10, rtol=0):
        failures.append("final tau(n)-2 identity mismatch")
    for modulus in range(2, 33):
        for boundary in (modulus, modulus + 1):
            near = contribution(np.array([boundary - 1e-7, boundary, boundary + 1e-7]), modulus)
            if np.max(np.abs(near - near[1])) > 1e-5:
                failures.append(f"activation discontinuity at {modulus}")
    upper, shifted = stages(GRID), stages(GRID + 2)
    lower = upper + shifted
    if np.max(upper) > 7 or np.max(lower) > 12 or np.min(upper) < 0:
        failures.append("plot bounds exceeded")
    if not all(np.any(GRID == n) for n in INTEGERS):
        failures.append("integer omitted from plot sampling")
    if not np.all(stages(np.arange(2, 33) + 0.5) >= 1 - 1e-10):
        failures.append("noninteger midpoint contact")
    if not np.array_equal(stages(GRID, 35)[-1], upper[-1]):
        failures.append("upper limit not locally stabilized")
    if not np.array_equal(stages(GRID + 2, 35)[-1], shifted[-1]):
        failures.append("lower endpoint limit not locally stabilized")
    if failures:
        raise ValueError("; ".join(failures))
    print(json.dumps({"status": "PASS", "integer_stage_checks": int(computed.size),
                      "prime_contacts": expected_primes, "twin_starts": expected_twins,
                      "maximum_heights": [float(upper.max()), float(lower.max())],
                      "final_filter": MAX_FILTER}))


if __name__ == "__main__":
    if sys.argv[1:] == ["--check"]:
        validate()
        sys.exit(0)
    raise SystemExit("Use --check, or render with manimgl.")


from manimlib import (  # noqa: E402
    Scene, Text, VMobject, VGroup, Dot, Line,
    FadeIn, FadeOut, Transform, ShowCreation,
)


class UniformPrimeTwins(Scene):
    def construct(self):
        white, muted = "#E8EDF5", "#9CAEC5"
        teal, gold, coral, grid_color = "#51E0B3", "#FFD479", "#FF817C", "#293A50"
        upper = stages(GRID)
        lower = upper + stages(GRID + 2)
        integer_heights = stages(np.arange(2, 34))

        def text(content, size, y, color=white, x=0):
            return Text(content, font="DejaVu Sans", font_size=size).set_color(color).move_to([x, y, 0])

        def point(t, h, pair=False):
            baseline, scale = (-2.4, 0.13) if pair else (0.45, 0.16)
            return np.array([-5.9 + (t - 2) * 11.8 / 29, baseline + scale * h, 0])

        def curve(index, pair=False):
            graph = VMobject(stroke_color=gold if pair else teal, stroke_width=2.5)
            heights = lower[index] if pair else upper[index]
            graph.set_points_as_corners([point(t, h, pair) for t, h in zip(GRID, heights)])
            return graph

        def contact_dots(index, pair=False):
            heights = integer_heights[index, :30].copy()
            if pair:
                heights += integer_heights[index, 2:]
            color = gold if pair else teal
            result = VGroup()
            for n, h in zip(INTEGERS, heights):
                dot = Dot(point(n, h, pair), radius=0.04).set_color(color if h < 1e-10 else coral)
                dot.set_opacity(1 if h < 1e-10 else 0.4)
                result.add(dot)
            return result

        def explanation(modulus):
            if not is_prime(modulus):
                return "Composite step: heights change, but no new integer contacts disappear."
            if modulus <= 5:
                return f"Top panel: the first newly removed value is {modulus} squared = {modulus * modulus}."
            return f"Top-panel removals begin at {modulus * modulus}, outside this window."

        self.add(text("Primes and twins from one uniform rule", 38, 3.55))
        self.add(text("Every integer is a filter: 2, 3, 4, 5, 6, 7, …, 32", 23, 3.08, muted))
        stage = text("Start: no filters applied", 27, 2.66)
        caption = text("Real-axis contacts are candidates until enough divisors have been checked.", 21, 2.23, muted)
        self.add(stage, caption)
        self.add(text("PRIME CONTACTS       F_M(t) = t + i h_M(t)", 25, 1.83, teal))
        self.add(text("TWIN STARTS       T_M(t) = t + i [ h_M(t) + h_M(t+2) ]", 25, -0.66, gold))
        self.add(text("Top: a prime value. Bottom: start n of the pair (n, n+2).", 18, -3.58, muted))

        labels = []
        for pair, ticks in ((False, (0, 2, 4, 6)), (True, (0, 4, 8, 12))):
            for tick in ticks:
                self.add(Line(point(2, tick, pair), point(31, tick, pair),
                              stroke_color=muted if tick == 0 else grid_color,
                              stroke_width=1.2 if tick == 0 else 0.6))
                self.add(text(str(tick), 15, point(2, tick, pair)[1], muted, -6.23))
            row = VGroup(*[
                text(str(n), 16, point(n, 0, pair)[1] - 0.24, muted, point(n, 0, pair)[0])
                for n in INTEGERS
            ])
            labels.append(row)
            self.add(row)
        prime_summary = text("All integers are initial contacts", 20, -0.15, muted)
        twin_summary = text("The pair curve requires both endpoint heights to vanish", 20, -3.01, muted)
        self.add(prime_summary, twin_summary)
        prime_curve, pair_curve = curve(0), curve(0, True)
        prime_dots, pair_dots = contact_dots(0), contact_dots(0, True)
        self.play(ShowCreation(prime_curve), ShowCreation(pair_curve), FadeIn(prime_dots), FadeIn(pair_dots), run_time=2)
        self.wait(2)

        for modulus in range(2, MAX_FILTER + 1):
            index = modulus - 1
            next_stage = text(f"Apply integer filter {modulus}     |     all filters 2 through {modulus}", 26, 2.66)
            next_caption = text(explanation(modulus), 21, 2.23, teal if is_prime(modulus) else gold)
            self.play(FadeOut(stage), FadeIn(next_stage), FadeOut(caption), FadeIn(next_caption),
                      Transform(prime_curve, curve(index)), Transform(pair_curve, curve(index, True)),
                      Transform(prime_dots, contact_dots(index)), Transform(pair_dots, contact_dots(index, True)),
                      run_time=1.25 if modulus <= 10 else 0.4)
            stage, caption = next_stage, next_caption
            if modulus <= 6:
                self.wait(0.75)

        final_stage = text("Exact limiting curves on the displayed interval 2–31", 27, 2.66, teal)
        final_caption = text("Integer contacts settled after filter 5 here; later filters changed the heights.", 21, 2.23, muted)
        final_primes = text("Primes: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31", 21, -0.15, teal)
        final_twins = text("Twin starts: 3, 5, 11, 17, 29   →   (3,5), (5,7), (11,13), (17,19), (29,31)", 21, -3.01, gold)
        changes = []
        for pair, row in zip((False, True), labels):
            for n, label in zip(INTEGERS, row):
                survives = is_prime(int(n)) and (not pair or is_prime(int(n) + 2))
                changes.append(label.animate.set_color((gold if pair else teal) if survives else muted))
        self.play(FadeOut(stage), FadeIn(final_stage), FadeOut(caption), FadeIn(final_caption),
                  FadeOut(prime_summary), FadeIn(final_primes), FadeOut(twin_summary), FadeIn(final_twins),
                  *changes, run_time=1.5)
        self.wait(6)
