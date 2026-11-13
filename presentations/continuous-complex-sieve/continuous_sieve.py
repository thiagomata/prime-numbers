"""ManimGL visualization of the activated continuous sieve, on [2, 31].

Use --check for numerical validation without importing ManimGL.
Unweighted filters have the same contacts as positive weighted filters.
"""

import json
import sys

import numpy as np


FILTERS = (2, 3, 5)
INTEGERS = np.arange(2, 32)
SAMPLES = np.linspace(2.0, 31.0, 1161)  # Includes every integer exactly.


def detector_squared(t, prime):
    """Squared modulus of the finite roots-of-unity sum; no singular quotient."""
    values = np.asarray(t, dtype=float)
    phases = 2j * np.pi * values[..., None] * np.arange(prime) / prime
    return np.abs(np.exp(phases).mean(axis=-1)) ** 2


def height(t, filters):
    """Imaginary part of Z(t); its real part is t."""
    values = np.asarray(t, dtype=float)
    result = np.sin(np.pi * values) ** 2
    for prime in filters:
        result = result + np.clip(values - prime, 0.0, 1.0) * detector_squared(values, prime)
    return result


def validate():
    """Check contacts against independent integer arithmetic, not a second DFT."""
    failures = []
    integers = np.arange(2, 101)
    for count in range(len(FILTERS) + 1):
        filters = FILTERS[:count]
        expected = np.array([
            sum(n > p and (n // p) * p == n for p in filters)
            for n in integers
        ], dtype=float)
        if not np.allclose(height(integers, filters), expected, atol=1e-10, rtol=0):
            failures.append(f"integer heights disagree at stage {filters}")
        midpoints = INTEGERS[:-1] + 0.5
        if not np.all(height(midpoints, filters) >= 1.0 - 1e-12):
            failures.append(f"noninteger contact at stage {filters}")
    actual = [int(n) for n in INTEGERS if height(n, FILTERS) < 1e-10]
    expected_primes = [
        int(n) for n in INTEGERS
        if all((int(n) // d) * d != n for d in range(2, int(np.sqrt(n)) + 1))
    ]
    if actual != expected_primes:
        failures.append("final contacts disagree with independent primality oracle")
    if not all(np.any(SAMPLES == n) for n in INTEGERS):
        failures.append("plot sampling omits an integer")
    for prime in FILTERS:
        for boundary in (prime, prime + 1):
            near = height(np.array([boundary - 1e-7, boundary, boundary + 1e-7]), (prime,))
            if np.max(np.abs(near - near[1])) > 1e-5:
                failures.append(f"activation continuity check failed at {prime}, {boundary}")
    sampled = height(SAMPLES, FILTERS)
    if not np.all(np.isfinite(sampled) & (sampled >= 0) & (sampled <= 3.5)):
        failures.append("curve exceeds the plotted vertical range")
    if failures:
        raise ValueError("; ".join(failures))
    print(json.dumps({"status": "PASS", "stages": 4, "integer_checks": 396,
                      "final_contacts": actual, "maximum_sampled_height": float(sampled.max())}))


if __name__ == "__main__":
    if sys.argv[1:] == ["--check"]:
        validate()
        sys.exit(0)
    raise SystemExit("Use python continuous_sieve.py --check, or render with manimgl.")


# Manim discovers the module-global Scene subclass when loading this file.
# Numerical validation above needs NumPy only, not an OpenGL context.
from manimlib import (  # noqa: E402
    Scene, Text, VMobject, VGroup, Dot, Line, Circle,
    FadeIn, FadeOut, Transform, ShowCreation,
)


class ContinuousSieve(Scene):
    def construct(self):
        ink = "#E8EDF5"
        muted = "#9CAEC5"
        teal = "#51E0B3"
        coral = "#FF817C"
        gold = "#FFD479"
        grid = "#2B3B50"

        def text(content, size, y, color=ink):
            return Text(content, font="DejaVu Sans", font_size=size, color=color).move_to([0, y, 0])

        def point(t, imaginary):
            return np.array([-5.95 + (t - 2) * 11.9 / 29, -1.65 + imaginary * 0.88, 0])

        def curve(filters, color=teal):
            graph = VMobject(stroke_color=color, stroke_width=2.5)
            graph.set_points_as_corners([point(t, h) for t, h in zip(SAMPLES, height(SAMPLES, filters))])
            return graph

        def markers(filters):
            return VGroup(*[
                Dot(point(n, h), radius=0.043, color=teal if h < 1e-10 else coral)
                for n, h in zip(INTEGERS, height(INTEGERS, filters))
            ])

        self.add(text("A continuous curve that keeps the primes", 39, 3.45))
        self.add(text("Each filter lifts later multiples. The prime itself stays on the real axis.", 21, 2.9, muted))
        self.add(text("Z(t) = t + i [ sin²(πt) + Σ a_p(t) |D_p(t)|² ]", 25, 2.35))

        for imaginary in (1, 2, 3):
            self.add(Line(point(2, imaginary), point(31, imaginary), stroke_color=grid, stroke_width=1))
            self.add(Text(str(imaginary), font_size=18, color=muted).move_to(point(1.2, imaginary)))
        self.add(Line(point(2, 0), point(31.4, 0), stroke_color=ink, stroke_width=1.5))
        self.add(Text("Im Z", font_size=18, color=muted).move_to([-6.25, 1.45, 0]))
        labels = VGroup(*[
            Text(str(n), font_size=17, color=muted).move_to(point(n, 0) + [0, -0.28, 0])
            for n in INTEGERS
        ])
        self.add(labels)
        self.add(text("Real axis  /  candidate value t", 18, -2.3, muted))
        footer = text("Unweighted filters · continuous activation · window 2–31", 17, -3.45, muted)
        self.add(footer)

        stage = text("Start: every integer touches the axis", 24, 1.83, gold)
        caption = text("Between integers, sin²(πt) keeps the curve above the axis.", 23, -2.95)
        graph = curve(())
        dots = markers(())
        self.play(FadeIn(stage), FadeIn(caption), ShowCreation(graph), FadeIn(dots), run_time=2)
        self.wait(2)

        filters = ()
        captions = {
            2: "Keep 2. Lift 4, 6, 8, 10, …",
            3: "Keep 3. Lift 6, 9, 12, 15, …; earlier primes stay put.",
            5: "Keep 5. Lift 10, 15, 20, 25, …; the last new composite is 25.",
        }
        for prime in FILTERS:
            next_filters = filters + (prime,)
            next_stage = text(f"Add the filter for {prime}   |   active filters: " + ", ".join(map(str, next_filters)), 24, 1.83, gold)
            next_caption = text(captions[prime], 23, -2.95)
            halo = Circle(radius=0.13, stroke_color=gold, stroke_width=3).move_to(point(prime, 0))
            self.play(FadeOut(stage), FadeIn(next_stage), FadeOut(caption), FadeIn(next_caption), ShowCreation(halo), run_time=0.7)
            self.play(Transform(graph, curve(next_filters)), Transform(dots, markers(next_filters)), run_time=3)
            self.play(FadeOut(halo), run_time=0.4)
            self.wait(1.5)
            stage, caption, filters = next_stage, next_caption, next_filters

        final_stage = text("Only prime contacts remain in this window", 26, 1.83, teal)
        final_caption = text("2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31", 25, -2.95, teal)
        label_animations = [
            label.animate.set_color(teal if height(n, FILTERS) < 1e-10 else muted)
            for n, label in zip(INTEGERS, labels)
        ]
        self.play(FadeOut(stage), FadeIn(final_stage), FadeOut(caption), FadeIn(final_caption), *label_animations, run_time=1)
        self.wait(4)
