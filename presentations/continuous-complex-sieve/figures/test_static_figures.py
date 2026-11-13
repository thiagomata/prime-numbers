"""Arithmetic and publication-export checks; run with stdlib unittest."""
import tempfile
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path

import numpy as np
import static_figures as plots


class ArithmeticTests(unittest.TestCase):
    def test_integer_waves_and_activation(self):
        integers = np.arange(-12, 35)
        for modulus in range(2, 13):
            expected = [(int(n) // modulus) * modulus == n for n in integers]
            np.testing.assert_allclose(plots.wave(integers, modulus), expected, atol=1e-13)
        np.testing.assert_allclose(plots.contribution(np.arange(2, 13), 4),
                                   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], atol=1e-13)

    def test_stages_against_proper_divisor_oracle(self):
        integers = np.arange(2, 35)
        for maximum in range(1, 13):
            expected = [plots.integer_height(int(n), maximum) for n in integers]
            np.testing.assert_allclose(plots.height(integers, maximum), expected, atol=1e-12)

    def test_completed_contacts_and_divisor_counts(self):
        window = plots.complete_window(2, 31)
        integers = window["integers"]
        # Full divisor count, independent of the truncated proper-divisor helper.
        tau_minus_two = [sum((int(n) // d) * d == n for d in range(1, int(n) + 1)) - 2
                         for n in integers]
        np.testing.assert_array_equal(window["exact"], tau_minus_two)
        self.assertEqual(integers[window["exact"] == 0].tolist(),
                         [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31])
        self.assertEqual(integers[window["exact_pairs"] == 0].tolist(), [3, 5, 11, 17, 29])
        self.assertEqual([int(n) for n in integers if plots.is_prime(int(n))],
                         integers[window["exact"] == 0].tolist())
        np.testing.assert_allclose(plots.bounded_pair_height(integers, 33),
                                   window["exact_pairs"] > 0, atol=1e-12)

    def test_shifted_stability_and_bounds(self):
        values = plots.sample_grid(2, 31, 17)
        for function in (plots.pair_height, plots.bounded_pair_height):
            np.testing.assert_allclose(function(values, 33), function(values, 37), atol=1e-13)
        bounded = plots.bounded_pair_height(values, 33)
        self.assertTrue(np.all((bounded >= 0) & (bounded <= 1)))
        self.assertGreater(float(plots.bounded_pair_height(3.5, 33)), .99)

    def test_grid_and_argument_validation(self):
        values = plots.sample_grid(2.3, 19.4, 7)
        self.assertTrue(np.all(np.diff(values) > 0))
        self.assertEqual((values[0], values[-1]), (2.3, 19.4))
        self.assertTrue(set(range(3, 20)).issubset(values))
        self.assertEqual(plots.complete_window(2.3, 19.4)["maximum"], 22)
        for invalid in (1, 2.5, True):
            with self.assertRaises(ValueError):
                plots.wave([2], invalid)
        for invalid in (0, 1.5, True):
            with self.assertRaises(ValueError):
                plots.height([2], invalid)
        with self.assertRaises(ValueError):
            plots.sample_grid(3, 2)


class RenderingTests(unittest.TestCase):
    def test_content_and_layout(self):
        figure = plots.contact_figure()
        figure.canvas.draw()
        self.assertEqual(len(figure.axes), 2)
        self.assertIn("Pair start", figure.axes[1].get_xlabel())
        contacts = figure.axes[1].collections[1].get_offsets()
        self.assertEqual(contacts[:, 0].tolist(), [3, 5, 11, 17, 29])
        self.assertTrue(np.all(contacts[:, 1] == 0))
        renderer = figure.canvas.get_renderer()
        for axis in figure.axes:
            bbox = axis.get_tightbbox(renderer)
            self.assertGreaterEqual(bbox.x0, 0)
            self.assertGreaterEqual(bbox.y0, 0)
            self.assertLessEqual(bbox.x1, figure.bbox.width)
            self.assertLessEqual(bbox.y1, figure.bbox.height)
        plots._pyplot().close(figure)

    def test_real_vector_and_preview_exports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = plots.export_figures(root / "previews", root / "vectors")
            self.assertEqual(len(paths), 9)
            for name in plots.FIGURES:
                svg = root / "previews" / f"{name}.svg"
                self.assertTrue(ET.parse(svg).getroot().tag.endswith("svg"))
                self.assertTrue((root / "previews" / f"{name}.png").read_bytes().startswith(b"\x89PNG"))
                pdf = (root / "vectors" / f"{name}.pdf").read_bytes()
                self.assertTrue(pdf.startswith(b"%PDF"))
                self.assertNotIn(b"/Subtype /Image", pdf)


if __name__ == "__main__":
    unittest.main()
