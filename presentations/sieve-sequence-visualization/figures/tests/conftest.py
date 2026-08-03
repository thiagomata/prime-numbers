"""Makes the sibling figure scripts (svg_kit.py, gap_heatmap.py, ...) importable
from this tests/ directory without turning the figures/ directory into a package."""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
