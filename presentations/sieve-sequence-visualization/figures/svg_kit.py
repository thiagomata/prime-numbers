"""Minimal stdlib-only SVG builder for the article diagrams in ../06-article-diagram-ideas.md.

No external dependencies. Each drawing primitive appends a literal SVG tag
string to the canvas, so geometry stays plain data that is easy to hand-tune.
"""

from dataclasses import dataclass, field
from typing import List, Sequence


def escape(text: str) -> str:
    """XML-escape the three characters that are unsafe raw inside SVG text/attributes."""
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


@dataclass
class Canvas:
    """An SVG document under construction: a fixed width/height plus an
    ordered list of element strings, appended to by the draw methods below
    and flattened into a single document by `render`."""

    width: int
    height: int
    font_family: str = "Helvetica, Arial, sans-serif"
    elements: List[str] = field(default_factory=list)

    def line(self, x1, y1, x2, y2, stroke="#222", width=2, dash=None):
        """A straight `<line>` from (x1, y1) to (x2, y2)."""
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        self.elements.append(
            f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" '
            f'stroke="{stroke}" stroke-width="{width}"{dash_attr} />'
        )

    def arrow(self, x1, y1, x2, y2, stroke="#222", width=2, dash=None):
        """Same as `line`, but with an arrowhead marker at (x2, y2)."""
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        self.elements.append(
            f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" '
            f'stroke="{stroke}" stroke-width="{width}"{dash_attr} '
            f'marker-end="url(#arrowhead)" />'
        )

    def polyline(self, points, stroke="#222", width=2, dash=None):
        """An unfilled `<polyline>` through `points` (a sequence of (x, y) pairs)."""
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        pts = " ".join(f"{x},{y}" for x, y in points)
        self.elements.append(
            f'<polyline points="{pts}" fill="none" stroke="{stroke}" '
            f'stroke-width="{width}"{dash_attr} />'
        )

    def circle(self, cx, cy, r=7, fill="white", stroke="#222", width=2):
        """A `<circle>` centered at (cx, cy) with radius r."""
        self.elements.append(
            f'<circle cx="{cx}" cy="{cy}" r="{r}" fill="{fill}" '
            f'stroke="{stroke}" stroke-width="{width}" />'
        )

    def cross(self, cx, cy, size=7, stroke="#c0392b", width=2.5):
        """An X mark (two crossed lines) centered at (cx, cy)."""
        self.elements.append(
            f'<line x1="{cx-size}" y1="{cy-size}" x2="{cx+size}" y2="{cy+size}" '
            f'stroke="{stroke}" stroke-width="{width}" />'
        )
        self.elements.append(
            f'<line x1="{cx-size}" y1="{cy+size}" x2="{cx+size}" y2="{cy-size}" '
            f'stroke="{stroke}" stroke-width="{width}" />'
        )

    def link_text(self, x, y, label, url, size=12, anchor="start", fill="#555", weight="normal"):
        """A clickable, underlined text label wrapped in <a href=...>."""
        self.elements.append(
            f'<a href="{escape(url)}" target="_blank" rel="noopener">'
            f'<text x="{x}" y="{y}" font-family="{self.font_family}" font-size="{size}" '
            f'font-weight="{weight}" fill="{fill}" text-anchor="{anchor}" '
            f'text-decoration="underline">{escape(label)}</text></a>'
        )

    def image(self, x, y, w, h, href, pixelated=True):
        """An `<image>` at (x, y) sized w x h, referencing `href` (a data: URI or path)."""
        style = ' style="image-rendering: pixelated"' if pixelated else ""
        self.elements.append(
            f'<image x="{x}" y="{y}" width="{w}" height="{h}" href="{href}" '
            f'preserveAspectRatio="none"{style} />'
        )

    def rect(self, x, y, w, h, fill="none", stroke="#222", width=2, rx=0):
        """A `<rect>` at (x, y) sized w x h, with corner radius rx."""
        self.elements.append(
            f'<rect x="{x}" y="{y}" width="{w}" height="{h}" fill="{fill}" '
            f'stroke="{stroke}" stroke-width="{width}" rx="{rx}" />'
        )

    def text(self, x, y, label, size=15, anchor="middle", weight="normal", fill="#111", style="normal"):
        """A `<text>` label anchored at (x, y)."""
        self.elements.append(
            f'<text x="{x}" y="{y}" font-family="{self.font_family}" font-size="{size}" '
            f'font-weight="{weight}" font-style="{style}" fill="{fill}" '
            f'text-anchor="{anchor}">{escape(label)}</text>'
        )

    def text_sub(self, x, y, base, sub, size=16, anchor="middle", fill="#111", weight="normal"):
        """Render `base` with a trailing subscript, e.g. text_sub(x, y, "e", "i+1")."""
        sub_size = round(size * 0.62)
        self.elements.append(
            f'<text x="{x}" y="{y}" font-family="{self.font_family}" font-size="{size}" '
            f'font-weight="{weight}" fill="{fill}" text-anchor="{anchor}">'
            f'{escape(base)}<tspan font-size="{sub_size}" dy="{round(size*0.3)}">{escape(sub)}</tspan>'
            f"</text>"
        )

    def table(self, x, y, col_widths: Sequence[int], rows: Sequence[Sequence[str]],
              row_height=32, header=True):
        """A grid of `rows` with per-column widths `col_widths`, drawn as an
        outer rect plus internal gridlines, with the first row bold if `header`."""
        total_w = sum(col_widths)
        total_h = row_height * len(rows)
        self.rect(x, y, total_w, total_h, fill="none", stroke="#222", width=2)
        for i in range(1, len(rows)):
            yy = y + i * row_height
            self.line(x, yy, x + total_w, yy, stroke="#999", width=1)
        cx = x
        for col_width in col_widths[:-1]:
            cx += col_width
            self.line(cx, y, cx, y + total_h, stroke="#999", width=1)
        for row_idx, row in enumerate(rows):
            cx = x
            for col_idx, cell in enumerate(row):
                weight = "bold" if (header and row_idx == 0) else "normal"
                self.text(cx + col_widths[col_idx] / 2,
                           y + row_idx * row_height + row_height / 2 + 5,
                           str(cell), size=14, weight=weight)
                cx += col_widths[col_idx]

    def render(self) -> str:
        """Serialize the accumulated elements into a complete standalone SVG document."""
        body = "\n  ".join(self.elements)
        return (
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.width}" '
            f'height="{self.height}" viewBox="0 0 {self.width} {self.height}">\n'
            "  <defs>\n"
            '    <marker id="arrowhead" markerWidth="10" markerHeight="8" refX="9" refY="4" '
            'orient="auto">\n'
            '      <path d="M0,0 L10,4 L0,8 Z" fill="#222" />\n'
            "    </marker>\n"
            "  </defs>\n"
            f'  <rect x="0" y="0" width="{self.width}" height="{self.height}" fill="white" />\n'
            f"  {body}\n"
            "</svg>\n"
        )


def save(canvas: Canvas, path: str) -> None:
    """Render `canvas` and write the resulting SVG document to `path`."""
    with open(path, "w") as svg_file:
        svg_file.write(canvas.render())
