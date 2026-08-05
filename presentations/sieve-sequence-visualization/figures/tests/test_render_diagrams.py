import render_diagrams as rd
from svg_kit import Canvas


def test_diagrams_dict_covers_all_ten_named_diagrams():
    assert sorted(rd.DIAGRAMS) == [f"{i:02d}-{suffix}" for i, suffix in enumerate([
        "copy-or-merge-strip", "repeated-period-before-filtering",
        "candidate-composite-certified", "safe-zone-boundary",
        "full-period-vs-local-window", "two-gap-descendant-fan",
        "two-focused-compression", "stage-summary-ladder",
        "rotation-is-change-of-view", "article-figure-map",
    ], start=1)]


def test_every_diagram_builds_a_nonempty_canvas():
    for name, build in rd.DIAGRAMS.items():
        canvas = build()
        assert isinstance(canvas, Canvas), f"{name} did not return a Canvas"
        assert canvas.width > 0 and canvas.height > 0, f"{name} has zero size"
        assert canvas.elements, f"{name} drew nothing"


def test_every_diagram_renders_to_a_well_formed_svg_document():
    for name, build in rd.DIAGRAMS.items():
        svg = build().render()
        assert svg.startswith("<svg "), f"{name}'s render() didn't start with <svg"
        assert svg.rstrip().endswith("</svg>"), f"{name}'s render() didn't close </svg>"


def test_diagram_10_article_figure_map_has_one_row_per_area_plus_header():
    canvas = rd.diagram_10_article_figure_map()
    # 6 data rows + 1 header row, 2 columns each = 14 text cells, plus the title.
    texts = [el for el in canvas.elements if el.startswith("<text")]
    assert len(texts) == 1 + 14  # title + (6 rows + 1 header) * 2 columns
