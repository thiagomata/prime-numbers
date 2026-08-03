import svg_kit


def test_escape_handles_the_three_unsafe_characters():
    assert svg_kit.escape("a & b < c > d") == "a &amp; b &lt; c &gt; d"


def test_escape_leaves_safe_text_untouched():
    assert svg_kit.escape("plain text 123") == "plain text 123"


def test_canvas_render_wraps_elements_in_a_valid_svg_document():
    canvas = svg_kit.Canvas(100, 50)
    canvas.line(0, 0, 10, 10)
    output = canvas.render()
    assert output.startswith('<svg xmlns="http://www.w3.org/2000/svg" width="100" height="50"')
    assert output.rstrip().endswith("</svg>")
    assert '<line x1="0" y1="0" x2="10" y2="10"' in output


def test_line_draws_between_the_given_points():
    canvas = svg_kit.Canvas(10, 10)
    canvas.line(1, 2, 3, 4, stroke="#123456", width=5)
    assert canvas.elements == [
        '<line x1="1" y1="2" x2="3" y2="4" stroke="#123456" stroke-width="5" />'
    ]


def test_line_with_dash_adds_stroke_dasharray():
    canvas = svg_kit.Canvas(10, 10)
    canvas.line(0, 0, 1, 1, dash="4,3")
    assert 'stroke-dasharray="4,3"' in canvas.elements[0]


def test_arrow_includes_marker_end():
    canvas = svg_kit.Canvas(10, 10)
    canvas.arrow(0, 0, 1, 1)
    assert 'marker-end="url(#arrowhead)"' in canvas.elements[0]


def test_circle_uses_radius_and_fill():
    canvas = svg_kit.Canvas(10, 10)
    canvas.circle(5, 5, r=3, fill="white", stroke="#222")
    assert canvas.elements == ['<circle cx="5" cy="5" r="3" fill="white" stroke="#222" stroke-width="2" />']


def test_cross_draws_two_crossed_lines():
    canvas = svg_kit.Canvas(10, 10)
    canvas.cross(5, 5, size=2)
    assert len(canvas.elements) == 2
    assert all(el.startswith("<line") for el in canvas.elements)


def test_text_escapes_its_label():
    canvas = svg_kit.Canvas(10, 10)
    canvas.text(1, 1, "a < b")
    assert "a &lt; b" in canvas.elements[0]


def test_link_text_wraps_text_in_an_anchor_tag():
    canvas = svg_kit.Canvas(10, 10)
    canvas.link_text(1, 1, "click me", "https://example.com/x?a=1&b=2")
    element = canvas.elements[0]
    assert element.startswith('<a href="https://example.com/x?a=1&amp;b=2"')
    assert "click me</text></a>" in element


def test_text_sub_renders_base_and_subscript():
    canvas = svg_kit.Canvas(10, 10)
    canvas.text_sub(1, 1, "e", "i+1")
    element = canvas.elements[0]
    assert ">e<tspan" in element
    assert ">i+1</tspan>" in element


def test_rect_includes_corner_radius():
    canvas = svg_kit.Canvas(10, 10)
    canvas.rect(0, 0, 10, 20, rx=4)
    assert 'rx="4"' in canvas.elements[0]
    assert 'width="10" height="20"' in canvas.elements[0]


def test_image_defaults_to_pixelated_rendering():
    canvas = svg_kit.Canvas(10, 10)
    canvas.image(0, 0, 10, 10, "data:image/png;base64,AAA")
    assert 'style="image-rendering: pixelated"' in canvas.elements[0]


def test_image_can_disable_pixelated_rendering():
    canvas = svg_kit.Canvas(10, 10)
    canvas.image(0, 0, 10, 10, "data:image/png;base64,AAA", pixelated=False)
    assert "style=" not in canvas.elements[0]


def test_table_draws_outer_rect_and_one_cell_per_row_column():
    canvas = svg_kit.Canvas(10, 10)
    canvas.table(0, 0, [10, 10], [["a", "b"], ["c", "d"]], row_height=20)
    rects = [el for el in canvas.elements if el.startswith("<rect")]
    texts = [el for el in canvas.elements if el.startswith("<text")]
    # one outer rect for the whole table, plus 4 text cells
    assert len(rects) == 1
    assert len(texts) == 4
    assert any(">a<" in el for el in texts)
    assert any(">d<" in el for el in texts)


def test_table_header_row_is_bold_by_default():
    canvas = svg_kit.Canvas(10, 10)
    canvas.table(0, 0, [10], [["head"], ["body"]], row_height=20)
    header_text = next(el for el in canvas.elements if ">head<" in el)
    body_text = next(el for el in canvas.elements if ">body<" in el)
    assert 'font-weight="bold"' in header_text
    assert 'font-weight="normal"' in body_text
