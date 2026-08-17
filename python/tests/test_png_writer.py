import struct
import zlib

from sieve_sequence import png_writer

PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"


def _parse_chunks(data: bytes):
    """Splits a PNG byte string into (tag, payload) chunks, skipping the signature."""
    pos = len(PNG_SIGNATURE)
    chunks = []
    while pos < len(data):
        length = struct.unpack(">I", data[pos:pos + 4])[0]
        tag = data[pos + 4:pos + 8]
        payload = data[pos + 8:pos + 8 + length]
        chunks.append((tag, payload))
        pos += 8 + length + 4  # length + tag + payload + crc
    return chunks


def test_encode_png_starts_with_the_png_signature():
    data = png_writer.encode_png(1, 1, [bytes([255, 0, 0])])
    assert data.startswith(PNG_SIGNATURE)


def test_encode_png_chunk_order_is_ihdr_idat_iend():
    data = png_writer.encode_png(1, 1, [bytes([255, 0, 0])])
    tags = [tag for tag, _ in _parse_chunks(data)]
    assert tags == [b"IHDR", b"IDAT", b"IEND"]


def test_encode_png_ihdr_encodes_width_height_and_8bit_rgb():
    width, height = 3, 2
    rows = [bytes([10, 20, 30] * width) for _ in range(height)]
    data = png_writer.encode_png(width, height, rows)
    chunks = dict(_parse_chunks(data))
    parsed_width, parsed_height, bit_depth, color_type = struct.unpack(">IIBB", chunks[b"IHDR"][:10])
    assert (parsed_width, parsed_height, bit_depth, color_type) == (width, height, 8, 2)


def test_encode_png_idat_round_trips_the_exact_pixel_bytes():
    width, height = 2, 2
    rows = [bytes([1, 2, 3, 4, 5, 6]), bytes([7, 8, 9, 10, 11, 12])]
    data = png_writer.encode_png(width, height, rows)
    chunks = dict(_parse_chunks(data))
    raw = zlib.decompress(chunks[b"IDAT"])
    # each scanline is prefixed with a filter-type byte (0 = None)
    stride = width * 3 + 1
    assert len(raw) == stride * height
    for row_idx, row in enumerate(rows):
        scanline = raw[row_idx * stride:(row_idx + 1) * stride]
        assert scanline[0] == 0
        assert scanline[1:] == row


def test_encode_png_iend_chunk_is_empty():
    data = png_writer.encode_png(1, 1, [bytes([0, 0, 0])])
    chunks = dict(_parse_chunks(data))
    assert chunks[b"IEND"] == b""


def test_save_png_writes_the_same_bytes_encode_png_would_produce(tmp_path):
    width, height = 1, 1
    rows = [bytes([9, 9, 9])]
    expected = png_writer.encode_png(width, height, rows)
    out_path = tmp_path / "out.png"
    png_writer.save_png(str(out_path), width, height, rows)
    assert out_path.read_bytes() == expected
