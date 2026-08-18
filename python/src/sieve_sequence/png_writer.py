"""Minimal stdlib-only PNG encoder (no Pillow/numpy) -- just zlib + struct.

For a dense per-cell heatmap, one SVG <rect> per cell doesn't scale (hundreds
of thousands of elements, tens of MB of text). A raster image is the right
format for that: one real pixel per data cell, let the viewer scale it.
"""

import struct
import zlib


def _chunk(tag: bytes, data: bytes) -> bytes:
    """One length-prefixed, CRC-suffixed PNG chunk, per the PNG spec."""
    return (
        struct.pack(">I", len(data)) + tag + data
        + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)
    )


def encode_png(width: int, height: int, rows_rgb) -> bytes:
    """rows_rgb: `height` rows, each `width * 3` RGB bytes (no filter byte)."""
    raw = bytearray()
    for row in rows_rgb:
        raw.append(0)  # filter type 0 (None) for every scanline
        raw.extend(row)
    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)  # 8-bit RGB truecolor
    idat = zlib.compress(bytes(raw), 9)
    return b"\x89PNG\r\n\x1a\n" + _chunk(b"IHDR", ihdr) + _chunk(b"IDAT", idat) + _chunk(b"IEND", b"")


def save_png(path: str, width: int, height: int, rows_rgb) -> None:
    """Encode rows_rgb as a PNG (see encode_png) and write it to path."""
    with open(path, "wb") as png_file:
        png_file.write(encode_png(width, height, rows_rgb))
