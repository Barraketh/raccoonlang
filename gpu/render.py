#!/usr/bin/env python3
"""Turns a printed Raccoon `String` value back into text.

The CLI prints a computed String as a constructor tree: `Char.mk(n)` for each character, with any packed literal tail
printed as a quoted string. This reads those pieces in order and writes the text.
"""
import json
import re
import sys

PIECE = re.compile(r'Char\.mk\((\d+)\)|("(?:[^"\\]|\\.)*")')


def render(printed: str) -> str:
    out = []
    for code, literal in PIECE.findall(printed):
        out.append(chr(int(code)) if code else json.loads(literal))
    return "".join(out)


if __name__ == "__main__":
    lines = [l for l in sys.stdin.read().splitlines() if not re.match(r"^\d\d:\d\d:\d\d\.\d+: ", l)]
    sys.stdout.write(render("\n".join(lines)))
