#!/usr/bin/env python3
"""Expand the `\\input` lines of `paper/cerw.tex` into `paper/cerw-flat.tex`.

The deterministic gates in `tools/leanform/` read a single pinned paper file
(`source_pin.file` in `ledger/manifest.yaml`).  The manuscript is split into a
main file and three section files, so the pinned file is their mechanical
concatenation: every line of the form `\\input{sections/NAME}` is replaced by
the lines of `paper/sections/NAME.tex`, and nothing else changes.

A line `k` of a section file therefore sits at a fixed offset in the flat file,
and the four source files stay byte-identical to the manuscript.

    python3 tools/flatten_paper.py            # write paper/cerw-flat.tex
    python3 tools/flatten_paper.py --check    # fail if it is stale
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAIN = ROOT / "paper" / "cerw.tex"
FLAT = ROOT / "paper" / "cerw-flat.tex"
INPUT = re.compile(r"\\input\{(sections/[^}]+)\}")


def flatten() -> tuple[str, list[tuple[str, int]]]:
    """The flat text, and the flat line at which each section file starts."""
    out: list[str] = []
    starts: list[tuple[str, int]] = []
    for line in MAIN.read_text(encoding="utf-8").splitlines():
        m = INPUT.fullmatch(line.strip())
        if m is None:
            out.append(line)
            continue
        name = m.group(1)
        path = ROOT / "paper" / (name if name.endswith(".tex") else name + ".tex")
        starts.append((path.name, len(out) + 1))
        out.extend(path.read_text(encoding="utf-8").splitlines())
    return "\n".join(out) + "\n", starts


def main(argv: list[str]) -> int:
    text, starts = flatten()
    if "--check" in argv:
        if not FLAT.exists() or FLAT.read_text(encoding="utf-8") != text:
            print("paper/cerw-flat.tex is stale; rerun tools/flatten_paper.py")
            return 1
        print(f"paper/cerw-flat.tex is current ({text.count(chr(10))} lines)")
        return 0
    FLAT.write_text(text, encoding="utf-8")
    for name, line in starts:
        print(f"{name}: line k is flat line {line - 1}+k")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
