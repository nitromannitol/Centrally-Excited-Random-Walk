#!/usr/bin/env python3
"""Compare the serialized frozen types written by tools/FrozenTypes.lean with their pinned digests.

Run `lake env lean tools/FrozenTypes.lean` first. The pinned digests are in
tools/frozen-types.sha256; the declarations must be exactly the exports of
ledger/oct13.yaml and the theorems of CERW/MainTheorems.lean. After an approved
change of statement or of a definition it uses, rerun with --write.
"""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
PINS = ROOT / "tools" / "frozen-types.sha256"
OUT = ROOT / ".lake" / "frozen-types"


def expected_names() -> set[str]:
    raw = yaml.safe_load((ROOT / "ledger" / "oct13.yaml").read_text())
    main = (ROOT / "CERW" / "MainTheorems.lean").read_text()
    mains = {"CERW.MainTheorems." + t for t in re.findall(r"(?m)^theorem\s+(\S+)", main)}
    return {node["export"] for node in raw["nodes"]} | mains


def digests() -> dict[str, str]:
    return {p.name[:-len(".txt")]: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(OUT.glob("*.txt"))}


def main(argv: list[str]) -> int:
    names = expected_names()
    got = digests()
    if set(got) != names:
        print(f"serializations {sorted(set(got) ^ names)} missing or unexpected; "
              "run lake env lean tools/FrozenTypes.lean")
        return 1
    if "--write" in argv:
        PINS.write_text("".join(f"{h}  {n}\n" for n, h in sorted(got.items())))
        print(f"wrote {len(got)} digests to {PINS.relative_to(ROOT)}")
        return 0
    pins = dict(reversed(line.split("  ", 1)) for line in PINS.read_text().splitlines())
    pins = {n.strip(): h for n, h in pins.items()}
    bad = 0
    if set(pins) != names:
        print(f"pinned declarations differ from the registered ones: {sorted(set(pins) ^ names)}")
        bad += 1
    for n in sorted(names & set(pins)):
        if got[n] != pins[n]:
            print(f"{n}: elaborated type or a definition it uses changed ({got[n]})")
            bad += 1
    print(f"{len(names)} frozen types checked, {bad} changed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
