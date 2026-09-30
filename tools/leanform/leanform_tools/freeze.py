"""Register (or refresh) a frozen node in ledger/manifest.yaml.

    python3 -m leanform_tools.freeze <repo> ID FILE EXPORT KIND STATE "SOURCE"

KIND is `theorem` or `definition`; STATE is `DRAFT_SORRY`, `SEALED`, `FROZEN`,
`CONDITIONAL`, or `PROVED`. The frozen SHA-256 is computed with the recipe of
CORRESPONDENCE.md: the bytes strictly between the markers, one leading
newline dropped -- exactly what `check_manifest.py` recomputes. An existing
node with the same ID is replaced and its `version` bumped, so a statement
change is visible in the manifest history.

This is a port of the vendored `tools/freeze.py`, byte-identical (sha256
`994be60d...`, 51 lines, zero per-repo literals) across rotor-23,
Parking-Sharpness, Divisible-Sandpile-Percolation, Divisible-Sandpile-RWRS,
Dynamic-Dimensional-Reduction, Exploding-Sandpiles, and
Unique-Continuation-Planar. The port is faithful except for:

* `ROOT`/`MAN` are no longer derived from `__file__` (there is no single
  repo this file lives inside anymore) -- they come from `config.load`,
  i.e. from the manifest itself.
* the frozen-block hash is computed with `lean_source.frozen_blocks` /
  `lean_source.block_body`, the same primitives `check_manifest.py` uses to
  verify it, instead of a second hand-rolled `BEGIN`/`END` slice that could
  silently drift from the checker's own recipe.
* the quote refusal is broadened from "starts with `'`, or contains `"`
  anywhere" to "contains either quote character anywhere" -- a stray `'`
  in the middle of a source string was not rejected by the incumbent.
"""

from __future__ import annotations

import hashlib
import re
import sys
from datetime import date
from pathlib import Path

from . import lean_source as ls
from .config import RepoConfig, load


class FreezeError(Exception):
    """The freeze request is malformed; the manifest is left untouched."""


def frozen_hash(path: Path) -> str:
    """The SHA-256 `check_manifest.py` will recompute for this file's block."""
    text = path.read_text(encoding="utf-8")
    spans = ls.frozen_blocks(text)
    if len(spans) != 1:
        raise FreezeError(f"{path}: {len(spans)} frozen blocks, want exactly 1")
    span = spans[0]
    if span[1] < 0:
        raise FreezeError(f"{path}: unterminated frozen block")
    return hashlib.sha256(ls.block_body(text, span).encode("utf-8")).hexdigest()


def check_source(source: str) -> None:
    """Refuse a `source:` that would corrupt the plain-YAML splice below."""
    if ": " in source or "'" in source or '"' in source:
        raise FreezeError(
            "the source text must not contain ': ' or a quote character "
            "('\"' or \"'\"); reword it"
        )


def next_version(manifest_text: str, nid: str) -> tuple[int, str]:
    """The version to record, and `manifest_text` with `nid`'s old block cut out.

    A fresh id gets version 1. Re-freezing an existing id bumps its recorded
    `version:` by one (or to 2 if the old block carried none).
    """
    head, *blocks = manifest_text.split("  - id: ")
    version = 1
    kept = []
    for b in blocks:
        if b.split("\n")[0].strip() == nid:
            m = re.search(r"version: (\d+)", b)
            version = int(m.group(1)) + 1 if m else 2
        else:
            kept.append(b)
    head = head.replace("nodes: []", "nodes:\n")
    if not head.rstrip().endswith("nodes:"):
        head = head.rstrip("\n") + "\n"
    return version, head + "".join("  - id: " + b for b in kept)


def render_entry(
    nid: str, version: int, kind: str, source: str, file: str, export: str,
    state: str, sha: str, approved: str,
) -> str:
    return (
        f"{nid}\n    version: {version}\n    kind: {kind}\n    source: {source}\n"
        f"    file: {file}\n    export: {export}\n    state: {state}\n"
        f"    frozen_sha256: {sha}\n    provider: {export}\n"
        f'    approved: "{approved}"\n\n'
    )


def freeze(
    cfg: RepoConfig, nid: str, file: str, export: str, kind: str, state: str,
    source: str,
) -> str:
    """Insert or replace `nid` in `cfg`'s manifest. Returns a one-line summary."""
    check_source(source)
    sha = frozen_hash(cfg.root / file)
    version, trimmed = next_version(cfg.manifest_path.read_text(encoding="utf-8"), nid)
    entry = render_entry(
        nid, version, kind, source, file, export, state, sha,
        date.today().isoformat(),
    )
    cfg.manifest_path.write_text(trimmed + "  - id: " + entry, encoding="utf-8")
    return f"{nid}: version {version}, sha {sha[:12]}…, state {state}"


def main(argv: list[str]) -> int:
    args = argv[1:]
    if len(args) != 7:
        sys.exit(
            "usage: python3 -m leanform_tools.freeze <repo> ID FILE EXPORT "
            'KIND STATE "SOURCE"'
        )
    root, nid, file, export, kind, state, source = args
    cfg = load(root)
    try:
        print(freeze(cfg, nid, file, export, kind, state, source))
    except FreezeError as exc:
        sys.exit(f"freeze: {exc}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
