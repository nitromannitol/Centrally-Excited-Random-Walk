#!/usr/bin/env python3
"""Run this repository's deterministic gates.

    python3 tools/verify.py              # the whole pipeline
    python3 tools/verify.py --skip-lake  # the pure-Python gates only

The gates themselves are not in this repository. They live in
`tools/leanform/`, a git subtree of `nitromannitol/leanform-tools`, shared by
every paper repository, so that a fix to a checker is made once rather than
in a dozen drifting copies.

That sharing is the point. When each repository carried its own copy, the
copies rotted invisibly: a checker whose paper-name regex no longer matched
its repository did not fail, it passed while inspecting nothing. Nine of them
were doing exactly that across four repositories as of 2026-09-23. Everything
paper-specific now comes from `ledger/manifest.yaml` and
`ledger/readings.yaml` instead of from a literal in the checker.

To update the gates:

    git subtree pull --prefix tools/leanform \\
        https://github.com/nitromannitol/leanform-tools.git main --squash
"""

import pathlib
import sys

_HERE = pathlib.Path(__file__).resolve().parent
_PKG = _HERE / "leanform"

if not (_PKG / "leanform_tools").is_dir():
    sys.exit(
        f"{_PKG}/leanform_tools is missing.\n"
        "The checker package is a git subtree; restore it with:\n"
        "  git subtree add --prefix tools/leanform "
        "https://github.com/nitromannitol/leanform-tools.git main --squash"
    )

sys.path.insert(0, str(_PKG))

from leanform_tools import verify  # noqa: E402

if __name__ == "__main__":
    argv = list(sys.argv)
    # Default to this repository rather than the current directory, so the
    # command works from anywhere in the tree.
    if len(argv) == 1 or argv[1].startswith("-"):
        argv.insert(1, str(_HERE.parent))
    sys.exit(verify.main(argv))
