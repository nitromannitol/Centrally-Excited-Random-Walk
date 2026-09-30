"""Build the library and verify its warnings against the frozen manifest.

The only accepted warnings are one Lean `declaration uses 'sorry'` diagnostic
for each manifest node in state `DRAFT_SORRY`. Any missing, duplicate,
misplaced, or differently worded warning makes the check fail.

    python3 -m leanform_tools.check_warnings <repo>

The comparison itself lives in `audit_warnings`, a pure function of the raw
build output and the manifest nodes, so it is testable without ever running
Lake -- the same separation `check_axioms.audit_closures` uses.

BUG NOT REPRODUCED HERE: every vendored copy of this script (rotor-23,
ORRW-Lower-Bound, Divisible-Sandpile-Percolation, and IDLA-Cylinder-GFF's
byte-identical, unadapted copy of rotor-23's) hardcodes the build target as
a literal -- `lake build Rotor`, `lake build ORRW`, `lake build Sandpile`.
IDLA-Cylinder-GFF's copy still says `lake build Rotor`
(tools/check_warnings.py:68), which is not a target in that repo at all: it
is rotor-23's library name, left over from a copy-paste. `check()` below
derives the target from `cfg.lib_name`, which comes from the manifest (see
config.py), so this class of bug cannot recur by construction.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

from .config import RepoConfig, load
from .gate import Result, run

_ANSI_RE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
_WARNING_RE = re.compile(r"^warning:\s*(.*)$", re.IGNORECASE)
# Build-environment diagnostics from Lake, which say nothing about the Lean
# sources this gate is responsible for. A regex, not an exact string match:
# Lake's wording carries a path or version suffix on some releases.
_IGNORED_WARNING_RE = re.compile(r"manifest out of date", re.IGNORECASE)
# Lean 4.32+ quotes the constant with backticks; earlier releases use plain
# single quotes. Both are accepted so the gate tracks the toolchain instead
# of pinning one spelling.
_SORRY_WARNING_RE = re.compile(
    r"(?P<path>.+?\.lean):(?P<line>[0-9]+):(?P<column>[0-9]+): "
    r"declaration uses (?:'sorry'|`sorry`)"
)


class BuildError(Exception):
    """The build did not run to completion. Never read as a clean check."""


def audit_warnings(build_output: str, nodes) -> list[str]:
    """Pure comparison: the warning multiset Lake emitted vs. the manifest.

    `nodes` need only expose `.state` and `.file` (a `config.Node`, or a
    lightweight stand-in in tests). Returns failure messages; an empty list
    means the build's warnings are exactly the registered `DRAFT_SORRY`
    placeholders, nothing more and nothing less.
    """
    expected: Counter[str] = Counter()
    for node in nodes:
        if getattr(node, "state", None) == "DRAFT_SORRY" and getattr(node, "file", None):
            expected[str(Path(node.file))] += 1

    actual: Counter[str] = Counter()
    unexpected: list[str] = []
    for raw_line in build_output.splitlines():
        line = _ANSI_RE.sub("", raw_line)
        warning = _WARNING_RE.fullmatch(line)
        if warning is None:
            continue
        message = warning.group(1)
        if _IGNORED_WARNING_RE.search(message):
            continue
        sorry_warning = _SORRY_WARNING_RE.fullmatch(message)
        if sorry_warning is None:
            unexpected.append(line)
            continue
        actual[str(Path(sorry_warning.group("path")))] += 1

    failures: list[str] = [f"unexpected warning: {line}" for line in unexpected]
    missing = expected - actual
    extra = actual - expected
    for path, count in sorted(missing.items()):
        failures.append(f"missing {count} warning(s): {path}")
    for path, count in sorted(extra.items()):
        failures.append(f"extra {count} warning(s): {path}")
    return failures


def check(res: Result, cfg: RepoConfig) -> None:
    res.total = len(cfg.nodes)
    if not cfg.nodes:
        res.vacuous_ok = "the manifest registers no nodes"
        return

    target = cfg.lib_name  # never a literal -- see the module docstring
    try:
        proc = subprocess.run(
            ["lake", "build", target],
            cwd=cfg.root,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except FileNotFoundError:
        raise BuildError("`lake` is not on PATH; check_warnings cannot run")
    sys.stdout.write(proc.stdout)
    if proc.returncode != 0:
        raise BuildError(f"lake build {target} exited {proc.returncode}")

    for message in audit_warnings(proc.stdout, cfg.nodes):
        res.fail(message)
    res.count(len(cfg.nodes))


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else "."
    cfg = load(root)
    return run("check_warnings", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
