"""Refuse a change that defers work instead of doing it.

The expensive failure mode of an agentic formalization is not a false proof;
the axiom gate (`check_axioms.py`) catches that. It is UNPRODUCTIVE WRAPPING:
a worker reduces an open goal to a new lemma that is itself open, repackages
it under a longer name, and reports progress, while the set of open
assumptions never shrinks.

This check counts open holes (`sorry`, comments masked) across the
production Lean tree and compares them with the recorded baseline in
`<root>/ledger/holes.json`. A change may close holes or leave them alone. It
may not open new ones.

    python3 -m leanform_tools.check_progress <repo>           # verify
    python3 -m leanform_tools.check_progress <repo> --record  # record

A hole in a file that a manifest node registers as `DRAFT_SORRY` is that
node's own placeholder and is counted like any other: closing it is what
sealing means, and `check_manifest.py`/`check_axioms.py` are the checks that
know it is authorized.

Unlike the vendored copies (which `rglob` a single hardcoded library
directory, e.g. `(ROOT / "Sandpile").rglob("*.lean")`), the file set here is
`cfg.production_lean_files()`, so this never needs a per-repo literal and
never silently scans zero files because the directory name changed.

If `ledger/holes.json` does not exist, that is a declared-vacuity note, not
a crash: most repos in this program do not have a baseline recorded yet, and
a missing baseline is not evidence that holes were opened.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from . import lean_source as ls
from .config import RepoConfig, load
from .gate import Result, run

_HOLE_RE = re.compile(r"\bsorry\b")


def survey(files, root: Path) -> dict[str, int]:
    """Open-hole count per file, comments masked. `files` relative to `root`."""
    out: dict[str, int] = {}
    for f in files:
        masked = ls.mask_comments(f.read_text(encoding="utf-8", errors="replace"))
        n = len(_HOLE_RE.findall(masked))
        if n:
            out[str(f.relative_to(root))] = n
    return out


def audit_progress(now: dict[str, int], baseline: dict) -> tuple[list[str], list[str]]:
    """Pure comparison against a recorded `{"holes": {...}, "total": N}` baseline.

    Returns `(failures, notes)`. Only the aggregate total is a gate -- a hole
    that moved from one file to another with the total unchanged is not
    itself a failure, matching the baseline format this replaces.
    """
    old: dict[str, int] = baseline.get("holes") or {}
    oldtotal = baseline.get("total", sum(old.values()))
    total = sum(now.values())

    failures: list[str] = []
    notes: list[str] = []

    if total > oldtotal:
        failures.append(
            f"{oldtotal} -> {total} open hole(s): a change may close holes, "
            "it may not open them. If a step genuinely needs spelling out "
            "further, close the hole you opened in the same change, or "
            "record a new baseline with a written reason "
            "(--record)."
        )
        opened = {f: n for f, n in now.items() if n > old.get(f, 0)}
        for f, n in sorted(opened.items()):
            failures.append(f"  + {f}: {old.get(f, 0)} -> {n}")
    else:
        closed = {f: old[f] - now.get(f, 0) for f in old if old[f] > now.get(f, 0)}
        for f, n in sorted(closed.items()):
            notes.append(f"  - {f}: closed {n}")
        notes.append(f"{oldtotal} -> {total} open hole(s)")
    return failures, notes


def check(res: Result, cfg: RepoConfig, record: bool = False) -> None:
    files = cfg.production_lean_files()
    res.total = len(files)
    if not files:
        res.vacuous_ok = "no production .lean files"
        return

    holes_path = cfg.root / "ledger" / "holes.json"
    now = survey(files, cfg.root)
    total = sum(now.values())

    if record:
        holes_path.parent.mkdir(parents=True, exist_ok=True)
        holes_path.write_text(
            json.dumps({"holes": now, "total": total}, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        res.count(len(files))
        res.note(f"recorded {total} open hole(s) in {len(now)} file(s)")
        return

    if not holes_path.exists():
        # Declared vacuity, not a crash: no baseline means nothing to compare
        # against, which is the normal state for a repo that has not run
        # `--record` yet -- see the module docstring.
        res.vacuous_ok = "ledger/holes.json is absent; run --record once to create it"
        return

    baseline = json.loads(holes_path.read_text(encoding="utf-8"))
    failures, notes = audit_progress(now, baseline)
    res.count(len(files))
    for f in failures:
        res.fail(f)
    for n in notes:
        res.note(n)


def main(argv: list[str]) -> int:
    args = argv[1:]
    record = "--record" in args
    positional = [a for a in args if not a.startswith("--")]
    root = positional[0] if positional else "."
    cfg = load(root)
    return run("check_progress", check, cfg, record=record)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
