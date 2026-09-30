"""The pipeline. One command that either exits 0 or tells you exactly why not.

Order is ORRW's, and it is deliberate: unit tests first (a broken checker
must not produce a verdict), then every pure-Python gate, then the three that
invoke Lake, cheapest last-resort first. A failure short-circuits, because
the later gates' verdicts are not meaningful once an earlier one has failed —
there is no point auditing exponents in a statement whose hash does not match.

Exit codes:
  0  every gate passed, and every gate inspected something
  1  a gate failed
  2  a gate was VACUOUS — it exited 0 having inspected nothing

Code 2 exists because that is the failure this package was written for. Nine
checkers across four repos, two of them released, reported OK while
inspecting zero items. In a CI log "vacuous" and "clean" must not look alike.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

# (module, needs_lake, skip_if_absent)
PIPELINE = [
    ("check_manifest", False, None),
    ("check_coverage", False, "paper"),
    ("check_clauses", False, "paper"),
    ("check_constants", False, "paper"),
    ("check_exponents", False, "paper"),
    ("paper_anchors", False, "paper"),
    ("paper_citations", False, "paper"),
    ("check_hazards", False, None),
    ("check_progress", False, None),
    ("sync_docs", False, None),
    ("assumptions", False, None),
    ("linkcheck", False, None),
    ("check_warnings", True, None),
    ("check_axioms", True, None),
    ("certificate", True, None),
]

EXTRA_ARGS = {"assumptions": ["--check"], "certificate": ["--check"]}


def _has_paper(root: Path) -> bool:
    mf = root / "ledger" / "manifest.yaml"
    if not mf.exists():
        return False
    try:
        import yaml

        raw = yaml.safe_load(mf.read_text(encoding="utf-8")) or {}
        rel = (raw.get("source_pin") or {}).get("file")
        return bool(rel) and (root / rel).exists()
    except Exception:
        return False


def run_unit_tests(pkg_root: Path) -> int:
    print("=== unit tests")
    proc = subprocess.run(
        [sys.executable, "-m", "unittest", "discover",
         "-s", "leanform_tools/tests", "-t", "."],
        cwd=pkg_root, capture_output=True, text=True,
    )
    tail = (proc.stderr or proc.stdout).strip().splitlines()
    for line in tail[-3:]:
        print("   ", line)
    if proc.returncode != 0:
        print("verify: FAILED (the checkers' own tests do not pass; "
              "no verdict from this run is trustworthy)")
    return proc.returncode


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="leanform_tools.verify")
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--skip-lake", action="store_true",
                    help="run only the pure-Python gates")
    ap.add_argument("--keep-going", action="store_true",
                    help="run every gate and summarize instead of short-circuiting")
    ap.add_argument("--skip-tests", action="store_true")
    args = ap.parse_args(argv[1:])

    root = Path(args.root).resolve()
    pkg_root = Path(__file__).resolve().parent.parent

    if not args.skip_tests:
        rc = run_unit_tests(pkg_root)
        if rc != 0:
            return 1

    paper = _has_paper(root)
    results: list[tuple[str, int]] = []
    worst = 0

    for mod, needs_lake, requires in PIPELINE:
        if needs_lake and args.skip_lake:
            continue
        if requires == "paper" and not paper:
            print(f"=== {mod}: skipped (no pinned paper in this repo)")
            continue
        if not (pkg_root / "leanform_tools" / f"{mod}.py").exists():
            print(f"=== {mod}: NOT INSTALLED")
            continue

        print(f"=== {mod}")
        cmd = [sys.executable, "-m", f"leanform_tools.{mod}", str(root)]
        cmd += EXTRA_ARGS.get(mod, [])
        proc = subprocess.run(cmd, cwd=pkg_root, capture_output=True, text=True)
        out = (proc.stdout or "").rstrip()
        if out:
            for line in out.splitlines():
                print("   ", line)
        if proc.returncode != 0 and proc.stderr.strip():
            print("   ", proc.stderr.strip().splitlines()[-1])
        results.append((mod, proc.returncode))
        worst = max(worst, 2 if proc.returncode == 2 else proc.returncode)

        if proc.returncode != 0 and not args.keep_going:
            print(f"\nverify: STOPPED at {mod} (exit {proc.returncode}). "
                  "Later gates are not meaningful until this one passes.")
            return proc.returncode

    print("\n=== summary")
    for mod, rc in results:
        tag = {0: "ok", 1: "FAILED", 2: "VACUOUS"}.get(rc, f"exit {rc}")
        print(f"   {mod:<18} {tag}")
    if worst == 0:
        print(f"verify: OK ({len(results)} gates passed, each having inspected "
              "at least one item)")
    elif worst == 2:
        print("verify: VACUOUS — a gate inspected nothing. Treat as a failure.")
    else:
        print("verify: FAILED")
    return worst


if __name__ == "__main__":
    sys.exit(main(sys.argv))
