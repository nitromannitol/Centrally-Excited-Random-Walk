"""The axiom-closure gate. This one is the authority; it runs Lean.

`check_manifest` counts `sorry` tokens, which is not enough: a file can
contain no `sorry` and still depend on one transitively through an import.
`Exploding.Frozen.insertion_inequality` was exactly that — zero sorrys of its
own, `sorryAx` in its closure. A node may be SEALED only if `#print axioms` on
its export shows no `sorryAx`.

Fail-closed, in three places, because a probe that does not run must never
read as a clean closure:

- a probe that fails to elaborate is a failure, not an absence of findings;
- an export with no `#print axioms` output at all is a failure;
- duplicated output for one export is a failure (it means the parse is
  ambiguous and a verdict cannot be attributed).

The acceptance logic lives in `audit_closures`, a pure function, so the
boundary can be unit-tested without a toolchain.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

from .config import ALLOWED_AXIOMS, RepoConfig, load
from .gate import Result, run

_AXIOM_LINE = re.compile(r"^'(?P<decl>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]")
_NO_AXIOMS = re.compile(r"^'(?P<decl>[^']+)' does not depend on any axioms")


class ProbeError(Exception):
    """The probe did not run. Never interpreted as a clean closure."""


def parse_axiom_report(stdout: str) -> dict[str, set[str]]:
    """Map export name -> axiom closure, from `#print axioms` output.

    Lean wraps long info lines, so lines are joined before matching.
    """
    joined, buf = [], ""
    for raw in stdout.splitlines():
        if raw.startswith("'") and buf:
            joined.append(buf)
            buf = raw.strip()
        elif raw.startswith("'"):
            buf = raw.strip()
        elif buf:
            buf += " " + raw.strip()
    if buf:
        joined.append(buf)

    out: dict[str, set[str]] = {}
    for line in joined:
        m = _AXIOM_LINE.match(line)
        if m:
            axs = {a.strip() for a in m.group("axioms").split(",") if a.strip()}
            decl = m.group("decl")
            if decl in out:
                raise ProbeError(
                    f"{decl}: two axiom reports for one export; cannot attribute a verdict"
                )
            out[decl] = axs
            continue
        m = _NO_AXIOMS.match(line)
        if m:
            out[m.group("decl")] = set()
    return out


def audit_closures(
    nodes, reports: dict[str, set[str]]
) -> tuple[list[str], list[str]]:
    """Pure acceptance boundary. Returns (failures, per-node status lines)."""
    failures: list[str] = []
    status: list[str] = []
    for node in nodes:
        for decl in node.decls:
            if decl not in reports:
                failures.append(
                    f"{node.id}: no axiom report for {decl} — the probe did not "
                    "cover it; treated as a failure, not as a clean closure"
                )
                continue
            closure = reports[decl]
            extra = closure - ALLOWED_AXIOMS - {"sorryAx"}
            has_sorry = "sorryAx" in closure
            draft = node.state in {"DRAFT_SORRY", "CONDITIONAL"}

            if extra:
                failures.append(
                    f"{node.id}: {decl} depends on {sorted(extra)}, which is "
                    f"outside {sorted(ALLOWED_AXIOMS)}"
                )
            if has_sorry and not draft:
                failures.append(
                    f"{node.id}: state {node.state} but {decl} has sorryAx in "
                    "its closure — it depends on an open proof, transitively"
                )
            if draft and not has_sorry:
                failures.append(
                    f"{node.id}: state {node.state} but {decl} has a clean "
                    "closure — register its seal (the proof is done)"
                )
            status.append(
                f"{node.id}: {decl}: "
                + ("sorryAx (registered draft)" if has_sorry and draft
                   else "clean" if not closure - ALLOWED_AXIOMS
                   else f"{sorted(closure)}")
            )
    return failures, status


def _probe_source(cfg: RepoConfig) -> str:
    modules, decls = [], []
    for node in cfg.nodes:
        if node.file:
            modules.append(str(Path(node.file).with_suffix("")).replace("/", "."))
        decls.extend(node.decls)
    lines = [f"import {m}" for m in sorted(set(modules))]
    lines += [f"#print axioms {d}" for d in decls]
    return "\n".join(lines) + "\n"


def check(res: Result, cfg: RepoConfig) -> None:
    res.total = sum(len(n.decls) for n in cfg.nodes)
    if not cfg.nodes:
        res.vacuous_ok = "the manifest registers no nodes"
        return

    scratch = cfg.root / "scratch"
    scratch.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=scratch, delete=False, encoding="utf-8"
    ) as fh:
        fh.write(_probe_source(cfg))
        probe = Path(fh.name)

    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=cfg.root, capture_output=True, text=True, timeout=7200,
        )
    except FileNotFoundError:
        raise ProbeError("`lake` is not on PATH; the axiom gate cannot run")
    except subprocess.TimeoutExpired:
        raise ProbeError("the axiom probe timed out")
    finally:
        probe.unlink(missing_ok=True)

    if proc.returncode != 0 and "depends on axioms" not in proc.stdout:
        raise ProbeError(
            "the probe did not elaborate; this is a failure, not a clean "
            f"closure.\nstderr:\n{proc.stderr[-2000:]}"
        )

    reports = parse_axiom_report(proc.stdout)
    failures, status = audit_closures(cfg.nodes, reports)
    for f in failures:
        res.fail(f)
    for s in status:
        res.count()
        res.note(s)


def main(argv: list[str]) -> int:
    cfg = load(argv[1] if len(argv) > 1 else ".")
    return run("check_axioms", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
