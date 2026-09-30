"""Produce the Lean certificate: a machine-checked record of what is proved.

The certificate is not prose. Every line of it is generated from the
manifest, from the files on disk, and from asking Lean itself for each
node's axiom closure, so a reader can reproduce it with the commands it
names and compare byte for byte.

    python3 -m leanform_tools.certificate <repo>            # write CERTIFICATE.md
    python3 -m leanform_tools.certificate <repo> --check    # verify it is current

Generation is split into two pieces on purpose:

* `gather(cfg)` does everything that touches Lake or the filesystem, and
  raises `CertificateError` the moment anything is wrong. It never returns
  partial data.
* `render(cfg, data)` is pure: it turns an already-gathered `data` dict into
  the certificate text, with no Lake and no I/O beyond what `data` already
  holds. This is what the tests below exercise directly.

`check()` calls `generate()` (== `render(cfg, gather(cfg))`) and only ever
calls `OUT.write_text(...)` on the text that call returns. If `gather`
raises, `check` never reaches the write, so a broken generation cannot
overwrite a good CERTIFICATE.md already on disk -- see
`tests/test_build_side.py`'s regression test for this property.

BUG NOT REPRODUCED HERE: ~/lean/Divisible-Sandpile-Percolation/tools/
certificate.py:170 prints "Every node's state in `ledger/manifest.yaml` is
`SEALED`." unconditionally -- literally always, regardless of the actual
mix of states. That repo's manifest has 78 SEALED and 26 FROZEN nodes (104
total), so the sentence is false every time it is printed: 26 nodes are not
SEALED. `claim_summary()` below counts every state with
`collections.Counter` and only ever states what the counts actually show,
the same discipline `sync_docs.status_block` already uses for the README
status line.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import tempfile
from collections import Counter
from datetime import date
from pathlib import Path

from . import lean_source as ls
from .check_axioms import ProbeError, audit_closures, parse_axiom_report
from .config import ALLOWED_AXIOMS, RepoConfig, load
from .gate import Result, run

OUT_NAME = "CERTIFICATE.md"

# The date row is allowed to differ between the file on disk and a freshly
# generated one; `--check` strips it from both sides before comparing.
_GENERATED_RE = re.compile(r"\| Generated \| .* \|")


class CertificateError(Exception):
    """Generation did not complete. The file on disk must not be touched."""


# ---- gathering (Lake- and filesystem-dependent) ---------------------------


def _toolchain(cfg: RepoConfig) -> str:
    p = cfg.root / "lean-toolchain"
    if not p.exists():
        raise CertificateError("lean-toolchain does not exist")
    return p.read_text(encoding="utf-8").strip()


def _mathlib_rev(cfg: RepoConfig) -> str | None:
    """The Mathlib package's pinned commit, from `lake-manifest.json`.

    Reads the JSON properly and looks up the package literally named
    `mathlib`, rather than grabbing the first 40-hex-character `"rev"` value
    anywhere in the file. `lake-manifest.json` lists every dependency
    (aesop, batteries, Qq, ...); Mathlib is not always the first entry, so
    that regex would sometimes report a different package's revision as
    "the Mathlib revision".
    """
    p = cfg.root / "lake-manifest.json"
    if not p.exists():
        return None
    try:
        manifest = json.loads(p.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise CertificateError(f"lake-manifest.json is not valid JSON: {exc}")
    for pkg in manifest.get("packages") or []:
        if str(pkg.get("name", "")).lower() == "mathlib":
            return pkg.get("rev")
    return None


def _paper_sha(cfg: RepoConfig) -> str:
    if not cfg.paper_path.exists():
        raise CertificateError(f"{cfg.paper_rel} does not exist")
    return hashlib.sha256(cfg.paper_path.read_bytes()).hexdigest()


def _frozen_hash(cfg: RepoConfig, node) -> str:
    if not node.file:
        raise CertificateError(f"{node.id}: no file: recorded")
    path = cfg.root / node.file
    if not path.exists():
        raise CertificateError(f"{node.id}: {node.file} does not exist")
    text = path.read_text(encoding="utf-8")
    spans = ls.frozen_blocks(text)
    if len(spans) != 1 or spans[0][1] < 0:
        raise CertificateError(
            f"{node.id}: {node.file} does not carry exactly one terminated "
            "frozen block"
        )
    return hashlib.sha256(ls.block_body(text, spans[0]).encode("utf-8")).hexdigest()


def _run_build(cfg: RepoConfig) -> subprocess.CompletedProcess:
    """`lake build <lib_name>` -- never a hardcoded target.

    Referenced by name inside `gather()`, not bound as a default argument,
    so `unittest.mock.patch("leanform_tools.certificate._run_build", ...)`
    is enough to exercise `gather`/`generate`/`check` with no toolchain.
    """
    try:
        return subprocess.run(
            ["lake", "build", cfg.lib_name],
            cwd=cfg.root, capture_output=True, text=True, timeout=7200,
        )
    except FileNotFoundError:
        raise CertificateError("`lake` is not on PATH; the build cannot run")
    except subprocess.TimeoutExpired:
        raise CertificateError("the build timed out")


def _probe_axioms(cfg: RepoConfig) -> dict[str, set[str]]:
    """`#print axioms` on every declaration the manifest registers.

    One elaboration, one `#print axioms` per declaration -- the same recipe
    `check_axioms.check` uses. The pure parsing step (`parse_axiom_report`)
    is imported from there rather than reimplemented; only the probe
    plumbing, which `check_axioms.check` intertwines with its own
    meta-check bookkeeping, is repeated here.
    """
    decls = [d for n in cfg.nodes for d in n.decls]
    if not decls:
        return {}
    modules = sorted({
        str(Path(n.file).with_suffix("")).replace("/", ".")
        for n in cfg.nodes if n.file
    })
    src = "\n".join(f"import {m}" for m in modules) + "\n"
    src += "\n".join(f"#print axioms {d}" for d in decls) + "\n"

    scratch = cfg.root / "scratch"
    scratch.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=scratch, delete=False, encoding="utf-8"
    ) as fh:
        fh.write(src)
        probe = Path(fh.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=cfg.root, capture_output=True, text=True, timeout=7200,
        )
    except FileNotFoundError:
        raise CertificateError("`lake` is not on PATH; the axiom probe cannot run")
    except subprocess.TimeoutExpired:
        raise CertificateError("the axiom probe timed out")
    finally:
        probe.unlink(missing_ok=True)

    if proc.returncode != 0 and "depends on axioms" not in proc.stdout:
        raise CertificateError(
            "the axiom probe did not elaborate; a certificate cannot be "
            f"generated.\nstderr:\n{proc.stderr[-2000:]}"
        )
    try:
        return parse_axiom_report(proc.stdout)
    except ProbeError as exc:
        raise CertificateError(str(exc))


def gather(cfg: RepoConfig) -> dict:
    """Everything Lake- or filesystem-dependent that `render` needs.

    Fail-closed: raises `CertificateError` on the first problem, rather than
    returning a dict with a hole in it that `render` would have to guess
    about.
    """
    if not cfg.nodes:
        raise CertificateError("the manifest registers no nodes")

    data: dict = {
        "toolchain": _toolchain(cfg),
        "mathlib_rev": _mathlib_rev(cfg),
        "paper_sha": _paper_sha(cfg),
        "frozen_hashes": {n.id: _frozen_hash(cfg, n) for n in cfg.nodes},
    }

    build = _run_build(cfg)
    if build.returncode != 0:
        raise CertificateError(
            f"lake build {cfg.lib_name} exited {build.returncode}; a "
            "certificate cannot claim a build that did not succeed"
        )
    warnings = [
        line for line in build.stdout.splitlines()
        if line.lstrip().lower().startswith("warning:")
    ]
    jobs_m = re.search(r"Build completed successfully \((\d+) jobs\)", build.stdout)
    data["build_jobs"] = jobs_m.group(1) if jobs_m else None
    data["warning_count"] = len(warnings)

    reports = _probe_axioms(cfg)
    failures, _status = audit_closures(cfg.nodes, reports)
    if failures:
        raise CertificateError(
            "axiom closures disagree with the manifest; a certificate would "
            "misrepresent what is proved:\n  " + "\n  ".join(failures)
        )
    data["axiom_reports"] = reports
    return data


# ---- rendering (pure) ------------------------------------------------------


def claim_summary(nodes) -> str:
    """The "what is claimed" sentence, computed from the actual state counts.

    Never says "every node is SEALED" unless every node actually is -- see
    the module docstring for the bug this replaces.
    """
    counts = Counter(n.state for n in nodes)
    total = len(nodes)
    sealed = counts.get("SEALED", 0)
    proved = counts.get("PROVED", 0)
    conditional = counts.get("CONDITIONAL", 0)
    frozen = counts.get("FROZEN", 0)
    draft = counts.get("DRAFT_SORRY", 0)
    other = total - sealed - proved - conditional - frozen - draft

    if total and sealed == total:
        return (
            f"Every node's state in `ledger/manifest.yaml` is `SEALED`: all "
            f"{total} are proved with no added axiom and no `sorry`."
        )
    if total and sealed + proved == total:
        return (
            f"Every node's state in `ledger/manifest.yaml` is `SEALED` or "
            f"`PROVED` ({sealed} SEALED, {proved} PROVED, {total} total): "
            "all are proved with no added axiom and no `sorry`."
        )

    parts = []
    if sealed:
        parts.append(f"{sealed} `SEALED`")
    if proved:
        parts.append(f"{proved} `PROVED`")
    if conditional:
        parts.append(f"{conditional} `CONDITIONAL`")
    if frozen:
        parts.append(f"{frozen} `FROZEN`")
    if draft:
        parts.append(f"{draft} `DRAFT_SORRY`")
    if other:
        parts.append(f"{other} other")
    return (
        f"Of {total} node(s) registered in `ledger/manifest.yaml`: "
        + ", ".join(parts)
        + ". Only `SEALED` and `PROVED` nodes are proved with a clean axiom "
        "closure; `FROZEN` nodes are cited results carried as explicit "
        "hypotheses and are assumed here, not proved; `CONDITIONAL` and "
        "`DRAFT_SORRY` nodes are not yet sealed."
    )


def _verdict(closures: list[set[str]], state: str) -> str:
    """The axiom-closure table cell for one node.

    Uses `config.ALLOWED_AXIOMS`, the same acceptance vocabulary
    `check_axioms.audit_closures` uses, so this cannot classify a closure
    differently from the checker that gates it.
    """
    if not closures:
        return "—"
    merged: set[str] = set()
    for c in closures:
        merged |= c
    extra = merged - ALLOWED_AXIOMS - {"sorryAx"}
    if extra:
        return "**" + ", ".join(sorted(extra)) + "**"
    if "sorryAx" in merged:
        draft = state in {"DRAFT_SORRY", "CONDITIONAL"}
        return "`sorryAx` (registered draft)" if draft else "**sorryAx**"
    return "classical only"


def render(cfg: RepoConfig, data: dict, today: str | None = None) -> str:
    """Pure: builds the certificate text from an already-gathered `data`."""
    today = today or date.today().isoformat()
    nodes = cfg.nodes
    lines: list[str] = []
    A = lines.append

    A("# Lean certificate")
    A("")
    A(
        f"Formalizes statements pinned in `{cfg.paper_rel}` as the Lean "
        f"library `{cfg.lib_name}`. This file records what a machine has "
        "checked, and how to check it again. It is generated by "
        "`python3 -m leanform_tools.certificate`; do not edit it by hand."
    )
    A("")
    A("## What is claimed")
    A("")
    A(claim_summary(nodes))
    A("")
    A("## Environment")
    A("")
    A("| | |")
    A("|---|---|")
    A(f"| Lean toolchain | `{data['toolchain']}` |")
    A(f"| Mathlib revision | `{data['mathlib_rev'] or 'unknown'}` |")
    A(f"| Paper (`{cfg.paper_rel}`) SHA-256 | `{data['paper_sha']}` |")
    jobs = f", {data['build_jobs']} jobs" if data.get("build_jobs") else ""
    A(f"| Build | succeeded{jobs} |")
    A(f"| Build warnings | {data['warning_count']} |")
    A(f"| Generated | {today} |")
    A("")
    A("## Reproducing it")
    A("")
    A("```")
    A("elan toolchain install $(cat lean-toolchain)")
    A(f"lake build {cfg.lib_name}")
    A("python3 -m leanform_tools.check_manifest .   # frozen statements match their hashes")
    A("python3 -m leanform_tools.check_axioms .     # no axiom closure contains an unregistered sorryAx")
    A("python3 -m leanform_tools.check_warnings .   # the build emits no unauthorized warning")
    A("python3 -m leanform_tools.certificate . --check")
    A("```")
    A("")
    A("## The theorems, and what each depends on")
    A("")
    A(
        "`#print axioms` reports the full transitive axiom closure of a "
        "proof. A closure of exactly `propext, Classical.choice, "
        "Quot.sound` is classical mathematics and nothing more; those three "
        "are Lean's own, not ours. `sorryAx` in a closure means the "
        "statement depends on an open proof; below, that is expected "
        "exactly at nodes whose state is `DRAFT_SORRY` or `CONDITIONAL`."
    )
    A("")
    A("| # | node | Lean name(s) | state | axiom closure |")
    A("|---|---|---|---|---|")
    reports = data["axiom_reports"]
    for i, n in enumerate(nodes, 1):
        decl_cell = ", ".join(f"`{d}`" for d in n.decls) if n.decls else "`<no decls>`"
        closures = [reports.get(d, set()) for d in n.decls]
        verdict = _verdict(closures, n.state)
        A(f"| {i} | `{n.id}` | {decl_cell} | `{n.state}` | {verdict} |")
    A("")
    A("## Frozen statements")
    A("")
    A(
        "The bytes of each statement are pinned, so a statement cannot be "
        "weakened after the fact without the hash changing. "
        "`python3 -m leanform_tools.check_manifest` verifies these."
    )
    A("")
    A("| node | SHA-256 of the frozen statement |")
    A("|---|---|")
    for n in nodes:
        got = data["frozen_hashes"].get(n.id)
        want = n.frozen_sha256
        flag = "" if (want and got == want) else "  ← MISMATCH"
        A(f"| `{n.id}` | `{got}`{flag} |")
    A("")
    A("## What is not claimed")
    A("")
    A(
        "- Anything not registered as a node in `ledger/manifest.yaml` is "
        "outside this certificate; `python3 -m leanform_tools.check_coverage` "
        "tracks whether the paper's statements are all registered."
    )
    frozen_n = sum(1 for n in nodes if n.state == "FROZEN")
    if frozen_n:
        A(
            f"- The {frozen_n} `FROZEN` node(s) are cited results, stated as "
            f"propositions in `{cfg.lib_name}/External/` and carried as "
            "explicit hypotheses by the theorems that use them; they are "
            "assumed here, not proved."
        )
    draft_ids = sorted(n.id for n in nodes if n.state == "DRAFT_SORRY")
    if draft_ids:
        A(
            f"- {', '.join(f'`{i}`' for i in draft_ids)} "
            f"{'is' if len(draft_ids) == 1 else 'are'} `DRAFT_SORRY`: the "
            "statement is frozen and registered, and no proof exists yet."
        )
    A("")
    return "\n".join(lines) + "\n"


def generate(cfg: RepoConfig, today: str | None = None) -> str:
    return render(cfg, gather(cfg), today=today)


# ---- CLI --------------------------------------------------------------


def check(res: Result, cfg: RepoConfig, write: bool = True) -> None:
    res.total = len(cfg.nodes)
    if not cfg.nodes:
        res.vacuous_ok = "the manifest registers no nodes"
        return

    # `generate` raises CertificateError on any problem; if it does, this
    # function returns via the exception before ever touching `out`, so a
    # failed generation cannot overwrite a good CERTIFICATE.md.
    text = generate(cfg)
    out = cfg.root / OUT_NAME

    if write:
        out.write_text(text, encoding="utf-8")
        res.count(len(cfg.nodes))
        res.note(f"wrote {out.relative_to(cfg.root)}")
        return

    if not out.exists():
        res.fail(f"{OUT_NAME} is missing")
        return
    cur = out.read_text(encoding="utf-8")
    if _GENERATED_RE.sub("", cur) != _GENERATED_RE.sub("", text):
        res.fail(f"{OUT_NAME} is out of date; regenerate it")
        return
    res.count(len(cfg.nodes))


def main(argv: list[str]) -> int:
    args = argv[1:]
    write = "--check" not in args
    positional = [a for a in args if not a.startswith("--")]
    root = positional[0] if positional else "."
    cfg = load(root)
    return run("certificate", check, cfg, write=write)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
