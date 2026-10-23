#!/usr/bin/env python3
"""Apply the shared statement gates to the current source surface.

The incumbent manifest and its frozen declarations retain their original source
pin. This entry point loads ledger/current.yaml and uses the same gate functions
for the new declarations, without changing that earlier source surface.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import re
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools" / "leanform"))

from leanform_tools.config import Node, RepoConfig  # noqa: E402
from leanform_tools.gate import Result, run  # noqa: E402
from leanform_tools.verify import run_unit_tests  # noqa: E402
from leanform_tools import certificate, check_coverage, sync_docs  # noqa: E402
from leanform_tools import lean_source  # noqa: E402


class PaperConfig(RepoConfig):
    """The new frozen directory, with the shared CERW build target."""

    @property
    def lib_dir(self) -> Path:
        return self.root / "CERW" / "LimitShapes"

    @property
    def frozen_dirs(self) -> list[Path]:
        return [self.lib_dir / "Frozen"]


EVENT_NODES = {"current-lem-contact", "current-lem-separated-brackets"}
SOURCE_CLOSURES = {
    "lem-contact-common-event": "current-lem-contact",
    "lem-separated-brackets-common-event": "current-lem-separated-brackets",
}
PROVED_STATES = {"SEALED", "PROVED"}
PROBABILITY_PRODUCERS = {
    "eq-distance-crossing": "CERW.LimitShapes.distance_crossing_bound",
    "sec-common-event": "CERW.LimitShapes.exists_common_event",
}
SOURCE_CONSUMERS = {
    "lem-contact-common-event": "CERW.LimitShapes.contact_potential_on_common_event",
    "lem-separated-brackets-common-event":
        "CERW.LimitShapes.separated_brackets_on_euclidean_event",
}


def status_text(cfg: PaperConfig) -> str:
    """Report manifest completion only with pinned coverage and completed producers/consumers."""
    proved = [node for node in cfg.nodes if node.state in PROVED_STATES]
    coverage = Result("status_coverage")
    check_coverage.check(coverage, replace(cfg, nodes=proved))
    pinned = cfg.paper_sha256 is not None and hashlib.sha256(
        cfg.paper_path.read_bytes()
    ).hexdigest() == cfg.paper_sha256

    def completed(required: dict[str, str]) -> int:
        return sum(any(node.id == ident and node.kind == "theorem" and node.decls == [export]
                       for node in proved)
                   for ident, export in required.items())

    producers = completed(PROBABILITY_PRODUCERS)
    consumers = completed(SOURCE_CONSUMERS)
    owners: dict[Path, int] = {}
    for node in proved:
        if node.file:
            path = (cfg.root / node.file).resolve()
            owners[path] = owners.get(path, 0) + 1
    unowned = {
        path.resolve() for directory in cfg.frozen_dirs for path in directory.rglob("*.lean")
        if owners.get(path.resolve(), 0) != 1
    }
    if (cfg.nodes and len(proved) == len(cfg.nodes) and pinned and coverage.processed > 0
            and not coverage.failures and not unowned
            and producers == len(PROBABILITY_PRODUCERS)
            and consumers == len(SOURCE_CONSUMERS)):
        return (
            f"**All {coverage.total} labeled results are proved in "
            f"{len(cfg.nodes)} checked declarations.** "
            "The literal Section 5.1 event has polynomial exceptional probability, "
            "and both contact and separated brackets use its produced uniform constants."
        )
    drafts = sum(node.state == "DRAFT_SORRY" for node in cfg.nodes)
    conditional = sum(node.state == "CONDITIONAL" for node in cfg.nodes)
    other = len(cfg.nodes) - len(proved) - drafts - conditional
    represented = coverage.total - len(coverage.failures)
    return (
        f"**{len(cfg.nodes)} manifest declarations: {len(proved)} sealed/proved, "
        f"{drafts} draft, {conditional} conditional, {other} other.** "
        f"{represented}/{coverage.total} source result blocks have sealed/proved label coverage; "
        f"{len(coverage.failures)} unresolved. "
        + ("" if pinned else "Source pin is unverified; source coverage remains unresolved. ")
        + ("" if coverage.processed else "No source result blocks were found. ")
        + f"{len(unowned)} frozen files lack a unique sealed/proved owner. "
        + f"Probability producers: {producers}/{len(PROBABILITY_PRODUCERS)} sealed/proved. "
        + f"Source consumers: {consumers}/{len(SOURCE_CONSUMERS)} sealed/proved."
    )


def surface_text(cfg: PaperConfig) -> str:
    """Generate the current paper correspondence, including the source frontier."""
    lines = [
        "| id | Lean | paper | checked type | source coverage |",
        "|---|---|---|---|---|",
    ]
    for node in cfg.nodes:
        coverage = "direct"
        if node.id in EVENT_NODES:
            coverage = "deterministic event implication"
        elif node.id in SOURCE_CLOSURES:
            coverage = "full common-event source closure"
        elif node.id in {"eq-distance-crossing", "sec-common-event"}:
            coverage = "section probability estimate"
        decls = ", ".join(f"`{d}`" for d in node.decls)
        paper = sync_docs.paper_cell(node, cfg)
        lines.append(f"| `{node.id}` | {decls} | {paper} | {node.state} | {coverage} |")
    return "\n".join(lines)


def check_docs(res, cfg: PaperConfig, write: bool = False) -> None:
    """Require the new manifest-derived blocks alongside the preserved old blocks."""
    blocks = [
        ("README.md", "STATUS", status_text(cfg)),
        ("PROOF.md", "STATUS", status_text(cfg)),
        ("CORRESPONDENCE.md", "SURFACE", surface_text(cfg)),
    ]
    res.total = len(blocks)
    for rel, kind, body in blocks:
        path = cfg.root / rel
        text = path.read_text()
        begin = f"<!-- LIMIT-SHAPES-{kind}-BEGIN -->"
        end = f"<!-- LIMIT-SHAPES-{kind}-END -->"
        res.count()
        if text.count(begin) != 1 or text.count(end) != 1:
            res.fail(f"{rel}: require exactly one {kind} marker pair")
            continue
        start = text.index(begin) + len(begin)
        finish = text.index(end)
        if start > finish:
            res.fail(f"{rel}: reversed markers")
            continue
        generated = text[:start] + "\n\n" + body + "\n\n" + text[finish:]
        if write:
            path.write_text(generated)
        elif generated != text:
            res.fail(f"{rel}: stale current-source block; run tools/verify_current.py --write-docs")


def certificate_text(cfg: PaperConfig) -> str:
    """Use the shared build/hash/axiom probes, retaining the source-closure distinction."""
    text = certificate.render(cfg, certificate.gather(cfg))
    text = text.replace("ledger/manifest.yaml", "ledger/current.yaml")
    text = text.replace("`python3 -m leanform_tools.certificate`", "`python3 tools/verify_current.py`")
    text = re.sub(
        r"python3 -m leanform_tools\.(?:check_manifest|check_axioms|check_warnings|certificate) "
        r"\..*\n", "", text,
    )
    text = text.replace("lake build CERW\n", "lake build CERW\npython3 tools/verify_current.py\n")
    text = text.replace(
        "## What is claimed\n\n",
        "## What is claimed\n\n" + status_text(cfg) + "\n\n"
        "The following tally certifies the registered Lean types, including the "
        "common-event probability producer and its source consumers.\n\n",
    )
    return text.rstrip() + "\n"


def check_certificate(res, cfg: PaperConfig, write: bool = False) -> None:
    """Fail on stale supplemental build and axiom evidence."""
    text = certificate_text(cfg)
    path = cfg.root / "CERTIFICATE-LIMIT-SHAPES.md"
    res.total = len(cfg.nodes)
    if write:
        path.write_text(text)
    elif not path.exists() or path.read_text() != text:
        res.fail("stale certificate; run tools/verify_current.py --write-certificate")
    res.count(len(cfg.nodes))


def check_nl_twins(res, cfg: PaperConfig) -> None:
    """Require each mathematical record to carry the exact source and frozen type."""
    paper = cfg.paper_path.read_text().splitlines()
    res.total = len(cfg.nodes)
    for node in cfg.nodes:
        res.count()
        path = cfg.root / "ledger" / "nl" / f"{node.id}.tex"
        if not path.is_file():
            res.fail(f"{node.id}: missing natural-language record")
            continue
        text = path.read_text()
        match = cfg.source_re.match(node.source)
        if match is None:
            res.fail(f"{node.id}: unresolved source range")
            continue
        start, end = int(match.group("a")), int(match.group("b"))
        source = "\n".join(line.rstrip() for line in paper[start - 1:end])
        anchor = (cfg.root / node.file).read_text()
        spans = lean_source.frozen_blocks(anchor)
        statement = lean_source.block_body(anchor, spans[0]).rstrip()
        for description, body in [("paper excerpt", source), ("Lean statement", statement)]:
            if f"\\begin{{verbatim}}\n{body}\n\\end{{verbatim}}" not in text:
                res.fail(f"{node.id}: stale {description}")
        marker = "\\paragraph{Proof of the registered statement.}"
        if marker not in text:
            res.fail(f"{node.id}: missing proof record")
            continue
        proof = text.split(marker, 1)[1]
        proof = re.split(r"\\(?:paragraph|section|subsection)\*?\s*\{", proof, maxsplit=1)[0]
        if re.search(r"\bSKETCH\b", proof, re.IGNORECASE):
            res.fail(f"{node.id}: SKETCH proof record")
        if not check_coverage._strip_comments(proof).strip():
            res.fail(f"{node.id}: empty proof record")


def run_current_source_tests() -> int:
    """Run the project-specific regressions outside the reusable tools package."""
    print("=== current-source unit tests", flush=True)
    proc = subprocess.run(
        [sys.executable, "-m", "unittest", "discover",
         "-s", str(ROOT / "tools" / "tests"), "-p", "test_current_source.py"],
        cwd=ROOT,
    )
    return proc.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-lake", action="store_true")
    parser.add_argument("--write-docs", action="store_true")
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    if args.skip_lake and args.write_certificate:
        parser.error("--write-certificate requires the build and axiom probes")
    rc = run_current_source_tests()
    if rc:
        return rc
    rc = run_unit_tests(ROOT / "tools" / "leanform")
    if rc:
        return rc
    manifest = ROOT / "ledger" / "current.yaml"
    raw = yaml.safe_load(manifest.read_text())
    cfg = PaperConfig(ROOT, manifest, raw, [Node(n) for n in raw["nodes"]])
    modules = [
        "check_manifest", "check_coverage", "check_clauses", "check_constants",
        "check_exponents", "paper_anchors", "paper_citations", "check_hazards",
        "check_progress",
    ]
    if not args.skip_lake:
        modules += ["check_warnings", "check_axioms"]
    results = []
    for name in modules:
        module = importlib.import_module(f"leanform_tools.{name}")
        print(f"=== current {name}", flush=True)
        results.append(run(name, module.check, cfg))
    results.append(run("sync_docs", check_docs, cfg, write=args.write_docs))
    results.append(run("nl_twins", check_nl_twins, cfg))
    if not args.skip_lake:
        results.append(run("certificate", check_certificate, cfg, write=args.write_certificate))
    return max(results)


if __name__ == "__main__":
    sys.exit(main())
