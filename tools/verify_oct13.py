#!/usr/bin/env python3
"""Apply the shared statement gates to the separate oct13 source surface.

The incumbent manifest and its frozen declarations retain their original source
pin. This entry point loads ledger/oct13.yaml and uses the same gate functions
for the new declarations, without changing that earlier source surface.
"""

from __future__ import annotations

import argparse
import importlib
import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools" / "leanform"))

from leanform_tools.config import Node, RepoConfig  # noqa: E402
from leanform_tools.gate import run  # noqa: E402
from leanform_tools.verify import run_unit_tests  # noqa: E402
from leanform_tools import certificate, sync_docs  # noqa: E402
from leanform_tools import lean_source  # noqa: E402


class PaperConfig(RepoConfig):
    """The new frozen directory, with the shared CERW build target."""

    @property
    def lib_dir(self) -> Path:
        return self.root / "CERW" / "LimitShapes"

    @property
    def frozen_dirs(self) -> list[Path]:
        return [self.lib_dir / "Frozen"]


EVENT_NODES = {"oct13-lem-contact", "oct13-lem-separated-brackets"}


def status_text(cfg: PaperConfig) -> str:
    """Distinguish checked declaration types from the unclosed event producer."""
    closed = sum(n.id not in EVENT_NODES for n in cfg.nodes)
    conditional = len(cfg.nodes) - closed
    return (
        f"**{len(cfg.nodes)} checked declarations on 22 paper labels: "
        f"{closed} with direct source coverage; {conditional} deterministic "
        "common-event implications.** The common-event probability bound "
        "and its uniform constants remain open."
    )


def surface_text(cfg: PaperConfig) -> str:
    """Generate the current paper correspondence, including the source frontier."""
    lines = [
        "| id | Lean | paper | checked type | source coverage |",
        "|---|---|---|---|---|",
    ]
    for node in cfg.nodes:
        coverage = "conditional on event constants" if node.id in EVENT_NODES else "direct"
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
            res.fail(f"{rel}: stale current-source block; run tools/verify_oct13.py --write-docs")


def certificate_text(cfg: PaperConfig) -> str:
    """Use the shared build/hash/axiom probes, retaining the source-closure distinction."""
    text = certificate.render(cfg, certificate.gather(cfg))
    text = text.replace("ledger/manifest.yaml", "ledger/oct13.yaml")
    text = text.replace("`python3 -m leanform_tools.certificate`", "`python3 tools/verify_oct13.py`")
    text = re.sub(
        r"python3 -m leanform_tools\.(?:check_manifest|check_axioms|check_warnings|certificate) "
        r"\..*\n", "", text,
    )
    text = text.replace("lake build CERW\n", "lake build CERW\npython3 tools/verify_oct13.py\n")
    text = text.replace(
        "## What is claimed\n\n",
        "## What is claimed\n\n" + status_text(cfg) + "\n\n"
        "The following tally certifies the registered Lean types. It does not "
        "certify the missing probability producer.\n\n",
    )
    return text.rstrip() + "\n"


def check_certificate(res, cfg: PaperConfig, write: bool = False) -> None:
    """Fail on stale supplemental build and axiom evidence."""
    text = certificate_text(cfg)
    path = cfg.root / "CERTIFICATE-LIMIT-SHAPES.md"
    res.total = len(cfg.nodes)
    if write:
        path.write_text(text)
    elif not path.exists() or certificate._GENERATED_RE.sub("", path.read_text()) != \
            certificate._GENERATED_RE.sub("", text):
        res.fail("stale certificate; run tools/verify_oct13.py --write-certificate")
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
        if "\\paragraph{Proof of the registered statement.}" not in text:
            res.fail(f"{node.id}: missing proof record")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-lake", action="store_true")
    parser.add_argument("--write-docs", action="store_true")
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    if args.skip_lake and args.write_certificate:
        parser.error("--write-certificate requires the build and axiom probes")
    rc = run_unit_tests(ROOT / "tools" / "leanform")
    if rc:
        return rc
    manifest = ROOT / "ledger" / "oct13.yaml"
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
        print(f"=== oct13 {name}", flush=True)
        results.append(run(name, module.check, cfg))
    results.append(run("sync_docs", check_docs, cfg, write=args.write_docs))
    results.append(run("nl_twins", check_nl_twins, cfg))
    if not args.skip_lake:
        results.append(run("certificate", check_certificate, cfg, write=args.write_certificate))
    return max(results)


if __name__ == "__main__":
    sys.exit(main())
