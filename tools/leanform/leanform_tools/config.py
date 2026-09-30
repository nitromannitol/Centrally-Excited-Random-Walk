"""Repo configuration, derived from the manifest — never hardcoded.

Every per-repo string that used to be embedded in a checker's regex lives
here and is read from `ledger/manifest.yaml`. That is the whole point of the
package: nine checkers across four repos passed vacuously because a regex
still said `rotor.tex` after the file had been copied into a repo whose paper
is `exploding.tex`.

Nothing in this module may contain a paper name, a library name, or a Frozen
directory path as a literal.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

import yaml

BEGIN = "-- FROZEN-STATEMENT-BEGIN"
END = "-- FROZEN-STATEMENT-END"

# The only axioms a sealed declaration may depend on.
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# States a node may carry. See BEST_PRACTICES.md §1.
STATES = frozenset({"FROZEN", "SEALED", "DRAFT_SORRY", "CONDITIONAL", "PROVED"})

# States whose axiom closure is allowed to contain sorryAx.
DRAFT_STATES = frozenset({"DRAFT_SORRY", "CONDITIONAL"})

# Tokens that may never appear in the production tree.
BANNED_TOKENS = ("admit", "sorryAx", "native_decide")


class ConfigError(Exception):
    """The repo is not shaped the way the protocol requires."""


@dataclass
class Node:
    """One manifest node, normalized across the two schemas in use.

    The released repos write `export: Rotor.Frozen.least_action` (exactly one
    declaration per block). `IDLA-Cylinder-GFF` writes
    `decls: [a_spectral, ...]`, allowing several declarations per block so a
    theorem is sealed together with the definitions carrying its content.

    Both are readable here. Which one is *correct* is a protocol question
    settled in audit/PLAN.md: one declaration per block is the rule, and the
    multi-declaration block is a stand-in for the semantic fingerprint that
    does not exist yet. Until the fingerprint lands, multi-declaration nodes
    are tolerated and reported, not rejected.
    """

    raw: dict

    @property
    def id(self) -> str:
        return self.raw.get("id", "<no id>")

    @property
    def state(self) -> str | None:
        return self.raw.get("state")

    @property
    def kind(self) -> str | None:
        return self.raw.get("kind")

    @property
    def file(self) -> str | None:
        return self.raw.get("file")

    @property
    def source(self) -> str | None:
        return self.raw.get("source")

    @property
    def frozen_sha256(self) -> str | None:
        return self.raw.get("frozen_sha256") or self.raw.get("hash")

    @property
    def decls(self) -> list[str]:
        """Declaration names the block is expected to contain, in order."""
        if self.raw.get("export"):
            return [self.raw["export"]]
        d = self.raw.get("decls")
        if isinstance(d, str):
            return [d]
        return list(d or [])

    @property
    def is_multi_decl(self) -> bool:
        return len(self.decls) > 1

    @property
    def has_paper_anchor(self) -> bool:
        """False when `source:` is absent or the placeholder `unknown`."""
        s = (self.source or "").strip()
        return bool(s) and s.lower() != "unknown"


@dataclass
class RepoConfig:
    """Everything a checker needs to know about one repo."""

    root: Path
    manifest_path: Path
    raw: dict
    nodes: list = field(default_factory=list)

    # ---- paper ------------------------------------------------------

    @property
    def paper_rel(self) -> str:
        """`paper/rotor.tex` — as written in `source_pin.file`."""
        pin = self.raw.get("source_pin") or {}
        f = pin.get("file")
        if not f:
            raise ConfigError(
                f"{self.manifest_path}: source_pin.file is missing; every "
                "checker derives the paper name from it"
            )
        return f

    @property
    def paper_path(self) -> Path:
        return self.root / self.paper_rel

    @property
    def paper_stem(self) -> str:
        """`rotor.tex` — the basename the Lean citations and `source:` use."""
        return Path(self.paper_rel).name

    @property
    def paper_sha256(self) -> str | None:
        return (self.raw.get("source_pin") or {}).get("sha256")

    @property
    def source_re(self) -> re.Pattern:
        """Matches `<paper>.tex:<a>-<b> (label <lab>)` in a node's `source:`.

        Built from the manifest, so it cannot name the wrong paper.
        """
        stem = re.escape(self.paper_stem)
        return re.compile(rf"^{stem}:(?P<a>\d+)-(?P<b>\d+)\s*(?P<rest>.*)$")

    @property
    def cite_re(self) -> re.Pattern:
        """Matches `<paper>.tex:<a>[-<b>]` anywhere in a Lean source file."""
        stem = re.escape(self.paper_stem)
        return re.compile(rf"{stem}:(\d+)(?:-(\d+))?")

    # ---- library ----------------------------------------------------

    @property
    def lib_name(self) -> str:
        """`Rotor`. Declared in the manifest, else inferred from the exports."""
        name = self.raw.get("library")
        if name:
            return name
        prefixes = {
            n.decls[0].split(".", 1)[0]
            for n in self.nodes
            if n.decls and "." in n.decls[0]
        }
        if len(prefixes) == 1:
            return next(iter(prefixes))
        # Fall back to the `file:` column: `IdlaCyl/Frozen/X.lean` -> `IdlaCyl`.
        # IDLA records unqualified declaration names, so the export prefix
        # trick cannot work there.
        roots = {
            Path(n.file).parts[0]
            for n in self.nodes
            if n.file and len(Path(n.file).parts) > 1
        }
        if len(roots) == 1:
            return next(iter(roots))
        raise ConfigError(
            f"{self.manifest_path}: cannot infer the library name "
            f"(export prefixes {sorted(prefixes) or 'none'}, "
            f"file roots {sorted(roots) or 'none'}); add a top-level "
            "`library:` key"
        )

    @property
    def lib_dir(self) -> Path:
        return self.root / self.lib_name

    @property
    def frozen_dirs(self) -> list[Path]:
        return [self.lib_dir / "Frozen", self.lib_dir / "External"]

    def production_lean_files(self) -> list[Path]:
        """Every .lean file that ships, excluding scratch and staging areas."""
        if not self.lib_dir.exists():
            return []
        skip = {".lake", "scratch", "wip", "tests", "Audit"}
        out = []
        for p in sorted(self.lib_dir.rglob("*.lean")):
            if any(part in skip for part in p.relative_to(self.root).parts):
                continue
            out.append(p)
        return out


def load(root: str | Path) -> RepoConfig:
    root = Path(root).resolve()
    mf = root / "ledger" / "manifest.yaml"
    if not mf.exists():
        raise ConfigError(f"{mf} does not exist")
    raw = yaml.safe_load(mf.read_text(encoding="utf-8")) or {}
    nodes = [Node(raw=n) for n in (raw.get("nodes") or [])]
    return RepoConfig(root=root, manifest_path=mf, raw=raw, nodes=nodes)
