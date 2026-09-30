"""The dangling-link lint (BEST_PRACTICES.md section 3, new-gate 8).

For every Markdown file in the repo, extract inline links `[text](target)`
and report each target that does not exist on disk.  `http(s)`/`mailto`
links and pure `#anchor` links are skipped; everything else is resolved
relative to the linking file's own directory (or, for a target starting
with `/`, relative to the repo root) and must exist.

Link syntax is only real inside prose: fenced code blocks and inline code
spans are blanked out before scanning, so a bracketed subscript like
``K_sigma[w](x,y)`` inside backticks is not mistaken for a link to a file
named `x,y`. A code span is allowed to run across one soft line break (real
Markdown allows this) but not across a blank line, matching CommonMark.

    python3 -m leanform_tools.linkcheck <repo>

Manhattan-Transience's README links two files that no longer exist
(`ledger/ERRATA.md`, `CONTRIBUTING.md`); this must fail there.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from .config import RepoConfig, load
from .gate import Result, run

_LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
_FENCE_RE = re.compile(r"```.*?```", re.S)
# A code span may cross a single newline (a soft break within one paragraph)
# but not a blank line (a paragraph break) — `\n(?!\n)` allows the former
# and stops at the latter.
_INLINE_CODE_RE = re.compile(r"`(?:[^`]|\n(?!\n))*?`")

# Build/VCS internals and scratch areas are not authored documentation;
# mirrors `config.py`'s own `production_lean_files` skip set.
_SKIP_DIRS = {".lake", ".git", "scratch", "wip"}


def _blank(match: re.Match) -> str:
    """Replace a matched span with spaces, preserving newlines and offsets."""
    return re.sub(r"[^\n]", " ", match.group(0))


def _strip_code(text: str) -> str:
    text = _FENCE_RE.sub(_blank, text)
    text = _INLINE_CODE_RE.sub(_blank, text)
    return text


def is_skippable(target: str) -> bool:
    t = target.strip()
    return t.startswith(("http://", "https://", "mailto:")) or t.startswith("#")


def dangling_links(md: Path) -> list[tuple[int, str]]:
    """`(line, target)` for every link in `md` whose target does not exist."""
    raw = md.read_text(encoding="utf-8", errors="replace")
    text = _strip_code(raw)
    out = []
    for m in _LINK_RE.finditer(text):
        target = m.group(1).strip()
        if is_skippable(target):
            continue
        # Drop a trailing `#anchor` and an optional ` "title"` suffix.
        target_path = target.split("#", 1)[0].split(" ", 1)[0]
        if not target_path:
            continue
        p = (
            Path(target_path)
            if target_path.startswith("/")
            else (md.parent / target_path)
        )
        if not p.exists():
            line = raw.count("\n", 0, m.start()) + 1
            out.append((line, target))
    return out


def markdown_files(cfg: RepoConfig) -> list[Path]:
    return [
        p
        for p in sorted(cfg.root.rglob("*.md"))
        if not any(part in _SKIP_DIRS for part in p.relative_to(cfg.root).parts)
    ]


def check(res: Result, cfg: RepoConfig) -> None:
    files = markdown_files(cfg)
    res.total = len(files)
    for md in files:
        res.count()
        rel = md.relative_to(cfg.root)
        for line, target in dangling_links(md):
            res.fail(f"{rel}:{line}: dangling link {target!r}")


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else "."
    cfg = load(root)
    return run("linkcheck", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
