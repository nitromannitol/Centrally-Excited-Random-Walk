"""Check (or repair) the `<paper>.tex:<a>-<b>` citations inside Lean sources.

The docstrings point at the paper by line range. Line ranges are derived
data: inserting a paragraph anywhere above a statement shifts every citation
below it, silently. A citation that also names the LaTeX `\\label` can be
recomputed, so this tool resolves those and repairs them. A citation with no
nearby label points into the middle of a proof and cannot be resolved
mechanically; those are listed so they can be checked by hand or dropped.

    python3 -m leanform_tools.paper_citations <repo>            # check
    python3 -m leanform_tools.paper_citations <repo> --fix       # repair
    python3 -m leanform_tools.paper_citations <repo> --list-unanchored

This is a port of the vendored `tools/paper_citations.py`, generalized to the
union of what the seven surveyed repos need:

* The citation regex (`cfg.cite_re`) and the library directory (`cfg.lib_dir`)
  come from `cfg`. The Parking-Sharpness and Divisible-Sandpile-RWRS
  vendored copies both hardcoded `CITE_RE = re.compile(r"rotor\\.tex:...")`
  -- a leftover from whichever repo the file was first copied from -- so
  neither ever matched a real citation in its own tree and both exited 0
  having inspected nothing: Parking has 426 `parking.tex:` citations sitting
  unchecked, RWRS has 145 `rwrs.tex:` citations. DimRed's and Exploding's
  copies carried the identical literal, with the identical effect (94 and 24
  citations respectively, unchecked). Deriving the regex from
  `cfg.paper_stem` is the entire fix.
* Only a Frozen file's header docstring is ever eligible for repair -- never
  `External/`, whose header cites another paper's or source's line numbers,
  and never a citation elsewhere in the file, which points into a proof and
  would be silently retargeted by re-anchoring it from a nearby label. This
  restriction is preserved exactly as the vendored copies had it; see
  `_is_frozen_header` below.
* A frozen file's header may cite one *part* of the label's full span
  (Sandpile has several Frozen files, one per part of a multi-part theorem,
  each citing only its own part's lines). When the manifest itself records
  that exact citation for that file, it is trusted over the recomputed full
  span of the label -- otherwise every one of those headers would be
  reported as perpetually "stale" against a span it never claimed to equal.
"""

from __future__ import annotations

import re
import sys

from .config import ConfigError, RepoConfig, load
from .gate import Result, run
from .paper_anchors import span_of_label

# A frozen file opens with a header docstring naming the paper statement it
# transcribes: its LaTeX label and its line range. Three wordings are in use
# (citation before the label, after it, or with another backticked token in
# between), so rather than match a wording, take the whole leading `/- ... -/`
# block: it names exactly one primary label, and the citation in it is that
# statement's. A citation anywhere else in the file points into a proof and
# is left alone -- re-anchoring it from a nearby label would silently
# retarget it.
HEADER_LABEL_RE = re.compile(r"label\s+`([A-Za-z][A-Za-z0-9:_-]*)`")


def header_block(text: str) -> tuple[int, int] | None:
    """Offsets of the leading `/- ... -/` docstring, if the file opens with one."""
    if not text.startswith("/-"):
        return None
    end = text.find("-/")
    return (0, end) if end > 0 else None


def _is_frozen_header(path, frozen_dir) -> bool:
    """True only for a file directly under `<lib>/Frozen`.

    `External/` is deliberately excluded: an external-input file's header
    cites the source it carries as a hypothesis, on its own terms, not a
    span this tool's label-driven recomputation understands.
    """
    try:
        path.relative_to(frozen_dir)
    except ValueError:
        return False
    return True


def check(res: Result, cfg: RepoConfig, fix: bool = False,
          list_unanchored: bool = False) -> None:
    if not cfg.paper_path.exists():
        raise ConfigError(f"paper not found at {cfg.paper_path}")
    lines = cfg.paper_path.read_text(encoding="utf-8").splitlines()

    # The range a frozen file's header should cite is the one the manifest
    # records for its node, not necessarily the whole environment the label
    # anchors: a node formalizing one part of a multi-part theorem cites its
    # own part.
    recorded: dict[str, str] = {}
    for n in cfg.nodes:
        if not n.file or not n.source:
            continue
        m = cfg.cite_re.search(n.source)
        if m:
            recorded[n.file] = m.group(0)

    frozen_dir = cfg.lib_dir / "Frozen"
    lean_files = sorted(cfg.lib_dir.rglob("*.lean")) if cfg.lib_dir.exists() else []

    ok = 0
    stale: list[tuple] = []
    unanchored: list[tuple] = []
    unresolvable: list[tuple] = []

    for path in lean_files:
        text = path.read_text(encoding="utf-8")
        block = header_block(text) if _is_frozen_header(path, frozen_dir) else None
        primary_label, primary_at = None, None
        if block:
            lab = HEADER_LABEL_RE.search(text[block[0]:block[1]])
            cite = cfg.cite_re.search(text[block[0]:block[1]])
            if lab and cite and abs(lab.start() - cite.start()) <= 120:
                primary_label, primary_at = lab.group(1), cite.start()

        out, cursor, changed = [], 0, False
        for m in cfg.cite_re.finditer(text):
            out.append(text[cursor:m.start()])
            cursor = m.end()
            res.count()
            label = primary_label if m.start() == primary_at else None
            if label is None:
                unanchored.append((path, text[:m.start()].count("\n") + 1, m.group(0)))
                out.append(m.group(0))
                continue
            rel = str(path.relative_to(cfg.root))
            if rel in recorded:
                want = recorded[rel]
            else:
                try:
                    a, b = span_of_label(lines, label)
                except LookupError as exc:
                    unresolvable.append((path, m.group(0), label, str(exc)))
                    out.append(m.group(0))
                    continue
                want = f"{cfg.paper_stem}:{a}-{b}"
            if want == m.group(0):
                ok += 1
                out.append(m.group(0))
            else:
                stale.append((path, text[:m.start()].count("\n") + 1,
                              m.group(0), want, label))
                out.append(want)
                changed = True
        out.append(text[cursor:])
        if changed and fix:
            path.write_text("".join(out), encoding="utf-8")

    res.total = ok + len(stale) + len(unanchored) + len(unresolvable)

    for path, got, label, why in unresolvable:
        res.fail(f"{path.relative_to(cfg.root)}  {got}: UNRESOLVABLE ({label}): {why}")

    if fix and stale:
        res.note(f"repaired {len(stale)} citation(s)")
    else:
        for path, line, got, want, label in stale:
            res.fail(f"{path.relative_to(cfg.root)}:{line}  {got} -> {want}  "
                      f"(label {label})")
        if stale:
            res.note("rerun with --fix to repair the resolvable ones")

    if list_unanchored:
        for path, line, got in unanchored:
            res.note(f"{path.relative_to(cfg.root)}:{line}  {got}: not anchored "
                      "to a label (points into a proof; verify by hand)")

    res.note(f"{ok} correct, {len(stale)} stale, {len(unanchored)} not anchored "
              f"to a label, {len(unresolvable)} unresolvable")


def main(argv: list[str]) -> int:
    fix = "--fix" in argv[1:]
    list_unanchored = "--list-unanchored" in argv[1:]
    root = next((a for a in argv[1:] if not a.startswith("--")), ".")
    cfg = load(root)
    return run("paper_citations", check, cfg, fix=fix, list_unanchored=list_unanchored)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
