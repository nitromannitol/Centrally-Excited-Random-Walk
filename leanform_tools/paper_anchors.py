"""Check (or repair) the paper line ranges recorded in ledger/manifest.yaml.

Each manifest node names the paper statement it formalizes as

    source: <paper>.tex:<a>-<b> (label <lab>[, ...])

The line range is derived data: it is the span of the LaTeX environment that
contains `\\label{<lab>}`.  Editing the paper anywhere above a statement shifts
that span, so the recorded range goes stale silently.  The label itself is
stable, so this tool recomputes every range from its label and reports drift.

    python3 -m leanform_tools.paper_anchors <repo>            # check
    python3 -m leanform_tools.paper_anchors <repo> --fix      # repair ranges

This is a port of the vendored `tools/paper_anchors.py` copied across
rotor-23, Parking-Sharpness, Divisible-Sandpile-Percolation, ORRW-Lower-Bound,
Divisible-Sandpile-RWRS, Dynamic-Dimensional-Reduction and Exploding-Sandpiles,
generalized to the union of what those seven repos actually need:

* `<paper>.tex`, the library directory and the citation regex all come from
  `cfg`, never from a literal — that is the point of the package.
* The label a node names is not always spelled `label <lab>`.  RWRS's
  manifest writes the bare token `(lem:fuk-nagaev)` with no `label` keyword
  at all; the vendored copy's `label\\s+...` regex found nothing for any of
  RWRS's 57 nodes and reported "0 anchors resolved, 57 carry no paper label"
  -- wrong, since the bare-token spelling is a real convention, not an
  absence of one.  `extract_label` recognizes both.
* A label may be spelled with a hyphen in the manifest and a colon in the
  paper (`thm-RW` vs `\\label{thm:RW}`, both observed in Sandpile and
  DimRed).  `label_variants` tries both.
* DimRed and Exploding define their proposition environment as `\\prop`, not
  `\\proposition` (`\\newtheorem{prop}{Proposition}`).  Every vendored copy's
  `ANCHORABLE` set said `proposition`, so every `prop:`-labelled statement in
  those two papers -- nine of them in Exploding alone -- was invisible to
  this tool.  `ANCHORABLE` here includes `prop`.
* A node citing `(cited in lem:fuk-nagaev)` (RWRS) names a label whose
  statement environment does NOT contain the node's own line range -- the
  citation is to the proof that follows the environment, not to the
  environment itself.  Recomputing this node's range from that label would
  silently retarget it, exactly the failure `paper_citations.py` already
  guards against for Lean-source citations.  Such nodes are reported as
  carrying no anchoring label, not resolved and not flagged as drift.
* Sandpile has several nodes that formalize one *part* of a single labelled
  multi-part theorem (`(label thm-main-explosion, part (iii)(a))`); several
  nodes share one label, each recording its own sub-range.  These are
  checked for containment in the label's full span, not equality.
"""

from __future__ import annotations

import re
import sys

from .config import ConfigError, RepoConfig, load
from .gate import Result, run

# A node's `source:` names its label either as `label <lab>` (rotor,
# Parking, Sandpile, ORRW, DimRed, Exploding) or, in RWRS, as a bare token
# with no keyword at all: `(lem:fuk-nagaev)`.
_LABEL_KEYWORD_RE = re.compile(r"\blabel\s+([A-Za-z][A-Za-z0-9:_-]*)")
_PLAIN_TOKEN_RE = re.compile(r"^[A-Za-z][A-Za-z0-9:_-]*$")

# A label anchoring a section/appendix/figure/table, not a statement -- such
# a node points at a subsection for context and carries its range by hand.
_SECTION_LABEL_RE = re.compile(r"^(?:(?:sub)?s?sec|app|fig|tab)[:-]")

# A node citing one part of a multi-part statement, or the context another
# label sits in: its own range is checked for containment, not equality.
PART_RE = re.compile(r"\bpart\b|\bcontext\b|\bclause\b")

_BEGIN_RE = re.compile(r"\\begin\{([A-Za-z*]+)\}")
_END_RE = re.compile(r"\\end\{([A-Za-z*]+)\}")

# Environments that carry a statement (or a display) we would ever anchor
# to. Superset of every vendored copy's list: `prop` (DimRed's and
# Exploding's spelling of `proposition`) and `remark`/`remark*` (Sandpile's
# addition) are folded in alongside the rest.
ANCHORABLE = {
    "theorem", "lemma", "proposition", "prop", "corollary", "definition",
    "problem", "remark", "remark*",
    "equation", "equation*", "align", "align*", "gather", "gather*",
}


def extract_label(rest: str) -> str | None:
    """The label a node's `source:` parenthetical names, or `None`.

    Two conventions are in use across the surveyed repos:

    1. `(label thm:main, ...)` -- explicit keyword, tried first.
    2. `(lem:fuk-nagaev)` -- RWRS's bare token, no keyword at all: the
       *entire* parenthetical, with no trailing comment at all, is a single
       identifier with no internal whitespace.

    That second rule is deliberately narrow, and deliberately requires the
    parenthetical to hold nothing but the token. It must accept
    `(prop:iid-stationary)` and reject `(cited in lem:fuk-nagaev)`, `(Carne
    1985, Varopoulos 1985, Lyons-Peres Theorem 13.4)` and `(Corollary 1.1)`:
    all three are prose, not a label. It must also reject Parking's
    `(prop:spatial-scaling, quoted from BP Theorem 1.3(i)(b))`: the label
    named there is real, but the range on this particular node is a step of
    *that statement's proof*, not the statement itself, and recomputing this
    node's range from `prop:spatial-scaling`'s span would silently retarget
    it exactly the way a mid-file Lean citation would. A first version of
    this rule took just the leading comma-separated clause and so treated
    `prop:spatial-scaling` as this node's primary anchor too, which produced
    seven false "stale anchor" reports on Parking-Sharpness (the vendored
    `label\\s+...`-only regex never had this bug, precisely because it never
    recognized the bare-token convention at all).
    """
    m = _LABEL_KEYWORD_RE.search(rest)
    if m:
        return m.group(1)
    inner = rest.strip()
    if inner.startswith("(") and inner.endswith(")"):
        body = inner[1:-1].strip()
        if _PLAIN_TOKEN_RE.match(body):
            return body
    return None


def label_variants(label: str) -> list[str]:
    """The spellings `label` may have in the paper.

    A manifest may write a label with a hyphen where the paper's `\\label`
    uses a colon, or vice versa (`thm-RW` / `\\label{thm:RW}`, `prop-
    base_case` / `\\label{prop:base_case}`): both are observed, in both
    directions, across Sandpile and DimRed. Only the *first* separator is
    swapped -- the rest of the label (`fuk-nagaev`, `base_case`) keeps
    whatever punctuation it already has.
    """
    out = [label]
    m = re.match(r"^([A-Za-z0-9]+)([-:])(.+)$", label)
    if m:
        swapped = ":" if m.group(2) == "-" else "-"
        alt = m.group(1) + swapped + m.group(3)
        if alt not in out:
            out.append(alt)
    return out


def span_of_label(lines: list[str], label: str) -> tuple[int, int]:
    """1-indexed inclusive span of the environment containing \\label{label}.

    Tries every spelling from `label_variants` before giving up.
    """
    text = "\n".join(lines)
    resolved = label
    for cand in label_variants(label):
        if text.count(f"\\label{{{cand}}}") == 1:
            resolved = cand
            break
    label = resolved
    marker = f"\\label{{{label}}}"
    hits = [i for i, line in enumerate(lines) if marker in line]
    if len(hits) != 1:
        raise LookupError(f"label {label!r} occurs {len(hits)} times, want 1")
    at = hits[0]

    # Walk up to the innermost enclosing anchorable \begin, tracking depth so
    # a nested environment that closes above us is not mistaken for our
    # opener.
    depth = 0
    start = None
    for i in range(at, -1, -1):
        for env in _END_RE.findall(lines[i]):
            if i != at and env in ANCHORABLE:
                depth += 1
        for env in _BEGIN_RE.findall(lines[i]):
            if env not in ANCHORABLE:
                continue
            if depth:
                depth -= 1
            else:
                start = (i, env)
                break
        if start:
            break
    if start is None:
        raise LookupError(f"label {label!r} is not inside an anchorable environment")

    i0, env = start
    depth = 0
    for j in range(i0 + 1, len(lines)):
        if re.search(rf"\\begin\{{{re.escape(env)}\}}", lines[j]):
            depth += 1
        if re.search(rf"\\end\{{{re.escape(env)}\}}", lines[j]):
            if depth:
                depth -= 1
            else:
                return i0 + 1, j + 1
    raise LookupError(f"environment {env} opened at line {i0 + 1} never closes")


def check(res: Result, cfg: RepoConfig, fix: bool = False) -> None:
    if not cfg.paper_path.exists():
        raise ConfigError(f"paper not found at {cfg.paper_path}")
    lines = cfg.paper_path.read_text(encoding="utf-8").splitlines()

    anchored = [n for n in cfg.nodes if n.source and cfg.source_re.match(n.source)]
    res.total = len(anchored)

    no_label = 0
    labeled = 0
    stale: list[tuple[str, str, str, str]] = []
    part_violations: list[str] = []
    unresolvable: list[str] = []

    for node in anchored:
        res.count()
        m = cfg.source_re.match(node.source)
        a0, b0, rest = int(m.group("a")), int(m.group("b")), m.group("rest")
        label = extract_label(rest)
        if label is None:
            no_label += 1
            res.note(f"{node.id}: carries no paper label ({node.source!r})")
            continue
        if _SECTION_LABEL_RE.match(label):
            no_label += 1
            res.note(f"{node.id}: label {label!r} anchors a section/appendix/"
                      "figure/table, not a statement")
            continue
        try:
            a, b = span_of_label(lines, label)
        except LookupError as exc:
            unresolvable.append(f"{node.id}: UNRESOLVABLE ({label}): {exc}")
            continue
        labeled += 1
        if PART_RE.search(rest):
            if not (a <= a0 <= b0 <= b):
                part_violations.append(
                    f"{node.id}: part range {a0}-{b0} is not inside "
                    f"{cfg.paper_stem}:{a}-{b} (label {label})"
                )
            continue
        if (a0, b0) == (a, b):
            continue
        want = f"{cfg.paper_stem}:{a}-{b}"
        new_source = f"{want} {rest}".strip() if rest else want
        stale.append((node.id, node.source, new_source, label))

    for msg in unresolvable:
        res.fail(msg)
    for msg in part_violations:
        res.fail(msg)

    if anchored and labeled == 0:
        res.fail(
            f"every one of {len(anchored)} node(s) carrying a paper anchor "
            "carries no paper label; nothing could be verified -- this is a "
            "meta-check failure for paper_anchors specifically, not an OK"
        )

    if fix and stale:
        text = cfg.manifest_path.read_text(encoding="utf-8")
        applied = 0
        for nid, old, new, _label in stale:
            before = f"    source: {old}\n"
            if before not in text:
                res.fail(f"{nid}: cannot repair -- no verbatim `source:` line "
                         "found in the manifest")
                continue
            text = text.replace(before, f"    source: {new}\n", 1)
            applied += 1
        if applied:
            cfg.manifest_path.write_text(text, encoding="utf-8")
            res.note(f"repaired {applied} stale anchor(s)")
    else:
        for nid, old, new, label in stale:
            res.fail(f"{nid}: stale anchor (label {label})\n"
                      f"        was: {old}\n        now: {new}")
        if stale:
            res.note("rerun with --fix to repair the resolvable ones")

    res.note(f"{len(anchored)} node(s) carry a paper anchor, {labeled} "
              f"resolved to a label, {no_label} carry no paper label")


def main(argv: list[str]) -> int:
    fix = "--fix" in argv[1:]
    root = next((a for a in argv[1:] if not a.startswith("--")), ".")
    cfg = load(root)
    return run("paper_anchors", check, cfg, fix=fix)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
