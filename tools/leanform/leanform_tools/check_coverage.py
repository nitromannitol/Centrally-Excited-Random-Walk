"""Check that every theorem-like statement in the paper is claimed.

The manifest says which paper statement each Lean node transcribes. This asks
the complementary question, which no other checker asks: is there a statement
in the paper that no node claims? A formalization can be entirely axiom-clean
and still be silently incomplete, so the gap is worth a gate of its own.

`problem` and open-problem environments are excluded: they are questions, not
claims. They are excluded simply by never appearing in `STATEMENT_ENVS`.

    python3 -m leanform_tools.check_coverage <repo>

This is a port of the vendored `tools/check_coverage.py`, generalized to the
union of what the seven surveyed repos need:

* The paper path, its basename and the claim regex all come from `cfg`.
* `STATEMENT_ENVS` includes `definition` (the task this package exists for)
  and `prop` -- DimRed and Exploding define their proposition environment as
  `\\prop`, not `\\proposition`. The rotor/Parking/ORRW/RWRS/Sandpile vendored
  copies never noticed because none of those five papers use the alias; the
  DimRed and Exploding copies used the same `STATEMENT_ENVS` regardless, so
  every `\\begin{prop}` statement in those two papers -- corollaries and
  propositions alike, nine of them in Exploding -- was invisible to
  `check_coverage.py` even though it exited 0 having "covered" every
  statement it looked at.
* An unlabeled statement environment is a hard error, reported distinctly
  from an uncovered one (only Sandpile's vendored copy did this; rotor,
  Parking, ORRW, RWRS, DimRed and Exploding's copies required a `\\label`
  immediately after `\\begin{env}` to even recognize the environment as a
  statement, so an unlabeled one was silently invisible rather than
  flagged). Running this rule against DimRed and Exploding turns up real,
  previously invisible unlabeled statements: DimRed has an unlabeled
  corollary at dimred.tex:143 and an unlabeled lemma at dimred.tex:728;
  Exploding has an unlabeled `\\prop` at exploding.tex:1965.
* A node's claim on a label is recognized by substring search over the
  node's whole `source:` text (canonicalized for the hyphen/colon ambiguity
  `paper_anchors.label_variants` already handles), not by requiring a
  `label <lab>` keyword or a `thm:`/`lem:`-style prefix. This is what lets a
  claim that never carries a paper line citation at all still count --
  Sandpile's `thm-RW` node is later "discharged by thm-optimal-stopping-
  proved" in prose, with no `sandpile.tex:` citation anywhere on that line,
  and DimRed's and RWRS's labels (`the_theorem`, `axis_monotonicity`,
  `prop:iid-stationary`) do not share a common prefix family at all.
"""

from __future__ import annotations

import re
import sys

from .config import ConfigError, RepoConfig, load
from .gate import Result, run
from .paper_anchors import label_variants

# `problem`/`openproblem`/`open-problem` are deliberately absent: they are
# questions, not claims, and are excluded simply by omission here.
STATEMENT_ENVS = ("theorem", "lemma", "proposition", "prop", "corollary",
                   "definition")

_STATEMENT_RE = re.compile(
    r"\\begin\{(" + "|".join(re.escape(e) for e in STATEMENT_ENVS) + r")\}"
    r"(.*?)\\end\{\1\}",
    re.DOTALL,
)
_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


def _strip_comments(text: str) -> str:
    """Drop `%...` comments while preserving line numbers."""
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def check(res: Result, cfg: RepoConfig) -> None:
    if not cfg.paper_path.exists():
        raise ConfigError(f"paper not found at {cfg.paper_path}")
    text = _strip_comments(cfg.paper_path.read_text(encoding="utf-8"))

    # The corpus a claim is searched in: every node's whole `source:` text,
    # not just the primary label slot, so a prose mention (Sandpile's
    # "discharged by thm-optimal-stopping-proved") counts as a claim.
    claimed_blob = "\n".join(n.source for n in cfg.nodes if n.source)

    statements: list[tuple[str, str, int]] = []
    unlabeled: list[tuple[str, int]] = []
    seen: set[str] = set()
    for m in _STATEMENT_RE.finditer(text):
        kind, body = m.group(1), m.group(2)
        line = text[:m.start()].count("\n") + 1
        lm = _LABEL_RE.search(body)
        if lm is None:
            unlabeled.append((kind, line))
            continue
        label = lm.group(1)
        if label in seen:
            continue
        seen.add(label)
        statements.append((kind, label, line))

    res.total = len(statements) + len(unlabeled)

    uncovered = []
    for kind, label, line in statements:
        res.count()
        variants = label_variants(label)
        if not any(re.search(rf"\b{re.escape(v)}\b", claimed_blob) for v in variants):
            uncovered.append((kind, label, line))

    for kind, line in unlabeled:
        res.count()
        res.fail(f"{cfg.paper_stem}:{line}: UNLABELED {kind} environment -- "
                 "fix the paper, not the checker")

    for kind, label, line in uncovered:
        res.fail(f"{cfg.paper_stem}:{line}: {kind} {label} is not claimed by "
                 "any manifest node")

    represented = len(statements) - len(uncovered)
    res.note(f"{len(statements) + len(unlabeled)} statements in the paper, "
              f"{represented} represented")
    if unlabeled:
        res.note(f"{len(unlabeled)} unlabeled statement environment(s) -- "
                  "these cannot be claimed by any node until labeled")


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else "."
    cfg = load(root)
    return run("check_coverage", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
