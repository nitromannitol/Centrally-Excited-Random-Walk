"""Every node must be read against the paper; report where the counts disagree.

Every other checker in this package compares a statement with *itself*: the
hash pins the bytes, the axiom check pins the proof. None of them notices
when a frozen statement quietly asserts less than the paper statement it
claims to transcribe. That is how, in the formalization this tooling comes
from, one lemma came to be frozen without one of the three displays its
paper statement asserts, while every other gate passed.

The gate this checker actually enforces: **every node must have a reading in
`readings.yaml['clauses']`** (see `readings.py` for the schema) — a node with
no recorded reading fails, unconditionally. That reading is where a human
states what the paper asserts and what the Lean statement asserts, in
prose a regex cannot produce or verify.

On top of that mandatory gate, this also runs the vendored heuristic as a
*note*, never a failure: it counts assertion units on each side and reports
the pairs where the paper appears to assert more.

  paper   displayed equations and enumerated items inside the paper's line range
  Lean    top-level conjuncts of the frozen statement's conclusion

The counts are a heuristic, not a proof of correspondence: one Lean conjunct
can faithfully carry two paper displays, and one paper display can need
three Lean conjuncts. So a mismatch is a prompt to look at the (mandatory)
reading, not a verdict on its own. A node whose `source:` does not name a
`<paper>.tex:<a>-<b>` range (an external-input node, say) simply skips the
heuristic; it still needs a clauses reading like every other node.

The paper's basename and its line-range regex come from `cfg.source_re`,
built in `config.py` from `ledger/manifest.yaml`'s `source_pin.file` —
**never** a literal paper name. A hardcoded `rotor\\.tex` regex in two
vendored copies of this checker (used in repos whose paper was not
`rotor.tex`) made it match zero of either repo's nodes and exit 0 anyway;
that silent vacuous pass is exactly what `gate.py`'s meta-check exists to
turn into exit 2, and is why every node here counts as "inspected" (via
`res.count()`) whether or not its `source:` happens to resolve a line range —
only a manifest with no nodes at all is allowed to inspect nothing.

    python3 -m leanform_tools.check_clauses <repo>
"""

from __future__ import annotations

import re
import sys

from . import lean_source as ls
from . import readings as rd
from .config import RepoConfig, load
from .gate import Result, run

RELATION = re.compile(r"\\leq|\\geq|\\neq|\\subseteq|(?<!\\not)\\in\b|<|>|=")


def paper_units(segment: str) -> int:
    """Assertions in a paper segment: relations inside displays, plus `\\item`s.

    Counting displays alone undercounts, because a paper often puts several
    assertions in one display separated by `\\qquad`. Counting relation
    symbols inside displayed math tracks the real number of things asserted.
    `\\coloneqq` is a definition, not an assertion, and is not counted; nor
    is anything outside a display.
    """
    body = []
    for m in re.finditer(
        r"\\begin\{(?:equation|align|gather)\*?\}(.*?)\\end\{(?:equation|align|gather)\*?\}",
        segment, re.S,
    ):
        body.append(m.group(1))
    for m in re.finditer(r"(?<!\\)\\\[(.*?)(?<!\\)\\\]", segment, re.S):
        body.append(m.group(1))
    n = 0
    for b in body:
        b = re.sub(r"\\text\{[^}]*\}", " ", b)
        b = b.replace("\\coloneqq", " ").replace("\\colon", " ")
        b = re.sub(r"\\begin\{cases\}.*?\\end\{cases\}", " ", b, flags=re.S)
        n += len(RELATION.findall(b))
    n += len(re.findall(r"\\item\b", segment))
    return max(n, 1) if body or "\\item" in segment else 0


def lean_conjuncts(block: str) -> int:
    """Top-level `∧` of the conclusion.

    The conclusion begins after the last `:` that sits at bracket depth
    zero: every binder is inside `(`, `{` or `[`, so its own `:` is at depth
    one or more. Conjuncts are then the depth-zero `∧` after that point.
    """
    depth, last_colon = 0, None
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            last_colon = i
    concl = block[last_colon + 1:] if last_colon is not None else block
    depth, n = 0, 1
    for ch in concl:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "∧" and depth == 0:
            n += 1
    return n


def _frozen_block(cfg: RepoConfig, node) -> tuple[str | None, str | None]:
    """The node's frozen block body, or `(None, reason)` it could not be read."""
    if not node.file:
        return None, f"{node.id}: no file: recorded"
    path = cfg.root / node.file
    if not path.exists():
        return None, f"{node.id}: file {node.file} does not exist"
    src = path.read_text(encoding="utf-8")
    spans = ls.frozen_blocks(src)
    if len(spans) != 1 or spans[0][1] < 0:
        return None, f"{node.id}: expected exactly one frozen block in {node.file}, found {len(spans)}"
    return ls.block_body(src, spans[0]), None


def check(res: Result, cfg: RepoConfig) -> None:
    res.total = len(cfg.nodes)

    clause_readings = rd.load_readings(cfg).get("clauses", {})

    paper_lines: list[str] | None = None
    if cfg.paper_path.exists():
        paper_lines = cfg.paper_path.read_text(encoding="utf-8").splitlines()
    else:
        res.fail(
            f"{cfg.paper_rel} does not exist; the paper-vs-Lean assertion-count "
            "heuristic cannot run for any node (the mandatory reading check "
            "below still runs)"
        )

    print(f"{'node':28s} {'paper':>6s} {'lean':>6s}")
    flagged = 0
    for node in cfg.nodes:
        nid = node.id
        # Every node is genuinely inspected here: it is checked for a
        # mandatory reading regardless of whether its source resolves a
        # paper line range.
        res.count()

        reading = clause_readings.get(nid)
        if not reading:
            res.fail(
                f"{nid}: no reading in readings.yaml['clauses'] — every node "
                "must be read against the paper before check_clauses can pass"
            )

        m = cfg.source_re.match(node.source or "") if node.source else None
        if not m or paper_lines is None:
            if m is None:
                res.note(
                    f"{nid}: source {node.source!r} does not name a "
                    f"`{cfg.paper_stem}:<a>-<b>` range; assertion-count "
                    "heuristic skipped (a clauses reading is still required)"
                )
            print(f"  {nid:26s} {'--':>6s} {'--':>6s}")
            continue

        a, b = int(m["a"]), int(m["b"])
        segment = "\n".join(paper_lines[a - 1:b])
        block, err = _frozen_block(cfg, node)
        if err:
            res.fail(err)
            print(f"  {nid:26s} {'--':>6s} {'--':>6s}")
            continue

        p, l = paper_units(segment), lean_conjuncts(block)
        print(f"  {nid:26s} {p:6d} {l:6d}" + ("  <-- paper asserts more" if p > l else ""))
        if p > l:
            flagged += 1
            res.note(
                f"{nid}: paper's assertion-unit count ({p}) exceeds Lean's "
                f"top-level conjunct count ({l}) — a prompt to re-read, not "
                "a verdict on its own"
            )

    print()
    for node in cfg.nodes:
        print(f"  {node.id}: {clause_readings.get(node.id, 'NOT REVIEWED')}")


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else "."
    cfg = load(root)
    return run("check_clauses", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
