"""Check that every existential constant is bound before every paper parameter
it is said not to depend on.

A paper constant is almost always introduced as "depending only on `d`" (or
whatever the fixed structural parameters are) and explicitly *not* on the
quantities that vary — the scale, the time, the error, the point. In Lean
that is a property of quantifier order, not of naming:

    theorem foo {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ : 1 ≤ β) : ∃ c, ... β ... n ...

reads as `∀ β, ∃ c(β)`, which lets the constant absorb any power of `β` and
makes a factor like `β^{-d/(d+1)}` decorative — the statement would hold
with the wrong exponent, or with none. That is a silent weakening invisible
to every other check in this package (the hash pins the bytes; this checks
what the bytes actually quantify over), so it gets its own gate.

The rule enforced: in a frozen statement that binds a real-valued
existential in its conclusion, none of the names in `FORBIDDEN` may already
be a *theorem parameter* — they must be quantified inside the conclusion,
after the existential, so the constant is genuinely chosen before them.

`FORBIDDEN` is the union of the forbidden-name lists actually used across
the surveyed repos' vendored copies of this checker (a mix of Latin scale/
point letters and the small set of Greek error letters). It is a fixed
heuristic vocabulary of the kind of single-letter names these papers bind as
varying parameters, not a per-paper literal — deliberately, since this file
must not name a paper. A repo whose own convention needs a name outside this
set, or whose existential genuinely and correctly depends on one of these
names for a reason specific to that paper, records that in
`readings.yaml['constants']` (see `readings.py`) rather than by editing this
list.

The binder list is split at the FIRST depth-zero `:`, not the last: every
theorem parameter sits inside a top-level bracket, so its own `:` is at
depth one or more, and the first depth-zero `:` is the one separating the
binders from the conclusion. Taking the *last* depth-zero `:` would run past
an existential's own `∃ c : ℝ` in the conclusion and read `c` as hidden away
in what this checker treats as "binders", exactly hiding the dependency this
check exists to catch. One vendored copy (`Unique-Continuation-Planar`) also
found parameters with a bracket-oblivious regex that reads any `(name : T)`
substring anywhere in the block, including a type ascription or a `Var(...)`
nested two brackets deep inside a hypothesis's *body* — reporting a
dependence the statement does not have. `parameters()` here tracks bracket
depth and only reads names out of a bracket group that is itself top-level.

Per-node waivers come from `readings.yaml['constants']`; a node's waiver, if
one is recorded, is printed on every run regardless of whether the node is
currently flagged, so a waiver never disappears from the log silently.

    python3 -m leanform_tools.check_constants <repo>
"""

from __future__ import annotations

import re
import sys

from . import lean_source as ls
from . import readings as rd
from .config import RepoConfig, load
from .gate import Result, run

# The union of the forbidden-name lists used by the surveyed repos' vendored
# copies of this checker: generic scale/point/error letters (six of the
# seven target repos share this exact list) plus ORRW-Lower-Bound's smaller,
# differently-lettered convention (β, k, h; ORRW does not use R/t/m/r/s/L/
# x/y/u/v/e/z/ε/η/δ as varying-parameter names at all). Neither list is a
# superset of the other, so the union is what makes one fixed vocabulary
# work for both without a per-repo literal.
FORBIDDEN = frozenset({
    "R", "n", "t", "m", "r", "s", "L", "x", "y", "u", "v", "e", "z",
    "ε", "η", "δ", "β", "k", "h",
})

# Only a real-valued existential is a *constant* in the sense this check
# cares about. An existential over a non-ℝ type (an ordering, a witness
# function) is not a numerical constant and is outside this check.
CONSTANT = re.compile(r"∃\s+[^,:]*:\s*ℝ")


def split_statement(block: str) -> tuple[str, str]:
    """(binders, conclusion), split at the FIRST `:` outside every bracket.

    See the module docstring: taking the *last* such `:` instead would cut
    inside `∃ c : ℝ` and hide the existential in the binders.
    """
    depth = 0
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            return block[:i], block[i + 1:]
    return block, ""


def parameters(binders: str) -> set[str]:
    """Variable names bound as theorem parameters.

    Only a TOP-LEVEL bracket group is a binder. A type ascription inside the
    body of a hypothesis — `(m : ℝ)` in a cast, `Var(...)` inside a display
    — sits at depth two or more and binds nothing, so reading it as a
    parameter would report a dependence the statement does not have. Within
    a top-level group the names are those before its own first `:`.
    """
    names: set[str] = set()
    depth, start = 0, None
    for i, ch in enumerate(binders):
        if ch in "([{⟨":
            if depth == 0:
                start = i + 1
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
            if depth == 0 and start is not None:
                group, inner = binders[start:i], 0
                for j, c in enumerate(group):
                    if c in "([{⟨":
                        inner += 1
                    elif c in ")]}⟩":
                        inner -= 1
                    elif c == ":" and inner == 0:
                        for tok in group[:j].split():
                            names.add(tok)
                        break
                start = None
    return names


def _frozen_block(cfg: RepoConfig, node) -> tuple[str | None, str | None]:
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
    waivers = rd.load_readings(cfg).get("constants", {})

    print(f"{'node':28s} {'real constant?':15s} {'offenders':22s}")
    for node in cfg.nodes:
        nid = node.id
        block, err = _frozen_block(cfg, node)
        if err:
            res.fail(err)
            continue
        res.count()

        binders, concl = split_statement(block)
        has_exists = bool(CONSTANT.search(concl))
        params = parameters(binders)
        offenders = sorted(params & FORBIDDEN)

        waiver = waivers.get(nid)
        if waiver:
            # Printed on every run, whether or not this node is currently
            # flagged — a waiver must never vanish from the log silently.
            print(f"  {nid}: waiver on record — {waiver}")

        mark = ""
        if has_exists and offenders:
            if waiver:
                res.note(
                    f"{nid}: existential constant is bound after "
                    f"{', '.join(offenders)}; waived — {waiver}"
                )
                mark = "  <-- waived, see above"
            else:
                res.fail(
                    f"{nid}: existential constant may depend on "
                    f"{', '.join(offenders)} (bound before it, not after); "
                    "move the constant after them or record a waiver in "
                    "readings.yaml['constants']"
                )
                mark = "  <-- CONSTANT MAY DEPEND ON " + ", ".join(offenders)
        print(
            f"  {nid:26s} {'yes' if has_exists else 'no':13s} "
            f"{', '.join(offenders) if offenders else '-':20s}{mark}"
        )


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else "."
    cfg = load(root)
    return run("check_constants", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
