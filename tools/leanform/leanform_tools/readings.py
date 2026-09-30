"""Per-repo audit prose for the reading-side checkers, externalized.

`check_clauses.py`, `check_constants.py` and `check_exponents.py` all need a
place to record something a regex cannot decide: that a human read a
statement against the paper and either endorsed the correspondence or
recorded why an apparent gap is not really a gap. In the vendored per-repo
tools that prose was an inline Python dict (`REVIEWED` / `EXPECTED_ABSENT`),
which is why `check_clauses.py` alone ran to 2359 lines in one repo. That
prose is genuinely per-repo data — it cites line numbers and Lean names from
one specific paper and one specific library — so it cannot live in this
shared package. It also must not be lost when a checker is ported here.

This module is the boundary: it reads `<root>/ledger/readings.yaml` (writing
one is entirely the downstream repo's job; this package only reads it) and
provides a one-shot migration helper that recovers the old inline dicts from
an incumbent `tools/` directory by parsing the Python source as a syntax
tree — never by importing or executing it — and writing them out in the new
shape.

## Schema

```yaml
clauses:
  <node-id>: "<prose reading of this statement against the paper>"

constants:
  <node-id>: "<why this quantifier order is correct / waiver reason>"

exponents:
  <node-id>:
    - kind: notation | general | split | context | definition
      detail: "<what differs and why it is expected>"

noise:
  - "<bare superscript token that is never a genuine exponent in this paper>"
```

`clauses` and `constants` hold one string per node. `exponents` holds a list
per node because one node can have several independent expected differences
(a notational respelling *and* a split with a sibling node, say). `noise`
is the one section that is NOT keyed by node id: which bare symbols a paper
uses as decoration rather than as a genuine exponent is a property of the
*paper*, not of any one statement — ORRW's `(A^+)^c` (set-complement
notation) makes `c` decorative everywhere that paper writes it, the same
way `check_exponents.py`'s shared `NOISE` constant already treats `j`, `n`,
`k`, `m`, `i` as decorative everywhere in the repos that share that
vocabulary. `noise` entries are unioned with the shared default at runtime;
they are never merged into the shared constant itself, because a symbol
that is decoration in one paper (ORRW's `d`) is a load-bearing exponent in
another (Dynamic-Dimensional-Reduction's `prop-no-reduction` genuinely
needs `d` tracked) — widening `NOISE` globally to fix one repo would
silently blind every other repo to a real gap in exactly that repo's own
vocabulary.

### Waiver granularity is per node, not per offending item

The incumbent `EXPECTED_ABSENT` and constants' `REVIEWED` dicts were keyed by
the literal offending string (an exact exponent spelling, a single forbidden
parameter name). That is fragile in two ways this schema deliberately avoids:
it silently breaks if the checker's own canonicalization changes the printed
spelling by one character, and it gives no natural single-string shape for
`constants` (a node can have more than one offending parameter, but the
schema asks for exactly one string).

So a reading here waives at the level of the *node*: if
`readings.yaml['constants'][node_id]` exists, it is printed and it suppresses
a quantifier-order failure for every forbidden parameter that node's
existential currently depends on. If `readings.yaml['exponents'][node_id]` is
a non-empty list, it is printed and it suppresses an exponent-mismatch
failure for every paper exponent occurrence missing from that node's Lean
statement. The trade is precision (a waiver no longer names exactly which
offending item it excuses) for robustness (rewording the paper, or changing
how an exponent is canonicalized, does not silently reintroduce an
unreviewed gap under a stale key). `check_clauses.py` has no such waiver: a
clauses reading is mandatory for every node, full stop.

## Migration

    python3 -m leanform_tools.readings --extract <repo-path> [--out <dir>]

Reads `<repo-path>/tools/check_clauses.py` (`REVIEWED: dict[str, str]`),
`<repo-path>/tools/check_constants.py` (`REVIEWED: dict[str, dict[str, str]]`,
node -> {parameter -> reason}) and `<repo-path>/tools/check_exponents.py`
(`EXPECTED_ABSENT: dict[str, dict[str, str]]`, node -> {exponent -> reason}),
each via `ast.parse` + `ast.literal_eval` on the assignment's value node —
the file is never imported or exec'd, so it cannot run arbitrary code just
by being migrated. Any of the three source files may be absent (not every
repo has all three checkers, or has waivers in all three); a missing file or
a missing variable yields an empty contribution, not an error.

The per-parameter constants dict is flattened to one string per node
(`"name: reason; name2: reason2"`, sorted by name) since the schema holds a
single string. The per-exponent dict becomes a list of `{kind, detail}`:
`kind` is read off the reason's own leading word (every incumbent reason
already starts with one of `notation:`, `general:`, `split:`, `context:` or
`definition:`); a reason that starts with none of those is filed under
`context` and the mismatch is left visible in the output so it can be
reviewed by hand. `detail` keeps the original exponent spelling prefixed onto
the reason text, so the specific string that triggered the waiver is not
discarded even though the schema does not give it its own field.

`check_exponents.py`'s own module-level `NOISE` set (if the incumbent has
one) is read the same way and written to the top-level `noise` list — this
is what recovers ORRW's `{d, c, M, R, ...}` vocabulary of decorative bare
symbols without ever merging it into this package's own shared `NOISE`
constant (see the schema section above for why that distinction matters).

### The foreign-key guard

Before writing, every `clauses`/`constants`/`exponents` entry is checked
against the *target* repo's own `ledger/manifest.yaml` node ids
(`drop_foreign_keys`); an entry whose key is not one of that repo's own
nodes is refused and counted, never written. This exists because
Dynamic-Dimensional-Reduction and Exploding-Sandpiles each carry a
`REVIEWED`/`EXPECTED_ABSENT` dict that was never updated when their
`tools/check_*.py` were copied out of rotor-23: every key in both dicts is
a rotor-23 node id, and not one matches either repo's own manifest.
Migrating that verbatim would be strictly worse than the vacuous pass it
replaces: instead of a checker that visibly inspected nothing, it would be
one that reports real-looking, confidently-wrong readings about a
different paper. The refusal is loud (`REFUSED <n> entr(ies) ...`, printed
to stdout) so a repo in this state is left with an empty `readings.yaml`
and an explicit todo, not a silently wrong one.

Writes `<out-dir>/ledger/readings.yaml` (default `<repo-path>/ledger/`).
Never writes anywhere under `~/lean`; run it against a copy.
"""

from __future__ import annotations

import argparse
import ast
import sys
import warnings
from pathlib import Path

import yaml

_KINDS = ("notation", "general", "split", "context", "definition")

READINGS_RELPATH = Path("ledger") / "readings.yaml"


def readings_path(cfg) -> Path:
    return cfg.root / READINGS_RELPATH


def load_readings(cfg) -> dict:
    """`<root>/ledger/readings.yaml`, normalized to always have all three keys.

    Missing file -> the empty structure, not an error: a brand-new repo, or
    one with nothing yet to waive, has no readings file at all.
    """
    path = readings_path(cfg)
    if not path.exists():
        return {"clauses": {}, "constants": {}, "exponents": {}}
    data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected a mapping at the top level")
    data = dict(data)
    data.setdefault("clauses", {})
    data.setdefault("constants", {})
    data.setdefault("exponents", {})
    if not isinstance(data["clauses"], dict):
        raise ValueError(f"{path}: 'clauses' must be a mapping of node id -> string")
    if not isinstance(data["constants"], dict):
        raise ValueError(f"{path}: 'constants' must be a mapping of node id -> string")
    if not isinstance(data["exponents"], dict):
        raise ValueError(f"{path}: 'exponents' must be a mapping of node id -> list")
    return data


# --------------------------------------------------------------------------
# Migration: recover the old inline dicts by parsing, never executing.
# --------------------------------------------------------------------------

def _literal_dict(py_path: Path, var_name: str) -> dict:
    """`ast.literal_eval` the value assigned to `var_name` in `py_path`.

    Handles both `NAME = {...}` and the annotated `NAME: T = {...}` form the
    incumbents use. Returns `{}` if the file does not exist, does not parse,
    or never assigns that name — a missing checker or a missing waiver table
    is normal, not an error.

    Several incumbents write non-raw string literals containing `\\Z`, `\\R`
    or `\\s` (meant as literal backslash-letter, not an escape); Python's
    parser only warns about this (`SyntaxWarning`), it does not refuse to
    parse, so the warning is suppressed here rather than left to spam every
    migration run for a pre-existing typo this tool is not the place to fix.
    """
    if not py_path.exists():
        return {}
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", SyntaxWarning)
            tree = ast.parse(py_path.read_text(encoding="utf-8"), filename=str(py_path))
    except SyntaxError:
        return {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        else:
            continue
        for t in targets:
            if isinstance(t, ast.Name) and t.id == var_name:
                try:
                    value = ast.literal_eval(node.value)
                except (ValueError, TypeError):
                    continue
                if isinstance(value, dict):
                    return value
    return {}


def _kind_of(reason: str) -> str:
    head = reason.split(":", 1)[0].strip().lower()
    return head if head in _KINDS else "context"


def extract_repo(repo: Path) -> dict:
    """The `readings.yaml`-shaped dict recovered from `<repo>/tools/`."""
    tools = repo / "tools"

    clauses = _literal_dict(tools / "check_clauses.py", "REVIEWED")
    # Every value must be a string; a malformed entry is dropped rather than
    # raising, since a partial migration you can inspect beats a crashed one.
    clauses = {k: v for k, v in clauses.items() if isinstance(v, str)}

    constants_raw = _literal_dict(tools / "check_constants.py", "REVIEWED")
    constants: dict = {}
    for node_id, entries in constants_raw.items():
        if not isinstance(entries, dict) or not entries:
            continue
        constants[node_id] = "; ".join(
            f"{name}: {reason}" for name, reason in sorted(entries.items())
        )

    exponents_raw = _literal_dict(tools / "check_exponents.py", "EXPECTED_ABSENT")
    exponents: dict = {}
    for node_id, entries in exponents_raw.items():
        if not isinstance(entries, dict) or not entries:
            continue
        rows = []
        for exponent, reason in sorted(entries.items()):
            rows.append({
                "kind": _kind_of(reason),
                "detail": f"{exponent}: {reason}",
            })
        exponents[node_id] = rows

    # Which bare symbols the paper uses decoratively rather than as real
    # exponents is per-paper vocabulary, and the incumbents kept it as a
    # module-level NOISE set. ORRW's is {d, c, M, R, …}; without carrying it
    # over, four of its nodes read as having unmatched exponents.
    noise = sorted(_literal_set(tools / "check_exponents.py", "NOISE"))

    out = {"clauses": clauses, "constants": constants, "exponents": exponents}
    if noise:
        out["noise"] = noise
    return out


def _literal_set(path: Path, name: str) -> set:
    """A module-level set literal, read by AST. Never imports or execs."""
    if not path.exists():
        return set()
    try:
        # Same non-raw-string caveat as _literal_dict: several incumbents
        # write "\Z" meaning a literal backslash-Z. Python warns; suppress it
        # rather than spam every migration run with a pre-existing typo.
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", SyntaxWarning)
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    except SyntaxError:
        return set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and any(
            getattr(t, "id", None) == name for t in node.targets
        ):
            try:
                value = ast.literal_eval(node.value)
            except (ValueError, SyntaxError):
                return set()
            if isinstance(value, (set, frozenset, list, tuple)):
                return {v for v in value if isinstance(v, str)}
    return set()


def drop_foreign_keys(data: dict, node_ids: set[str]) -> tuple[dict, dict[str, int]]:
    """Remove any per-node entry whose key is not a node of THIS repo.

    Dynamic-Dimensional-Reduction and Exploding-Sandpiles carry a `REVIEWED`
    dict that was never updated when the checker was copied out of rotor-23:
    all 26 keys are rotor-23 node ids and none is their own. Migrating that
    verbatim would replace a checker that inspected nothing with one that
    inspects 26 readings describing a different paper — a vacuous pass
    upgraded into a confidently wrong one. So the migration refuses, loudly,
    and those repos' readings get written from scratch instead.
    """
    refused: dict[str, int] = {}
    cleaned = dict(data)
    for section in ("clauses", "constants", "exponents"):
        entries = data.get(section) or {}
        keep = {k: v for k, v in entries.items() if k in node_ids}
        n = len(entries) - len(keep)
        if n:
            refused[section] = n
        cleaned[section] = keep
    return cleaned, refused


def _counts(data: dict) -> str:
    n_clauses = len(data["clauses"])
    n_constants = len(data["constants"])
    n_exp_nodes = len(data["exponents"])
    n_exp_entries = sum(len(v) for v in data["exponents"].values())
    return (f"{n_clauses} clause reading(s), {n_constants} constant waiver(s), "
            f"{n_exp_entries} exponent waiver(s) across {n_exp_nodes} node(s)")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        prog="python3 -m leanform_tools.readings",
        description="Recover ledger/readings.yaml from an incumbent tools/ directory.",
    )
    parser.add_argument("--extract", metavar="REPO_PATH", required=True,
                         help="a repo (or a copy of one) with a tools/ directory to read")
    parser.add_argument("--out", metavar="DIR", default=None,
                         help="write DIR/ledger/readings.yaml instead of REPO_PATH/ledger/readings.yaml")
    parser.add_argument("--dry-run", action="store_true",
                         help="report counts without writing anything")
    args = parser.parse_args(argv[1:])

    repo = Path(args.extract).resolve()
    data = extract_repo(repo)

    # Fail closed against a migration that would import another repo's
    # readings. See drop_foreign_keys.
    try:
        from .config import load as _load
        node_ids = {n.id for n in _load(repo).nodes}
    except Exception:
        node_ids = None
    if node_ids:
        data, refused = drop_foreign_keys(data, node_ids)
        if refused:
            total = sum(refused.values())
            print(f"REFUSED {total} entr(ies) whose keys are not nodes of this "
                  f"repo's manifest: {refused}")
            print("  These came from another repo's checker copy. They are NOT "
                  "written. Those nodes need readings authored against THIS paper.")

    print(f"{repo}: {_counts(data)}")

    if args.dry_run:
        return 0

    out_root = Path(args.out).resolve() if args.out else repo
    out_path = out_root / READINGS_RELPATH
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        yaml.safe_dump(data, sort_keys=True, allow_unicode=True, width=100),
        encoding="utf-8",
    )
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
