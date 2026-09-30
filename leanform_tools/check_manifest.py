"""The statement-integrity gate. Pure Python: no Lake, no network.

Eight checks, carried over from the vendored `check_manifest.py` that was
copied across at least ten repos, with the per-repo literals removed and the
meta-check wired in.

What this gate does NOT do: it counts `sorry` tokens, which is not enough,
because a file can contain no `sorry` and still depend on one transitively
through an import. `Exploding.Frozen.insertion_inequality` was exactly that.
The axiom closure is the authority; see `check_axioms.py`. This is the fast
prefilter.
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path

from . import lean_source as ls
from .config import BANNED_TOKENS, DRAFT_STATES, STATES, RepoConfig, load
from .gate import Result, run


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def check(res: Result, cfg: RepoConfig) -> None:
    res.total = len(cfg.nodes)
    owners: dict[Path, list[str]] = {}

    # 8. The paper pin. Checked once, before the nodes, because every node's
    #    `source:` line range is meaningless if the paper moved underneath it.
    if cfg.paper_sha256:
        if not cfg.paper_path.exists():
            res.fail(f"source_pin.file {cfg.paper_rel} does not exist")
        else:
            got = _sha(cfg.paper_path.read_text(encoding="utf-8"))
            if got != cfg.paper_sha256:
                res.fail(
                    f"paper hash drift: {cfg.paper_rel}\n"
                    f"        manifest={cfg.paper_sha256[:16]}  "
                    f"actual={got[:16]}  — every node's line range is now suspect"
                )
    else:
        res.note("source_pin.sha256 absent: the paper is not pinned")

    for node in cfg.nodes:
        nid = node.id

        # 7. State and kind legality.
        if node.state not in STATES:
            res.fail(f"{nid}: state {node.state!r} is not one of {sorted(STATES)}")
        if node.kind not in (None, "theorem", "definition"):
            res.fail(f"{nid}: kind {node.kind!r} is not theorem or definition")
        if node.kind == "definition" and node.state in DRAFT_STATES:
            res.fail(
                f"{nid}: an External/definition node is {node.state}; "
                "a carried hypothesis has nothing to prove"
            )

        if not node.file:
            res.fail(f"{nid}: no file:")
            continue
        path = cfg.root / node.file
        if not path.exists():
            res.fail(f"{nid}: file {node.file} does not exist")
            continue

        owners.setdefault(path, []).append(nid)
        src = path.read_text(encoding="utf-8")

        # 1. Exactly one block.
        spans = ls.frozen_blocks(src)
        if len(spans) != 1:
            res.fail(f"{nid}: {len(spans)} frozen blocks in {node.file}, want exactly 1")
            continue
        span = spans[0]
        if span[1] < 0:
            res.fail(f"{nid}: unterminated frozen block in {node.file}")
            continue

        res.count()
        body = ls.block_body(src, span)

        # 2. The hash.
        want = node.frozen_sha256
        got = _sha(body)
        if not want:
            res.fail(f"{nid}: no frozen_sha256 recorded (computed {got[:16]})")
        elif want != got:
            res.fail(
                f"{nid}: STATEMENT DRIFT in {node.file}\n"
                f"        manifest={want[:16]}  actual={got[:16]}"
            )

        # 3. The declarations in the block match the manifest, in order.
        found = ls.declarations(body)
        recorded = node.decls
        if not recorded:
            res.fail(f"{nid}: manifest records no export/decls")
        else:
            # `export:` is fully qualified; `decls:` may be unqualified.
            def tail(name: str) -> str:
                return name.rsplit(".", 1)[-1]

            if len(found) != len(recorded):
                res.fail(
                    f"{nid}: block holds {len(found)} declaration(s) "
                    f"{found}, manifest records {len(recorded)} {recorded}"
                )
            else:
                for r, f in zip(recorded, found):
                    # Compare on the final component: `export:` is fully
                    # qualified, `decls:` may be unqualified, and the Lean
                    # source may write either.
                    if tail(r) == tail(f):
                        continue
                    if ls.is_truncation(tail(r), tail(f)):
                        res.fail(
                            f"{nid}: manifest name {r!r} is a truncation of the "
                            f"declaration {f!r} — these are different identifiers"
                        )
                    else:
                        res.fail(
                            f"{nid}: manifest records {r!r}, block declares {f!r}"
                        )
        if node.is_multi_decl:
            res.note(
                f"{nid}: {len(recorded)} declarations in one block "
                "(tolerated pending the semantic fingerprint; see PLAN.md)"
            )

        # 5. `sorry` only as a registered draft body, once, after the marker.
        masked = ls.mask_comments(src)
        sorries = [
            ls.line_of(masked, i)
            for i in range(len(masked))
            if masked.startswith("sorry", i)
            and not (i and (masked[i - 1].isalnum() or masked[i - 1] == "_"))
            and not (
                i + 5 < len(masked)
                and (masked[i + 5].isalnum() or masked[i + 5] == "_")
            )
        ]
        end_line = ls.line_of(src, span[1])
        if node.state == "DRAFT_SORRY":
            # The authorized placeholder: a `sorry` below the END marker, so
            # it cannot be part of the statement.
            #
            # A single-declaration node wants exactly one. A multi-declaration
            # block wants at least one and no more than one per declaration:
            # the definitions it seals alongside the theorem have nothing to
            # prove, so the count is between 1 and len(decls) and cannot be
            # pinned more tightly without parsing each declaration's kind.
            ndecl = max(1, len(node.decls))
            if node.is_multi_decl:
                if not 1 <= len(sorries) <= ndecl:
                    res.fail(
                        f"{nid}: state DRAFT_SORRY with {ndecl} declarations "
                        f"wants between 1 and {ndecl} sorry, found "
                        f"{len(sorries)} at lines {sorries}"
                    )
            elif len(sorries) != 1:
                res.fail(
                    f"{nid}: state DRAFT_SORRY wants exactly one sorry, "
                    f"found {len(sorries)} at lines {sorries}"
                )
            for line in sorries:
                if line <= end_line:
                    res.fail(
                        f"{nid}: the sorry at line {line} is not after the END "
                        f"marker (line {end_line}) — it is inside the statement"
                    )
        elif node.state == "CONDITIONAL":
            # CONDITIONAL means the proof is written and complete; the
            # sorryAx enters through a DRAFT_SORRY predecessor, not from here.
            # So a CONDITIONAL node has no `sorry` of its own.
            if sorries:
                res.fail(
                    f"{nid}: state CONDITIONAL but {len(sorries)} own sorry at "
                    f"lines {sorries}; a CONDITIONAL proof is complete and "
                    "inherits sorryAx through a predecessor"
                )
        elif sorries:
            res.fail(
                f"{nid}: state {node.state} but {len(sorries)} sorry at "
                f"lines {sorries}; register the seal or fix the state"
            )

    # 4. Every frozen file owned by exactly one node.
    for path, ids in sorted(owners.items()):
        if len(ids) > 1:
            res.fail(f"{path.name} is owned by {len(ids)} nodes: {ids}")
    for d in cfg.frozen_dirs:
        if not d.exists():
            continue
        for p in sorted(d.rglob("*.lean")):
            if p not in owners:
                res.fail(
                    f"{p.relative_to(cfg.root)} is under a frozen directory "
                    "but no manifest node owns it"
                )

    # 6. Banned tokens anywhere in the production tree. `axiom` is scanned as
    #    a declaration head only, so `#print axioms` stays legal.
    for p in cfg.production_lean_files():
        src = p.read_text(encoding="utf-8")
        rel = p.relative_to(cfg.root)
        for tok, line in ls.token_hits(src, BANNED_TOKENS):
            res.fail(f"{rel}:{line}: banned token {tok!r}")
        for line in ls.axiom_declarations(src):
            res.fail(f"{rel}:{line}: `axiom` declaration; cited results are "
                     "carried as explicit hypotheses, never as axioms")


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else "."
    cfg = load(root)
    return run("check_manifest", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
