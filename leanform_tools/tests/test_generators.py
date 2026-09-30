"""Tests for the three document generators: sync_docs, assumptions, linkcheck.

Every repo here is synthetic, built fresh in `tempfile.mkdtemp()`; nothing
depends on `~/lean`.
"""

from __future__ import annotations

import shutil
import tempfile
import unittest
from pathlib import Path

import yaml

from .. import assumptions, linkcheck, sync_docs
from ..config import BEGIN, END, load


# ---- repo-building helpers -------------------------------------------------


def _node(
    id: str,
    state: str,
    export: str | None = None,
    decls=None,
    file: str | None = None,
    source: str = "demo.tex:1-2 (label demo)",
    kind: str = "theorem",
    frozen_sha256: str | None = None,
) -> dict:
    d = {"id": id, "state": state, "kind": kind, "source": source}
    if export:
        d["export"] = export
    if decls:
        d["decls"] = decls
    if file:
        d["file"] = file
    if frozen_sha256:
        d["frozen_sha256"] = frozen_sha256
    return d


def make_repo(nodes, library: str = "Demo", paper_rel: str = "paper/demo.tex") -> Path:
    root = Path(tempfile.mkdtemp(prefix="leanform-test-"))
    (root / "ledger").mkdir(parents=True)
    manifest = {
        "source_pin": {"file": paper_rel},
        "library": library,
        "nodes": nodes,
    }
    (root / "ledger" / "manifest.yaml").write_text(
        yaml.safe_dump(manifest, sort_keys=False), encoding="utf-8"
    )
    return root


def write_markdown_shells(root: Path) -> None:
    (root / "README.md").write_text(
        "# Demo\n\nSome prose.\n\n"
        + sync_docs.STATUS_BEGIN
        + "\n\nplaceholder\n\n"
        + sync_docs.STATUS_END
        + "\n\nMore prose.\n",
        encoding="utf-8",
    )
    (root / "CORRESPONDENCE.md").write_text(
        "# Correspondence\n\n"
        + sync_docs.SURFACE_BEGIN
        + "\n\nplaceholder\n\n"
        + sync_docs.SURFACE_END
        + "\n",
        encoding="utf-8",
    )


def write_frozen_lean_file(root: Path, rel: str, decl: str, body: str) -> None:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    text = (
        "/- a frozen node, for the test -/\n"
        "import Init\n\n"
        f"{BEGIN}\n"
        f"theorem {decl} : {body} := by sorry\n"
        f"{END}\n"
    )
    path.write_text(text, encoding="utf-8")


class _TempRepoTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._roots: list[Path] = []

    def tearDown(self) -> None:
        for r in self._roots:
            shutil.rmtree(r, ignore_errors=True)

    def track(self, root: Path) -> Path:
        self._roots.append(root)
        return root


# ---- sync_docs: the Exploding-Sandpiles bug -------------------------------


class ExplodingSandpilesCase(_TempRepoTestCase):
    """4 SEALED + 2 CONDITIONAL + 2 FROZEN + 16 DRAFT_SORRY must not read '8 sealed'.

    The incumbent `status_block` computed sealed as `len(nodes) - len(draft)`
    (24 - 16 = 8), folding CONDITIONAL and FROZEN into "sealed". The true
    count is 4.
    """

    def test_exact_counts_not_8_sealed(self) -> None:
        nodes = []
        for i in range(1, 5):
            nodes.append(_node(f"sealed-{i}", "SEALED", export=f"Exploding.Frozen.sealed_{i}"))
        for i in range(1, 3):
            nodes.append(_node(f"cond-{i}", "CONDITIONAL", export=f"Exploding.Frozen.cond_{i}"))
        for i in range(1, 3):
            nodes.append(
                _node(f"ext-{i}", "FROZEN", export=f"Exploding.External.ext_{i}", kind="definition")
            )
        for i in range(1, 17):
            nodes.append(_node(f"draft-{i}", "DRAFT_SORRY", export=f"Exploding.Frozen.draft_{i}"))
        self.assertEqual(len(nodes), 24)

        root = self.track(make_repo(nodes, library="Exploding"))
        cfg = load(root)
        text = sync_docs.status_block(cfg)

        self.assertNotIn("8 sealed", text)
        self.assertNotIn("8 `SEALED`", text)
        self.assertIn("4 sealed, 2 conditional, 2 assumed, 16 draft", text)
        self.assertIn("24 registered statements", text)


# ---- sync_docs: hand-edited number inside a generated block --------------


class HandEditedNumberCase(_TempRepoTestCase):
    def test_hand_edit_inside_generated_block_is_detected(self) -> None:
        nodes = [
            _node("thm-1", "SEALED", export="Demo.Frozen.thm_1"),
            _node("thm-2", "DRAFT_SORRY", export="Demo.Frozen.thm_2"),
        ]
        root = self.track(make_repo(nodes))
        write_markdown_shells(root)

        rc = sync_docs.main(["sync_docs", str(root), "--write"])
        self.assertEqual(rc, 0)

        readme = root / "README.md"
        text = readme.read_text(encoding="utf-8")
        self.assertIn("1 sealed, 1 draft", text)

        # Hand-edit a digit inside the generated STATUS block only.
        i = text.find(sync_docs.STATUS_BEGIN)
        j = text.find(sync_docs.STATUS_END, i)
        block = text[i:j]
        edited_block = block.replace("1 sealed", "2 sealed", 1)
        self.assertNotEqual(block, edited_block)
        readme.write_text(text[:i] + edited_block + text[j:], encoding="utf-8")

        rc = sync_docs.main(["sync_docs", str(root)])
        self.assertNotEqual(rc, 0)


# ---- sync_docs: --write then bare check round-trips clean -----------------


class WriteThenCheckRoundTripCase(_TempRepoTestCase):
    def test_round_trip(self) -> None:
        nodes = [
            _node("thm-1", "SEALED", export="Demo.Frozen.thm_1"),
            _node("ext-1", "FROZEN", export="Demo.External.ext_1", kind="definition"),
        ]
        root = self.track(make_repo(nodes))
        write_markdown_shells(root)

        rc_write = sync_docs.main(["sync_docs", str(root), "--write"])
        self.assertEqual(rc_write, 0)

        rc_check = sync_docs.main(["sync_docs", str(root)])
        self.assertEqual(rc_check, 0)

    def test_missing_marker_in_required_file_fails(self) -> None:
        nodes = [_node("thm-1", "SEALED", export="Demo.Frozen.thm_1")]
        root = self.track(make_repo(nodes))
        # README.md/CORRESPONDENCE.md exist but carry no markers at all.
        (root / "README.md").write_text("# Demo\n\nno markers here.\n", encoding="utf-8")
        (root / "CORRESPONDENCE.md").write_text("# Correspondence\n", encoding="utf-8")

        rc = sync_docs.main(["sync_docs", str(root)])
        self.assertNotEqual(rc, 0)


# ---- sync_docs: PROOF.md and formalization.yaml (new-gate 7) --------------


class ProofMdAndFormalizationYamlCase(_TempRepoTestCase):
    def test_proof_md_without_markers_fails(self) -> None:
        nodes = [_node("thm-1", "SEALED", export="Demo.Frozen.thm_1")]
        root = self.track(make_repo(nodes))
        write_markdown_shells(root)
        (root / "PROOF.md").write_text(
            "# The proof\n\n37 of the statements are `SEALED`.\n", encoding="utf-8"
        )

        rc = sync_docs.main(["sync_docs", str(root)])
        self.assertNotEqual(rc, 0)

    def test_formalization_yaml_stale_row_reported(self) -> None:
        nodes = [_node("thm-main", "PROVED", export="Demo.Frozen.main")]
        root = self.track(make_repo(nodes))
        write_markdown_shells(root)
        (root / "formalization.yaml").write_text(
            "version: \"v0.1\"\n"
            "alignment:\n"
            "  namespace: \"Demo\"\n"
            "  statements:\n"
            "    - source: \"Theorem 1\"\n"
            "      lean: \"Demo.Frozen.main\"\n"
            "      module: \"Demo.Frozen.Main\"\n"
            "      status: \"sealed\"\n"
            "      note: \"stale row\"\n",
            encoding="utf-8",
        )

        rc = sync_docs.main(["sync_docs", str(root)])
        self.assertNotEqual(rc, 0)

    def test_formalization_yaml_write_fixes_stale_row(self) -> None:
        nodes = [_node("thm-main", "PROVED", export="Demo.Frozen.main")]
        root = self.track(make_repo(nodes))
        write_markdown_shells(root)
        (root / "formalization.yaml").write_text(
            "version: \"v0.1\"\n"
            "alignment:\n"
            "  namespace: \"Demo\"\n"
            "  statements:\n"
            "    - source: \"Theorem 1\"\n"
            "      lean: \"Demo.Frozen.main\"\n"
            "      module: \"Demo.Frozen.Main\"\n"
            "      status: \"sealed\"\n"
            "      note: \"stale row\"\n",
            encoding="utf-8",
        )

        rc_write = sync_docs.main(["sync_docs", str(root), "--write"])
        self.assertEqual(rc_write, 0)
        self.assertIn('status: "proved"', (root / "formalization.yaml").read_text(encoding="utf-8"))

        rc_check = sync_docs.main(["sync_docs", str(root)])
        self.assertEqual(rc_check, 0)


# ---- assumptions -----------------------------------------------------------


class AssumptionsZeroFrozenCase(_TempRepoTestCase):
    def test_zero_frozen_is_nothing_and_exit_0(self) -> None:
        nodes = [
            _node("thm-1", "SEALED", export="Demo.Frozen.thm_1"),
            _node("thm-2", "PROVED", export="Demo.Frozen.thm_2"),
        ]
        root = self.track(make_repo(nodes))

        rc = assumptions.main(["assumptions", str(root)])
        self.assertEqual(rc, 0)
        text = (root / "ASSUMPTIONS.md").read_text(encoding="utf-8")
        self.assertIn("Nothing.", text)

        rc_check = assumptions.main(["assumptions", str(root), "--check"])
        self.assertEqual(rc_check, 0)

    def test_hand_edited_vacuous_file_is_a_real_failure(self) -> None:
        nodes = [_node("thm-1", "SEALED", export="Demo.Frozen.thm_1")]
        root = self.track(make_repo(nodes))
        assumptions.main(["assumptions", str(root)])
        (root / "ASSUMPTIONS.md").write_text(
            "# What this development assumes\n\nSomething, actually.\n", encoding="utf-8"
        )
        rc = assumptions.main(["assumptions", str(root), "--check"])
        self.assertNotEqual(rc, 0)


class AssumptionsVerbatimUnicodeCase(_TempRepoTestCase):
    def test_quotes_frozen_block_verbatim_including_unicode(self) -> None:
        body = "∀ x : ℝ, x ≤ x + 1"  # ∀ x : ℝ, x ≤ x + 1
        nodes = [
            _node(
                "ext-1",
                "FROZEN",
                export="Demo.External.ext_kingman",
                file="Demo/External/Kingman.lean",
                source="demo.tex:10-12 (label ext:kingman)",
                kind="definition",
            )
        ]
        root = self.track(make_repo(nodes))
        write_frozen_lean_file(root, "Demo/External/Kingman.lean", "Demo.External.ext_kingman", body)

        rc = assumptions.main(["assumptions", str(root)])
        self.assertEqual(rc, 0)
        text = (root / "ASSUMPTIONS.md").read_text(encoding="utf-8")
        self.assertIn(body, text)
        self.assertIn("ext-1", text)
        self.assertIn("Not proved here", text)

    def test_discharged_companion_is_marked(self) -> None:
        body = "True"
        nodes = [
            _node(
                "ext-1",
                "FROZEN",
                export="Demo.External.ext_1",
                file="Demo/External/Ext1.lean",
                kind="definition",
            ),
            _node(
                "ext-1-proved",
                "SEALED",
                export="Demo.External.ext_1_proved",
                file="Demo/External/Ext1Proved.lean",
            ),
        ]
        root = self.track(make_repo(nodes))
        write_frozen_lean_file(root, "Demo/External/Ext1.lean", "Demo.External.ext_1", body)
        write_frozen_lean_file(
            root, "Demo/External/Ext1Proved.lean", "Demo.External.ext_1_proved", body
        )

        rc = assumptions.main(["assumptions", str(root)])
        self.assertEqual(rc, 0)
        text = (root / "ASSUMPTIONS.md").read_text(encoding="utf-8")
        self.assertIn("DISCHARGED", text)
        self.assertIn("ext-1-proved", text)


# ---- linkcheck --------------------------------------------------------------


class LinkcheckCase(_TempRepoTestCase):
    def test_finds_dangling_and_ignores_http(self) -> None:
        nodes = [_node("thm-1", "SEALED", export="Demo.Frozen.thm_1")]
        root = self.track(make_repo(nodes))
        (root / "CONTRIBUTING.md").write_text("exists", encoding="utf-8")
        (root / "README.md").write_text(
            "# Demo\n\n"
            "See [online docs](https://example.com/docs) and "
            "[contact](mailto:a@b.com) and [section](#top).\n\n"
            "See [`CONTRIBUTING.md`](CONTRIBUTING.md) which exists, and "
            "[`ledger/ERRATA.md`](ledger/ERRATA.md) which does not.\n",
            encoding="utf-8",
        )

        links = linkcheck.dangling_links(root / "README.md")
        targets = {t for _, t in links}
        self.assertEqual(targets, {"ledger/ERRATA.md"})

        rc = linkcheck.main(["linkcheck", str(root)])
        self.assertNotEqual(rc, 0)

    def test_ignores_link_syntax_inside_code_spans(self) -> None:
        nodes = [_node("thm-1", "SEALED", export="Demo.Frozen.thm_1")]
        root = self.track(make_repo(nodes))
        (root / "README.md").write_text(
            "# Demo\n\nWrite `K_sigma[w](x,y) = sigma` for the kernel.\n",
            encoding="utf-8",
        )
        links = linkcheck.dangling_links(root / "README.md")
        self.assertEqual(links, [])

    def test_all_links_resolve_exits_0(self) -> None:
        nodes = [_node("thm-1", "SEALED", export="Demo.Frozen.thm_1")]
        root = self.track(make_repo(nodes))
        (root / "NOTICE").write_text("notice", encoding="utf-8")
        (root / "README.md").write_text(
            "# Demo\n\nSee [NOTICE](NOTICE).\n", encoding="utf-8"
        )
        rc = linkcheck.main(["linkcheck", str(root)])
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
