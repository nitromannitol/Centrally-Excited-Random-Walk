"""Tests for the three paper-side checkers: check_coverage, paper_anchors,
paper_citations.

These three replace per-repo copies whose embedded literals (a paper name, a
label-syntax assumption, a `\\proposition` spelling) made them pass vacuously
or blindly on at least one real repo -- see the module docstrings for the
specific incidents. Every synthetic repo here is built from scratch in
`tempfile.mkdtemp()`; nothing depends on `~/lean`.
"""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from leanform_tools import check_coverage, paper_anchors, paper_citations
from leanform_tools.config import load
from leanform_tools.gate import Result, run


def make_repo(manifest_text: str, paper_text: str, lean_files=None) -> Path:
    """A throwaway repo: `ledger/manifest.yaml` + `paper/foo.tex` + extras."""
    root = Path(tempfile.mkdtemp(prefix="leanform-paper-side-"))
    (root / "ledger").mkdir(parents=True)
    (root / "ledger" / "manifest.yaml").write_text(manifest_text, encoding="utf-8")
    (root / "paper").mkdir(parents=True)
    (root / "paper" / "foo.tex").write_text(paper_text, encoding="utf-8")
    for rel, content in (lean_files or {}).items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    return root


MANIFEST_HEADER = "version: 1\nsource_pin:\n  file: paper/foo.tex\n\nnodes:\n"


class TestVacuousCaseExitsTwo(unittest.TestCase):
    """The whole point of the package: a checker that inspects nothing must
    not exit 0, no matter which of the three checkers it is."""

    def test_check_coverage_with_no_statements_and_no_nodes(self):
        manifest = "version: 1\nsource_pin:\n  file: paper/foo.tex\n\nnodes: []\n"
        root = make_repo(manifest, "just a preamble, no statements\n")
        cfg = load(root)
        rc = run("check_coverage", check_coverage.check, cfg)
        self.assertEqual(rc, 2)

    def test_paper_anchors_with_no_nodes(self):
        manifest = "version: 1\nsource_pin:\n  file: paper/foo.tex\n\nnodes: []\n"
        root = make_repo(manifest, "just a preamble\n")
        cfg = load(root)
        rc = run("paper_anchors", paper_anchors.check, cfg)
        self.assertEqual(rc, 2)

    def test_paper_citations_with_no_citations_anywhere(self):
        manifest = MANIFEST_HEADER + (
            "  - id: n1\n"
            "    source: unknown\n"
            "    file: Foo/Plain.lean\n"
            "    export: Foo.plain\n"
            "    state: SEALED\n"
        )
        root = make_repo(manifest, "just a preamble\n",
                          lean_files={"Foo/Plain.lean": "theorem plain : True := trivial\n"})
        cfg = load(root)
        rc = run("paper_citations", paper_citations.check, cfg)
        self.assertEqual(rc, 2)


class TestCheckCoverage(unittest.TestCase):
    PAPER = (
        "\\begin{theorem}\\label{thm:claimed}\n"
        "  This one is claimed by a node.\n"
        "\\end{theorem}\n"
        "\n"
        "\\begin{lemma}\\label{lem:orphan}\n"
        "  This one is never claimed by any node.\n"
        "\\end{lemma}\n"
        "\n"
        "\\begin{proposition}\n"
        "  This one has no \\label at all.\n"
        "\\end{proposition}\n"
    )

    def setUp(self):
        manifest = MANIFEST_HEADER + (
            "  - id: thm-claimed\n"
            "    source: foo.tex:1-3 (label thm:claimed)\n"
            "    file: Foo/Frozen/Main.lean\n"
            "    export: Foo.Frozen.main\n"
            "    state: SEALED\n"
        )
        self.root = make_repo(manifest, self.PAPER)
        self.cfg = load(self.root)

    def test_total_counts_every_statement_labeled_or_not(self):
        res = Result(name="check_coverage")
        check_coverage.check(res, self.cfg)
        self.assertEqual(res.total, 3)
        self.assertEqual(res.processed, 3)

    def test_unclaimed_labelled_statement_is_reported(self):
        res = Result(name="check_coverage")
        check_coverage.check(res, self.cfg)
        joined = "\n".join(res.failures)
        self.assertIn("lem:orphan", joined)
        self.assertIn("not claimed", joined)

    def test_unlabeled_environment_is_reported_distinctly(self):
        res = Result(name="check_coverage")
        check_coverage.check(res, self.cfg)
        joined = "\n".join(res.failures)
        self.assertIn("UNLABELED proposition", joined)
        # The two kinds of problem are distinguishable in the failure text,
        # not merged into one generic "uncovered" message.
        self.assertNotIn("UNLABELED proposition environment -- fix the paper, "
                          "not the checker\n  not claimed", joined)

    def test_claimed_statement_is_not_flagged(self):
        res = Result(name="check_coverage")
        check_coverage.check(res, self.cfg)
        joined = "\n".join(res.failures)
        self.assertNotIn("thm:claimed", joined)

    def test_exit_code_is_one_not_two(self):
        rc = run("check_coverage", check_coverage.check, self.cfg)
        self.assertEqual(rc, 1)


class TestPaperAnchors(unittest.TestCase):
    # The environment spans lines 2-5 inclusive (1-indexed).
    PAPER = (
        "% preamble\n"
        "\\begin{theorem}\\label{thm:main}\n"
        "  First line of the statement.\n"
        "  Second line of the statement.\n"
        "\\end{theorem}\n"
    )

    def _manifest(self, a: int, b: int) -> str:
        return MANIFEST_HEADER + (
            "  - id: thm-main\n"
            f"    source: foo.tex:{a}-{b} (label thm:main)\n"
            "    file: Foo/Frozen/Main.lean\n"
            "    export: Foo.Frozen.main\n"
            "    state: SEALED\n"
        )

    def test_stale_range_is_detected(self):
        root = make_repo(self._manifest(2, 4), self.PAPER)  # actual is 2-5
        cfg = load(root)
        res = Result(name="paper_anchors")
        paper_anchors.check(res, cfg)
        joined = "\n".join(res.failures)
        self.assertIn("stale anchor", joined)
        self.assertIn("foo.tex:2-4", joined)
        self.assertIn("foo.tex:2-5", joined)
        self.assertEqual(run("paper_anchors", paper_anchors.check, cfg), 1)

    def test_correct_range_is_not_flagged(self):
        root = make_repo(self._manifest(2, 5), self.PAPER)  # already correct
        cfg = load(root)
        res = Result(name="paper_anchors")
        paper_anchors.check(res, cfg)
        self.assertEqual(res.failures, [])
        self.assertEqual(run("paper_anchors", paper_anchors.check, cfg), 0)

    def test_fix_repairs_the_manifest_range_and_only_the_range(self):
        root = make_repo(self._manifest(2, 4), self.PAPER)
        cfg = load(root)
        res = Result(name="paper_anchors")
        paper_anchors.check(res, cfg, fix=True)

        rewritten = (root / "ledger" / "manifest.yaml").read_text(encoding="utf-8")
        self.assertIn("source: foo.tex:2-5 (label thm:main)", rewritten)
        self.assertNotIn("foo.tex:2-4", rewritten)
        # Everything else in the manifest is untouched.
        self.assertIn("export: Foo.Frozen.main", rewritten)

        # Re-loading and re-checking now finds nothing wrong.
        cfg2 = load(root)
        res2 = Result(name="paper_anchors")
        paper_anchors.check(res2, cfg2)
        self.assertEqual(res2.failures, [])


class TestPaperCitations(unittest.TestCase):
    # The environment spans lines 2-5 inclusive (1-indexed).
    PAPER = (
        "% preamble\n"
        "\\begin{theorem}\\label{thm:main}\n"
        "  First line of the statement.\n"
        "  Second line of the statement.\n"
        "\\end{theorem}\n"
    )

    CORRECT_LEAN = (
        "/-\n"
        "Some theorem, frozen. `foo.tex:2-5` (label `thm:main`):\n"
        "  statement text.\n"
        "-/\n"
        "theorem correct_one : True := trivial\n"
    )

    STALE_LEAN = (
        "/-\n"
        "Some theorem, frozen. `foo.tex:2-4` (label `thm:main`):\n"
        "  statement text.\n"
        "-/\n"
        "theorem stale_one : True := trivial\n"
    )

    def setUp(self):
        manifest = (
            "version: 1\nsource_pin:\n  file: paper/foo.tex\nlibrary: Foo\n\n"
            "nodes:\n  - id: thm-main\n    source: unknown\n"
        )
        self.root = make_repo(
            manifest, self.PAPER,
            lean_files={
                "Foo/Frozen/Correct.lean": self.CORRECT_LEAN,
                "Foo/Frozen/Stale.lean": self.STALE_LEAN,
            },
        )
        self.cfg = load(self.root)

    def test_correct_and_stale_are_distinguished(self):
        res = Result(name="paper_citations")
        paper_citations.check(res, self.cfg)
        joined = "\n".join(res.failures)
        self.assertIn("foo.tex:2-4 -> foo.tex:2-5", joined)
        self.assertEqual(run("paper_citations", paper_citations.check, self.cfg), 1)

    def test_fix_repairs_only_the_stale_file(self):
        res = Result(name="paper_citations")
        paper_citations.check(res, self.cfg, fix=True)

        correct_text = (self.root / "Foo/Frozen/Correct.lean").read_text(encoding="utf-8")
        stale_text = (self.root / "Foo/Frozen/Stale.lean").read_text(encoding="utf-8")
        self.assertIn("foo.tex:2-5", correct_text)
        self.assertIn("foo.tex:2-5", stale_text)
        self.assertNotIn("foo.tex:2-4", stale_text)

        cfg2 = load(self.root)
        res2 = Result(name="paper_citations")
        paper_citations.check(res2, cfg2)
        self.assertEqual(res2.failures, [])


if __name__ == "__main__":
    unittest.main()
