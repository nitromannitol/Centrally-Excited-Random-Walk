"""Label citations must resolve and must never make an empty audit pass."""

import unittest

from leanform_tools import paper_citations
from leanform_tools.config import load
from leanform_tools.gate import Result, run
from leanform_tools.tests.test_paper_side import make_repo


class LabelCitations(unittest.TestCase):
    def make_config(self, lean="/- The result `lem:bound`. -/\n", label="lem:bound"):
        manifest = (
            "version: 1\nlibrary: Foo\ncitation_style: labels\n"
            "source_pin:\n  file: paper/foo.tex\nnodes:\n"
            "  - id: bound\n    file: Foo/Frozen/Bound.lean\n"
            f"    source: foo.tex:1-3 (label {label})\n"
            "    export: Foo.bound\n    state: SEALED\n"
        )
        paper = "\\begin{lemma}\\label{lem:bound}\nBound.\n\\end{lemma}\n"
        root = make_repo(manifest, paper, {"Foo/Frozen/Bound.lean": lean})
        return load(root)

    def test_resolves_label_without_lean_line_numbers(self):
        result = Result("paper_citations")
        paper_citations.check(result, self.make_config())
        self.assertEqual(result.processed, 1)
        self.assertEqual(result.failures, [])

    def test_missing_label_in_lean_fails(self):
        self.assertEqual(run("paper_citations", paper_citations.check,
                             self.make_config("/- A bound. -/\n")), 1)

    def test_unknown_label_in_paper_fails(self):
        self.assertEqual(run("paper_citations", paper_citations.check,
                             self.make_config(label="lem:missing")), 1)

    def test_line_number_citation_is_rejected(self):
        self.assertEqual(run("paper_citations", paper_citations.check,
                             self.make_config("/- `lem:bound`, foo.tex:1-3. -/\n")), 1)

    def test_empty_manifest_is_not_a_pass(self):
        cfg = self.make_config()
        cfg.nodes = []
        self.assertEqual(run("paper_citations", paper_citations.check, cfg), 2)


if __name__ == "__main__":
    unittest.main()
