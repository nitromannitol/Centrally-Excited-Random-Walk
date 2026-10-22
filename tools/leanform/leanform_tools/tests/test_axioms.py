"""Acceptance-boundary tests for the axiom gate, run without a toolchain.

The cases here are the ones a false success would hide: a draft that is
secretly clean, a seal that secretly depends on an open proof, an export the
probe never covered, and an added axiom.
"""

import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from leanform_tools.check_axioms import (
    ProbeError,
    audit_closures,
    check,
    parse_axiom_report,
)
from leanform_tools.gate import Result


class FakeNode:
    def __init__(self, nid, state, decls):
        self.id, self.state, self.decls = nid, state, decls


STD = "propext, Classical.choice, Quot.sound"


class TestParse(unittest.TestCase):
    def test_parses_a_standard_closure(self):
        out = parse_axiom_report(f"'Foo.bar' depends on axioms: [{STD}]")
        self.assertEqual(out["Foo.bar"],
                         {"propext", "Classical.choice", "Quot.sound"})

    def test_parses_no_axioms_at_all(self):
        out = parse_axiom_report("'Foo.bar' does not depend on any axioms")
        self.assertEqual(out["Foo.bar"], set())

    def test_joins_lines_lean_wrapped(self):
        out = parse_axiom_report(
            "'Foo.bar' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]"
        )
        self.assertEqual(out["Foo.bar"],
                         {"propext", "Classical.choice", "Quot.sound"})

    def test_duplicate_report_for_one_export_is_a_probe_error(self):
        with self.assertRaises(ProbeError):
            parse_axiom_report(
                f"'Foo.bar' depends on axioms: [{STD}]\n"
                f"'Foo.bar' depends on axioms: [propext]"
            )

    def test_duplicate_reports_including_no_axioms_are_probe_errors(self):
        reports = [
            f"'Foo.bar' depends on axioms: [{STD}]",
            "'Foo.bar' does not depend on any axioms",
        ]
        message = "Foo.bar: two axiom reports for one export; cannot attribute a verdict"
        for first in reports:
            for second in reports:
                with self.subTest(first=first, second=second):
                    with self.assertRaises(ProbeError) as caught:
                        parse_axiom_report(first + "\n" + second)
                    self.assertEqual(str(caught.exception), message)


class TestProbe(unittest.TestCase):
    def run_probe(self, root, returncode, stdout, stderr=""):
        node = SimpleNamespace(id="main", state="SEALED", decls=["Foo.bar"], file="Foo.lean")
        cfg = SimpleNamespace(root=Path(root), nodes=[node])
        result = Result("check_axioms")
        process = subprocess.CompletedProcess([], returncode, stdout, stderr)
        with patch("leanform_tools.check_axioms.subprocess.run", return_value=process):
            check(result, cfg)
        return result

    def test_nonzero_exit_rejects_complete_clean_reports(self):
        reports = [
            f"'Foo.bar' depends on axioms: [{STD}]",
            "'Foo.bar' does not depend on any axioms",
        ]
        for code in (1, 2, -9):
            for report in reports:
                with self.subTest(code=code, report=report):
                    with tempfile.TemporaryDirectory() as root:
                        with self.assertRaises(ProbeError) as caught:
                            self.run_probe(root, code, report + "\nerror: later failure",
                                           "stderr context")
                        message = str(caught.exception)
                        self.assertIn(f"code {code}", message)
                        self.assertIn(report, message)
                        self.assertIn("error: later failure", message)
                        self.assertIn("stderr context", message)
                        self.assertEqual(list((Path(root) / "scratch").iterdir()), [])

    def test_failure_context_keeps_only_output_tails(self):
        stdout = "stdout prefix" + "x" * 2100 + "stdout tail"
        stderr = "stderr prefix" + "y" * 2100 + "stderr tail"
        with tempfile.TemporaryDirectory() as root:
            with self.assertRaises(ProbeError) as caught:
                self.run_probe(root, 1, stdout, stderr)
        message = str(caught.exception)
        self.assertIn("stdout tail", message)
        self.assertIn("stderr tail", message)
        self.assertNotIn("stdout prefix", message)
        self.assertNotIn("stderr prefix", message)

    def test_successful_probe_accepts_standard_and_empty_closures(self):
        for report in (f"'Foo.bar' depends on axioms: [{STD}]",
                       "'Foo.bar' does not depend on any axioms"):
            with self.subTest(report=report):
                with tempfile.TemporaryDirectory() as root:
                    result = self.run_probe(root, 0, report)
                self.assertEqual(result.failures, [])
                self.assertEqual(result.processed, 1)


class TestAcceptance(unittest.TestCase):
    def test_sealed_with_standard_closure_passes(self):
        n = FakeNode("thm-main", "SEALED", ["L.Frozen.main"])
        fails, _ = audit_closures([n], {"L.Frozen.main": {"propext", "Quot.sound"}})
        self.assertEqual(fails, [])

    def test_sealed_with_sorry_ax_fails(self):
        """The insertion_inequality case: zero own sorrys, sorryAx in closure."""
        n = FakeNode("thm-x", "SEALED", ["L.Frozen.x"])
        fails, _ = audit_closures([n], {"L.Frozen.x": {"propext", "sorryAx"}})
        self.assertEqual(len(fails), 1)
        self.assertIn("transitively", fails[0])

    def test_draft_with_clean_closure_fails_register_the_seal(self):
        n = FakeNode("thm-y", "DRAFT_SORRY", ["L.Frozen.y"])
        fails, _ = audit_closures([n], {"L.Frozen.y": {"propext"}})
        self.assertEqual(len(fails), 1)
        self.assertIn("register its seal", fails[0])

    def test_draft_with_sorry_ax_is_accepted(self):
        n = FakeNode("thm-z", "DRAFT_SORRY", ["L.Frozen.z"])
        fails, _ = audit_closures([n], {"L.Frozen.z": {"propext", "sorryAx"}})
        self.assertEqual(fails, [])

    def test_conditional_with_sorry_ax_is_accepted(self):
        n = FakeNode("thm-c", "CONDITIONAL", ["L.Frozen.c"])
        fails, _ = audit_closures([n], {"L.Frozen.c": {"propext", "sorryAx"}})
        self.assertEqual(fails, [])

    def test_an_added_axiom_fails(self):
        n = FakeNode("thm-a", "SEALED", ["L.Frozen.a"])
        fails, _ = audit_closures([n], {"L.Frozen.a": {"propext", "extraAxiom"}})
        self.assertEqual(len(fails), 1)
        self.assertIn("extraAxiom", fails[0])

    def test_a_missing_report_is_a_failure_not_a_pass(self):
        """Fail closed: an export the probe never covered is not clean."""
        n = FakeNode("thm-m", "SEALED", ["L.Frozen.m"])
        fails, _ = audit_closures([n], {})
        self.assertEqual(len(fails), 1)
        self.assertIn("did not cover", fails[0])

    def test_every_declaration_of_a_multi_decl_node_is_audited(self):
        n = FakeNode("GFF", "DRAFT_SORRY", ["a", "b", "c"])
        fails, status = audit_closures(
            [n], {"a": {"sorryAx"}, "b": {"sorryAx"}, "c": {"sorryAx"}}
        )
        self.assertEqual(fails, [])
        self.assertEqual(len(status), 3)


if __name__ == "__main__":
    unittest.main()
