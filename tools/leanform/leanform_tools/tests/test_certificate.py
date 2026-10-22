"""Certificate axiom probes fail closed without requiring a Lean toolchain."""

import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from leanform_tools import certificate


class TestCertificateProbe(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="leanform-certificate-probe-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        node = SimpleNamespace(file="Demo/Frozen/Main.lean", decls=["Demo.main", "Demo.other"])
        self.cfg = SimpleNamespace(root=self.root, nodes=[node])

    def probe(self, code, stdout, stderr=""):
        process = subprocess.CompletedProcess([], code, stdout, stderr)
        with patch.object(certificate.subprocess, "run", return_value=process):
            return certificate._probe_axioms(self.cfg)

    def assert_probe_removed(self):
        self.assertEqual(list((self.root / "scratch").iterdir()), [])

    def test_nonzero_exit_rejects_complete_clean_reports_before_later_error(self):
        output = (
            "'Demo.main' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'Demo.other' does not depend on any axioms\n"
            "error: later Lean command failed\n"
        )
        for code in (1, 2, -9):
            with self.subTest(code=code):
                with self.assertRaises(certificate.CertificateError) as caught:
                    self.probe(code, output, "stderr diagnostic")
                message = str(caught.exception)
                self.assertIn(f"code {code}", message)
                self.assertIn("'Demo.main' depends on axioms", message)
                self.assertIn("error: later Lean command failed", message)
                self.assertIn("stderr diagnostic", message)
                self.assert_probe_removed()

    def test_nonzero_exit_rejects_complete_no_axiom_reports(self):
        output = (
            "'Demo.main' does not depend on any axioms\n"
            "'Demo.other' does not depend on any axioms\n"
        )
        with self.assertRaises(certificate.CertificateError):
            self.probe(1, output)
        self.assert_probe_removed()

    def test_failure_context_is_bounded_to_stdout_and_stderr_tails(self):
        stdout = "stdout prefix" + "x" * 2100 + "stdout tail"
        stderr = "stderr prefix" + "y" * 2100 + "stderr tail"
        with self.assertRaises(certificate.CertificateError) as caught:
            self.probe(1, stdout, stderr)
        message = str(caught.exception)
        self.assertIn("stdout:\n" + stdout[-2000:], message)
        self.assertIn("stderr:\n" + stderr[-2000:], message)
        self.assertNotIn("stdout prefix", message)
        self.assertNotIn("stderr prefix", message)
        self.assert_probe_removed()

    def test_successful_standard_and_no_axiom_reports_are_preserved(self):
        output = (
            "'Demo.main' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
            "'Demo.other' does not depend on any axioms\n"
        )
        self.assertEqual(self.probe(0, output), {
            "Demo.main": {"propext", "Classical.choice", "Quot.sound"},
            "Demo.other": set(),
        })
        self.assert_probe_removed()

    def test_missing_tool_and_timeout_still_remove_probe(self):
        for error in (FileNotFoundError(), subprocess.TimeoutExpired("lake", 7200)):
            with self.subTest(error=type(error).__name__):
                with patch.object(certificate.subprocess, "run", side_effect=error):
                    with self.assertRaises(certificate.CertificateError):
                        certificate._probe_axioms(self.cfg)
                self.assert_probe_removed()


if __name__ == "__main__":
    unittest.main()
