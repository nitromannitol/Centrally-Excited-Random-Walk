"""Regression tests for the meta-check.

Each test encodes a real silent vacuous pass observed on 2026-09-23 (see
audit/EVIDENCE-2026-09-23.md, rows V1-V9). Before this package, every one of
these exited 0.
"""

import io
import unittest
from contextlib import redirect_stdout

from leanform_tools.gate import Result, run


class TestMetaCheck(unittest.TestCase):
    def test_zero_processed_is_exit_2_not_0(self):
        """V1: Parking-Sharpness paper_citations reported 0/0/0/0 and exited 0
        while 426 parking.tex citations sat in the tree."""
        r = Result(name="paper_citations", total=426)
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = r.done()
        self.assertEqual(rc, 2)
        self.assertIn("META-CHECK FAILED", buf.getvalue())
        self.assertIn("of 426 available", buf.getvalue())

    def test_zero_processed_reports_the_likely_cause(self):
        r = Result(name="check_clauses")
        buf = io.StringIO()
        with redirect_stdout(buf):
            r.done()
        self.assertIn("source_pin.file", buf.getvalue())

    def test_declared_vacuity_is_allowed_and_explains_itself(self):
        """A repo with no External nodes must still be able to pass."""
        r = Result(name="assumptions", vacuous_ok="this repo has no FROZEN nodes")
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = r.done()
        self.assertEqual(rc, 0)
        self.assertIn("nothing to do", buf.getvalue())

    def test_work_done_with_failures_is_exit_1(self):
        r = Result(name="check_manifest", total=3)
        r.count(3)
        r.fail("node thm-main: hash mismatch")
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = r.done()
        self.assertEqual(rc, 1)
        self.assertIn("3 item(s) inspected", buf.getvalue())

    def test_work_done_clean_is_exit_0_and_prints_the_count(self):
        r = Result(name="check_exponents", total=24)
        r.count(24)
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = r.done()
        self.assertEqual(rc, 0)
        self.assertIn("24 item(s) inspected", buf.getvalue())

    def test_partial_coverage_shows_both_numbers(self):
        r = Result(name="check_clauses", total=24)
        r.count(18)
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = r.done()
        self.assertEqual(rc, 0)
        self.assertIn("18/24", buf.getvalue())

    def test_a_crashing_checker_fails_closed(self):
        def boom(res):
            raise RuntimeError("paper file vanished")

        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = run("check_coverage", boom)
        self.assertEqual(rc, 1)
        self.assertIn("checker raised", buf.getvalue())

    def test_a_checker_that_silently_does_nothing_cannot_pass(self):
        """The whole class: a body that never calls count()."""
        def does_nothing(res):
            return None

        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = run("paper_anchors", does_nothing)
        self.assertEqual(rc, 2)


if __name__ == "__main__":
    unittest.main()
