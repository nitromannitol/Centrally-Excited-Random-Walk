"""Tests for the four build-side tools: check_warnings, check_progress,
certificate, freeze.

Every repo here is synthetic, built fresh in `tempfile.mkdtemp()`; nothing
depends on `~/lean` and nothing here invokes `lake`. The Lake-touching
functions in `certificate.py` (`_run_build`, `_probe_axioms`) and in
`check_warnings.py` (`subprocess.run`) are monkeypatched where a test needs
to exercise the code around them.
"""

from __future__ import annotations

import hashlib
import io
import json
import shutil
import subprocess
import tempfile
import unittest
from contextlib import redirect_stdout
from datetime import date
from pathlib import Path
from unittest import mock

import yaml

from leanform_tools import certificate, check_progress, check_warnings, freeze
from leanform_tools import lean_source as ls
from leanform_tools.config import BEGIN, END, load
from leanform_tools.gate import Result, run

# ---- shared fixtures --------------------------------------------------


class FakeNode:
    """A minimal stand-in for `config.Node`, for the pure functions that
    only need `.id` / `.state` / `.file` / `.decls`."""

    def __init__(self, nid, state, file=None, decls=None):
        self.id = nid
        self.state = state
        self.file = file
        self.decls = decls or []


def _node(id, state, kind="theorem", export=None, file=None,
          frozen_sha256=None, source="demo.tex:1-2 (label demo)"):
    d = {"id": id, "state": state, "kind": kind, "source": source}
    if export:
        d["export"] = export
    if file:
        d["file"] = file
    if frozen_sha256:
        d["frozen_sha256"] = frozen_sha256
    return d


def make_repo(nodes, library="Demo", paper_rel="paper/demo.tex") -> Path:
    root = Path(tempfile.mkdtemp(prefix="leanform-build-side-"))
    (root / "ledger").mkdir(parents=True)
    manifest = {"source_pin": {"file": paper_rel}, "library": library, "nodes": nodes}
    (root / "ledger" / "manifest.yaml").write_text(
        yaml.safe_dump(manifest, sort_keys=False), encoding="utf-8"
    )
    return root


def write_lean(root: Path, rel: str, body: str) -> Path:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body, encoding="utf-8")
    return p


def write_frozen_file(root: Path, rel: str, decl: str) -> Path:
    return write_lean(
        root, rel,
        f"import Init\n\n{BEGIN}\ntheorem {decl} : True := trivial\n{END}\n",
    )


def frozen_hash_of(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    span = ls.frozen_blocks(text)[0]
    return hashlib.sha256(ls.block_body(text, span).encode("utf-8")).hexdigest()


# ---- check_warnings.audit_warnings -------------------------------------


class TestAuditWarnings(unittest.TestCase):
    def test_exactly_one_sorry_per_draft_node_passes(self):
        nodes = [FakeNode("thm-a", "DRAFT_SORRY", file="Demo/Frozen/A.lean")]
        output = "warning: Demo/Frozen/A.lean:10:8: declaration uses 'sorry'\n"
        self.assertEqual(check_warnings.audit_warnings(output, nodes), [])

    def test_an_extra_warning_for_the_same_node_fails(self):
        nodes = [FakeNode("thm-a", "DRAFT_SORRY", file="Demo/Frozen/A.lean")]
        output = (
            "warning: Demo/Frozen/A.lean:10:8: declaration uses 'sorry'\n"
            "warning: Demo/Frozen/A.lean:20:8: declaration uses 'sorry'\n"
        )
        fails = check_warnings.audit_warnings(output, nodes)
        self.assertTrue(any("extra" in f for f in fails), fails)

    def test_a_missing_warning_fails(self):
        nodes = [FakeNode("thm-a", "DRAFT_SORRY", file="Demo/Frozen/A.lean")]
        fails = check_warnings.audit_warnings("", nodes)
        self.assertTrue(any("missing" in f for f in fails), fails)

    def test_sorry_warning_from_a_sealed_nodes_file_fails(self):
        """A `sorry` warning is only authorized for a DRAFT_SORRY node's own
        file; the same warning from a SEALED node's file is unregistered."""
        nodes = [FakeNode("thm-sealed", "SEALED", file="Demo/Frozen/Sealed.lean")]
        output = "warning: Demo/Frozen/Sealed.lean:5:2: declaration uses 'sorry'\n"
        fails = check_warnings.audit_warnings(output, nodes)
        self.assertTrue(
            any("extra" in f and "Sealed.lean" in f for f in fails), fails
        )

    def test_accepts_the_backticked_spelling(self):
        """Lean 4.32+ writes `` declaration uses `sorry` ``, not `'sorry'`."""
        nodes = [FakeNode("thm-a", "DRAFT_SORRY", file="Demo/Frozen/A.lean")]
        output = "warning: Demo/Frozen/A.lean:10:8: declaration uses `sorry`\n"
        self.assertEqual(check_warnings.audit_warnings(output, nodes), [])

    def test_ignores_the_manifest_out_of_date_notice(self):
        nodes = [FakeNode("thm-a", "DRAFT_SORRY", file="Demo/Frozen/A.lean")]
        output = (
            "warning: Demo/Frozen/A.lean:10:8: declaration uses 'sorry'\n"
            "warning: Demo/lakefile.lean:3:0: manifest out of date; "
            "run `lake update`\n"
        )
        self.assertEqual(check_warnings.audit_warnings(output, nodes), [])

    def test_an_unrelated_warning_fails(self):
        nodes = [FakeNode("thm-a", "DRAFT_SORRY", file="Demo/Frozen/A.lean")]
        output = (
            "warning: Demo/Frozen/A.lean:10:8: declaration uses 'sorry'\n"
            "warning: Demo/Frozen/A.lean:1:0: unused variable `x`\n"
        )
        fails = check_warnings.audit_warnings(output, nodes)
        self.assertTrue(any("unexpected warning" in f for f in fails), fails)


class TestCheckWarningsBuildTarget(unittest.TestCase):
    """BUG NOT REPRODUCED: IDLA-Cylinder-GFF/tools/check_warnings.py:68 runs
    `lake build Rotor` regardless of the repo it is copied into. The target
    must come from `cfg.lib_name`, derived from the manifest."""

    def test_build_target_is_derived_from_lib_name_not_hardcoded(self):
        nodes = [_node("thm-a", "SEALED", export="ExplodingSandpiles.Frozen.a")]
        root = make_repo(nodes, library="ExplodingSandpiles")
        self.addCleanup(shutil.rmtree, root, ignore_errors=True)
        cfg = load(root)

        calls: list[list[str]] = []

        def fake_run(cmd, **kwargs):
            calls.append(cmd)
            return subprocess.CompletedProcess(cmd, 0, stdout="")

        with mock.patch(
            "leanform_tools.check_warnings.subprocess.run", side_effect=fake_run
        ):
            res = Result(name="check_warnings")
            check_warnings.check(res, cfg)

        self.assertEqual(calls, [["lake", "build", "ExplodingSandpiles"]])
        self.assertNotIn("Rotor", calls[0])


# ---- check_progress -----------------------------------------------------


class TestAuditProgress(unittest.TestCase):
    def test_rising_total_fails_with_the_required_phrase(self):
        fails, _notes = check_progress.audit_progress(
            {"A.lean": 3}, {"holes": {"A.lean": 1}, "total": 1}
        )
        self.assertTrue(fails)
        self.assertIn("may close holes", fails[0])
        self.assertIn("may not open them", fails[0])

    def test_falling_total_passes(self):
        fails, _notes = check_progress.audit_progress(
            {"A.lean": 1}, {"holes": {"A.lean": 3}, "total": 3}
        )
        self.assertEqual(fails, [])

    def test_steady_total_passes(self):
        fails, _notes = check_progress.audit_progress(
            {"A.lean": 2}, {"holes": {"A.lean": 2}, "total": 2}
        )
        self.assertEqual(fails, [])


class TestCheckProgress(unittest.TestCase):
    def setUp(self):
        self.root = make_repo([])  # no nodes needed; check_progress ignores them
        self.addCleanup(shutil.rmtree, self.root, ignore_errors=True)

    def _write_baseline(self, holes: dict, total: int) -> None:
        (self.root / "ledger" / "holes.json").write_text(
            json.dumps({"holes": holes, "total": total}), encoding="utf-8"
        )

    def test_missing_baseline_is_a_declared_vacuity_pass_not_a_crash(self):
        write_lean(self.root, "Demo/Foo.lean", "theorem foo : True := by sorry\n")
        cfg = load(self.root)
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = run("check_progress", check_progress.check, cfg)
        self.assertEqual(rc, 0)
        self.assertIn("nothing to do", buf.getvalue())

    def test_closing_holes_passes(self):
        write_lean(self.root, "Demo/Foo.lean", "theorem foo : True := trivial\n")
        self._write_baseline({"Demo/Foo.lean": 2}, 2)
        cfg = load(self.root)
        rc = run("check_progress", check_progress.check, cfg)
        self.assertEqual(rc, 0)

    def test_opening_a_hole_fails(self):
        write_lean(self.root, "Demo/Foo.lean", "theorem foo : True := by sorry\n")
        self._write_baseline({}, 0)
        cfg = load(self.root)

        res = Result(name="check_progress")
        check_progress.check(res, cfg)
        self.assertTrue(any("may close holes" in f for f in res.failures))

        rc = run("check_progress", check_progress.check, cfg)
        self.assertEqual(rc, 1)

    def test_a_hole_masked_as_a_comment_is_not_counted(self):
        write_lean(
            self.root, "Demo/Foo.lean",
            "-- sorry, this comment is not a hole\ntheorem foo : True := trivial\n",
        )
        self._write_baseline({}, 0)
        cfg = load(self.root)
        rc = run("check_progress", check_progress.check, cfg)
        self.assertEqual(rc, 0)

    def test_record_writes_the_baseline_from_the_current_tree(self):
        write_lean(self.root, "Demo/Foo.lean", "theorem foo : True := by sorry\n")
        cfg = load(self.root)
        res = Result(name="check_progress")
        check_progress.check(res, cfg, record=True)
        baseline = json.loads((self.root / "ledger" / "holes.json").read_text())
        self.assertEqual(baseline, {"holes": {"Demo/Foo.lean": 1}, "total": 1})


# ---- certificate ----------------------------------------------------------


class TestClaimSummary(unittest.TestCase):
    def test_all_sealed_emits_the_unconditional_sentence(self):
        nodes = [FakeNode(f"n{i}", "SEALED") for i in range(3)]
        text = certificate.claim_summary(nodes)
        self.assertIn("is `SEALED`", text)

    def test_sealed_and_frozen_mix_never_claims_all_sealed(self):
        """Pins the Divisible-Sandpile-Percolation bug: certificate.py:170
        printed "Every node's state in `ledger/manifest.yaml` is `SEALED`."
        unconditionally on a manifest with 78 SEALED and 26 FROZEN nodes."""
        nodes = [FakeNode(f"s{i}", "SEALED") for i in range(78)] + [
            FakeNode(f"f{i}", "FROZEN") for i in range(26)
        ]
        text = certificate.claim_summary(nodes)
        self.assertNotIn(
            "Every node's state in `ledger/manifest.yaml` is `SEALED`.", text
        )
        self.assertIn("78", text)
        self.assertIn("26", text)
        self.assertIn("FROZEN", text)

    def test_a_draft_sorry_node_is_named_and_not_folded_into_sealed(self):
        nodes = [FakeNode("s1", "SEALED"), FakeNode("d1", "DRAFT_SORRY")]
        text = certificate.claim_summary(nodes)
        self.assertNotIn("is `SEALED`.", text)
        self.assertIn("DRAFT_SORRY", text)


class TestVerdict(unittest.TestCase):
    def test_clean_closure_is_classical_only(self):
        self.assertEqual(certificate._verdict([{"propext"}], "SEALED"), "classical only")

    def test_sorry_ax_on_a_draft_node_is_registered(self):
        v = certificate._verdict([{"propext", "sorryAx"}], "DRAFT_SORRY")
        self.assertIn("registered draft", v)

    def test_sorry_ax_on_a_sealed_node_is_flagged(self):
        v = certificate._verdict([{"sorryAx"}], "SEALED")
        self.assertIn("sorryAx", v)
        self.assertTrue(v.startswith("**"))

    def test_an_extra_axiom_is_flagged(self):
        v = certificate._verdict([{"propext", "extraAxiom"}], "SEALED")
        self.assertIn("extraAxiom", v)
        self.assertTrue(v.startswith("**"))


class TestRender(unittest.TestCase):
    def test_mismatched_frozen_hash_is_flagged_and_matching_is_not(self):
        nodes = [
            _node("thm-a", "SEALED", export="Demo.Frozen.a", frozen_sha256="aaaa"),
            _node("ext-b", "FROZEN", kind="definition",
                  export="Demo.External.b", frozen_sha256="bbbb"),
        ]
        root = make_repo(nodes)
        self.addCleanup(shutil.rmtree, root, ignore_errors=True)
        cfg = load(root)
        data = {
            "toolchain": "leanprover/lean4:v4.99.0",
            "mathlib_rev": "d" * 40,
            "paper_sha": "0" * 64,
            "frozen_hashes": {"thm-a": "wronghash", "ext-b": "bbbb"},
            "build_jobs": "3",
            "warning_count": 0,
            "axiom_reports": {"Demo.Frozen.a": {"propext"}},
        }
        text = certificate.render(cfg, data, today="2026-01-01")
        a_row = next(l for l in text.splitlines() if l.startswith("| `thm-a` |"))
        b_row = next(l for l in text.splitlines() if l.startswith("| `ext-b` |"))
        self.assertIn("MISMATCH", a_row)
        self.assertNotIn("MISMATCH", b_row)


class TestCertificateWriteSafety(unittest.TestCase):
    """MUST HOLD: a failed generation never overwrites a good CERTIFICATE.md."""

    def test_failed_generation_does_not_touch_the_existing_certificate(self):
        nodes = [_node("thm-a", "SEALED", export="Demo.Frozen.a")]
        root = make_repo(nodes)
        self.addCleanup(shutil.rmtree, root, ignore_errors=True)
        existing = "# OLD CERTIFICATE\n\ndo not touch\n"
        (root / certificate.OUT_NAME).write_text(existing, encoding="utf-8")
        cfg = load(root)

        with mock.patch.object(
            certificate, "gather", side_effect=certificate.CertificateError("boom")
        ):
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = run("certificate", certificate.check, cfg)

        self.assertEqual(rc, 1)
        self.assertEqual(
            (root / certificate.OUT_NAME).read_text(encoding="utf-8"), existing
        )


class TestCertificateCheckFlow(unittest.TestCase):
    """`gather()`'s Lake calls are monkeypatched; nothing here runs Lake."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix="leanform-cert-flow-"))
        self.addCleanup(shutil.rmtree, self.root, ignore_errors=True)
        (self.root / "ledger").mkdir(parents=True)
        (self.root / "paper").mkdir()
        (self.root / "paper" / "demo.tex").write_text("hello\n", encoding="utf-8")
        (self.root / "lean-toolchain").write_text(
            "leanprover/lean4:v4.99.0\n", encoding="utf-8"
        )
        frozen_path = write_frozen_file(self.root, "Demo/Frozen/A.lean", "a")
        sha = frozen_hash_of(frozen_path)

        manifest = {
            "source_pin": {"file": "paper/demo.tex"},
            "library": "Demo",
            "nodes": [
                _node("thm-a", "SEALED", export="Demo.Frozen.a",
                      file="Demo/Frozen/A.lean", frozen_sha256=sha),
            ],
        }
        (self.root / "ledger" / "manifest.yaml").write_text(
            yaml.safe_dump(manifest, sort_keys=False), encoding="utf-8"
        )
        self.cfg = load(self.root)

    @staticmethod
    def _fake_build(cfg):
        return subprocess.CompletedProcess(
            ["lake", "build", cfg.lib_name], 0,
            stdout="Build completed successfully (3 jobs)\n", stderr="",
        )

    @staticmethod
    def _fake_probe(cfg):
        return {"Demo.Frozen.a": {"propext", "Classical.choice", "Quot.sound"}}

    def test_write_then_check_round_trips(self):
        with mock.patch.object(certificate, "_run_build", side_effect=self._fake_build), \
             mock.patch.object(certificate, "_probe_axioms", side_effect=self._fake_probe):
            res1 = Result(name="certificate")
            certificate.check(res1, self.cfg, write=True)
            self.assertEqual(res1.failures, [])
            self.assertTrue((self.root / certificate.OUT_NAME).exists())

            res2 = Result(name="certificate")
            certificate.check(res2, self.cfg, write=False)
            self.assertEqual(res2.failures, [])

    def test_check_tolerates_a_different_generated_date(self):
        with mock.patch.object(certificate, "_run_build", side_effect=self._fake_build), \
             mock.patch.object(certificate, "_probe_axioms", side_effect=self._fake_probe):
            stale_text = certificate.generate(self.cfg, today="2000-01-01")
            (self.root / certificate.OUT_NAME).write_text(stale_text, encoding="utf-8")

            res = Result(name="certificate")
            certificate.check(res, self.cfg, write=False)
            self.assertEqual(res.failures, [])

    def test_check_reports_a_genuinely_stale_certificate(self):
        with mock.patch.object(certificate, "_run_build", side_effect=self._fake_build), \
             mock.patch.object(certificate, "_probe_axioms", side_effect=self._fake_probe):
            (self.root / certificate.OUT_NAME).write_text(
                "not the generated text at all\n", encoding="utf-8"
            )
            res = Result(name="certificate")
            certificate.check(res, self.cfg, write=False)
            self.assertTrue(res.failures)


# ---- freeze -----------------------------------------------------------


class TestFreeze(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix="leanform-freeze-"))
        self.addCleanup(shutil.rmtree, self.root, ignore_errors=True)
        (self.root / "ledger").mkdir(parents=True)
        write_frozen_file(self.root, "Demo/Frozen/X.lean", "demo_x")
        manifest_text = (
            "version: 1\nnodes:\n"
            "  - id: thm-x\n"
            "    version: 1\n"
            "    kind: theorem\n"
            "    source: demo.tex:1-2 (label demo)\n"
            "    file: Demo/Frozen/X.lean\n"
            "    export: Demo.Frozen.demo_x\n"
            "    state: SEALED\n"
            "    frozen_sha256: 0000000000000000000000000000000000000000000000000000000000000000\n"
            "    provider: Demo.Frozen.demo_x\n"
            '    approved: "2020-01-01"\n\n'
        )
        (self.root / "ledger" / "manifest.yaml").write_text(
            manifest_text, encoding="utf-8"
        )
        self.cfg = load(self.root)

    def test_refuses_a_source_containing_colon_space(self):
        with self.assertRaises(freeze.FreezeError):
            freeze.freeze(
                self.cfg, "thm-x", "Demo/Frozen/X.lean", "Demo.Frozen.demo_x",
                "theorem", "SEALED", "demo.tex: this has a colon-space",
            )
        # refused before any write
        self.assertIn("version: 1", self.cfg.manifest_path.read_text(encoding="utf-8"))

    def test_refuses_a_source_containing_a_quote_character(self):
        with self.assertRaises(freeze.FreezeError):
            freeze.freeze(
                self.cfg, "thm-x", "Demo/Frozen/X.lean", "Demo.Frozen.demo_x",
                "theorem", "SEALED", "demo.tex:1-2 (label it's-fine)",
            )
        with self.assertRaises(freeze.FreezeError):
            freeze.freeze(
                self.cfg, "thm-x", "Demo/Frozen/X.lean", "Demo.Frozen.demo_x",
                "theorem", "SEALED", 'demo.tex:1-2 (label "quoted")',
            )

    def test_bumps_version_on_refreeze(self):
        summary = freeze.freeze(
            self.cfg, "thm-x", "Demo/Frozen/X.lean", "Demo.Frozen.demo_x",
            "theorem", "SEALED", "demo.tex:1-2 (label demo)",
        )
        self.assertIn("version 2", summary)
        text = self.cfg.manifest_path.read_text(encoding="utf-8")
        self.assertEqual(text.count("id: thm-x"), 1)
        self.assertIn("version: 2", text)

    def test_stamps_approved_with_today(self):
        freeze.freeze(
            self.cfg, "thm-x", "Demo/Frozen/X.lean", "Demo.Frozen.demo_x",
            "theorem", "SEALED", "demo.tex:1-2 (label demo)",
        )
        text = self.cfg.manifest_path.read_text(encoding="utf-8")
        self.assertIn(f'approved: "{date.today().isoformat()}"', text)

    def test_a_fresh_id_is_recorded_at_version_one(self):
        write_frozen_file(self.root, "Demo/Frozen/Y.lean", "demo_y")
        summary = freeze.freeze(
            self.cfg, "thm-y", "Demo/Frozen/Y.lean", "Demo.Frozen.demo_y",
            "theorem", "DRAFT_SORRY", "demo.tex:3-4 (label demo-y)",
        )
        self.assertIn("version 1", summary)
        text = self.cfg.manifest_path.read_text(encoding="utf-8")
        self.assertIn("id: thm-x", text)
        self.assertIn("id: thm-y", text)

    def test_frozen_hash_matches_check_manifests_recipe(self):
        summary = freeze.freeze(
            self.cfg, "thm-x", "Demo/Frozen/X.lean", "Demo.Frozen.demo_x",
            "theorem", "SEALED", "demo.tex:1-2 (label demo)",
        )
        want = frozen_hash_of(self.root / "Demo/Frozen/X.lean")
        self.assertIn(want[:12], summary)


if __name__ == "__main__":
    unittest.main()
