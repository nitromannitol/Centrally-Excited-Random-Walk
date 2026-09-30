"""Tests for the three reading-side checkers (check_clauses, check_constants,
check_exponents) and the readings.py migration/loading module.

Every repo here is synthetic, built fresh in `tempfile.mkdtemp()`; nothing
depends on `~/lean`. Each test double-checks one concrete failure mode these
checkers exist to catch:

* a node with no recorded reading must fail check_clauses, unconditionally;
* `2/3` vs `1/3` is a transposition no Lean type error would catch, and the
  exponent comparison must be a multiset comparison so a repeated-occurrence
  mismatch is also caught, not just a missing value;
* `∃ c, ∀ β` (correct: the constant is chosen before β) vs `∀ β, ∃ c`
  (wrong: the "constant" may depend on β) must be told apart by quantifier
  order alone;
* a bracket-oblivious regex over the binder list reads a nested type
  ascription like `Var (m : ℝ)` as if it were its own top-level parameter;
  the bracket-depth-tracked scanner here must not;
* a declared waiver in `readings.yaml` must suppress the failure it
  documents and must still be printed, not silently swallowed;
* a manifest with no nodes at all must exit 2 (the meta-check), never 0 —
  this is the class of bug that let two repos' vendored copies of
  check_clauses/check_exponents report "OK (0 statements)" against 24 real
  nodes, because a literal `rotor\\.tex` regex never matched their paper.
"""

from __future__ import annotations

import io
import shutil
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

import yaml

from leanform_tools import check_clauses, check_constants, check_exponents, readings
from leanform_tools.config import BEGIN, END, load
from leanform_tools.gate import Result, run

# ---------------------------------------------------------------------------
# repo-building helpers
# ---------------------------------------------------------------------------


def _node(id: str, source: str, file: str, export: str | None = None,
          state: str = "SEALED", kind: str = "theorem") -> dict:
    d = {"id": id, "source": source, "file": file, "state": state, "kind": kind}
    if export:
        d["export"] = export
    return d


class _TempRepoTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self._roots: list[Path] = []

    def tearDown(self) -> None:
        for r in self._roots:
            shutil.rmtree(r, ignore_errors=True)

    def track(self, root: Path) -> Path:
        self._roots.append(root)
        return root

    def make_repo(self, nodes: list[dict], paper_text: str,
                   paper_rel: str = "paper/foo.tex", library: str = "Demo") -> Path:
        root = Path(tempfile.mkdtemp(prefix="leanform-reading-side-"))
        (root / "ledger").mkdir(parents=True)
        manifest = {"source_pin": {"file": paper_rel}, "library": library, "nodes": nodes}
        (root / "ledger" / "manifest.yaml").write_text(
            yaml.safe_dump(manifest, sort_keys=False, allow_unicode=True), encoding="utf-8"
        )
        paper_path = root / paper_rel
        paper_path.parent.mkdir(parents=True, exist_ok=True)
        paper_path.write_text(paper_text, encoding="utf-8")
        return self.track(root)

    def write_lean(self, root: Path, rel: str, statement: str) -> None:
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            "import Init\n\n" + f"{BEGIN}\n{statement}\n{END}\n", encoding="utf-8",
        )

    def write_readings(self, root: Path, data: dict) -> None:
        path = root / "ledger" / "readings.yaml"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(yaml.safe_dump(data, sort_keys=True, allow_unicode=True), encoding="utf-8")


def _run_capturing(name: str, fn, cfg) -> tuple[int, str]:
    buf = io.StringIO()
    with redirect_stdout(buf):
        rc = run(name, fn, cfg)
    return rc, buf.getvalue()


# ---------------------------------------------------------------------------
# check_clauses
# ---------------------------------------------------------------------------

PAPER_ONE = (
    "preamble line\n"                       # 1
    "\\begin{equation}\\label{thm:one}\n"   # 2
    "  a \\leq b \\leq c\n"                 # 3
    "\\end{equation}\n"                     # 4
    "trailing prose\n"                      # 5
)
LEAN_ONE = "theorem one_thing (a b c : ℝ) : a ≤ c := by sorry"


class TestCheckClauses(_TempRepoTestCase):
    def test_node_with_no_reading_fails(self):
        root = self.make_repo(
            [_node("thm-one", "foo.tex:2-4 (label thm:one)", "Demo/Frozen/One.lean")],
            PAPER_ONE,
        )
        self.write_lean(root, "Demo/Frozen/One.lean", LEAN_ONE)
        cfg = load(root)
        rc, out = _run_capturing("check_clauses", check_clauses.check, cfg)
        self.assertEqual(rc, 1)
        self.assertIn("no reading in readings.yaml['clauses']", out)

    def test_reading_present_passes_and_count_mismatch_is_only_a_note(self):
        """paper_units=2 (two \\leq) > lean_conjuncts=1: a prompt, not a failure."""
        root = self.make_repo(
            [_node("thm-one", "foo.tex:2-4 (label thm:one)", "Demo/Frozen/One.lean")],
            PAPER_ONE,
        )
        self.write_lean(root, "Demo/Frozen/One.lean", LEAN_ONE)
        self.write_readings(root, {"clauses": {"thm-one": "paper: a<=b<=c; Lean: a<=c, same content"}})
        cfg = load(root)
        rc, out = _run_capturing("check_clauses", check_clauses.check, cfg)
        self.assertEqual(rc, 0)
        self.assertIn("paper's assertion-unit count (2) exceeds Lean's top-level "
                      "conjunct count (1)", out)

    def test_vacuous_manifest_exits_2(self):
        root = self.make_repo([], "just a preamble\n")
        cfg = load(root)
        rc, out = _run_capturing("check_clauses", check_clauses.check, cfg)
        self.assertEqual(rc, 2)
        self.assertIn("META-CHECK FAILED", out)

    def test_node_without_paper_range_still_requires_a_reading(self):
        """An external-input node skips the count heuristic but not the gate."""
        root = self.make_repo(
            [_node("ext-1", "external input, cited classical fact", "Demo/External/Ext.lean")],
            "no statements here\n",
        )
        self.write_lean(root, "Demo/External/Ext.lean", "theorem ext_1 : True := trivial")
        cfg = load(root)

        rc, out = _run_capturing("check_clauses", check_clauses.check, cfg)
        self.assertEqual(rc, 1)
        self.assertIn("no reading in readings.yaml['clauses']", out)

        self.write_readings(root, {"clauses": {"ext-1": "the classical fact X, cited not proved"}})
        rc2, out2 = _run_capturing("check_clauses", check_clauses.check, cfg)
        self.assertEqual(rc2, 0)
        self.assertIn("assertion-count heuristic skipped", out2)

    def test_paper_name_is_never_hardcoded(self):
        """Same structure, two different paper basenames: behavior must not change.

        This is the regression for the literal `rotor\\.tex` regex that made
        two vendored copies of this checker inspect 0 of 24 real nodes.
        """
        for paper_rel in ("paper/rotor.tex", "paper/totally_unrelated_name.tex"):
            stem = Path(paper_rel).name
            paper_text = (
                "preamble\n"
                f"\\begin{{equation}}\\label{{thm:x}}\n"
                "  a \\leq b\n"
                "\\end{equation}\n"
            )
            root = self.make_repo(
                [_node("thm-x", f"{stem}:2-4 (label thm:x)", "Demo/Frozen/X.lean")],
                paper_text, paper_rel=paper_rel,
            )
            self.write_lean(root, "Demo/Frozen/X.lean", "theorem x_thing : True := trivial")
            self.write_readings(root, {"clauses": {"thm-x": "trivial reading"}})
            cfg = load(root)
            res = Result(name="check_clauses")
            check_clauses.check(res, cfg)
            self.assertEqual(res.processed, 1, f"paper {paper_rel!r} was not inspected")
            self.assertEqual(res.failures, [])


# ---------------------------------------------------------------------------
# check_constants
# ---------------------------------------------------------------------------

class TestCheckConstants(_TempRepoTestCase):
    def _single_node_cfg(self, statement: str):
        root = self.make_repo(
            [_node("thm-c", "unknown", "Demo/Frozen/C.lean")],
            "no paper needed for this checker\n",
        )
        self.write_lean(root, "Demo/Frozen/C.lean", statement)
        return root

    def test_exists_c_forall_beta_is_the_correct_order_and_passes(self):
        """`∃ c, ∀ β`: the constant is chosen before β varies. Correct."""
        root = self._single_node_cfg(
            "theorem good (d : ℕ) : ∃ c : ℝ, 0 < c ∧ "
            "∀ β : ℝ, 1 ≤ β → c * β ≤ 1 := by sorry"
        )
        cfg = load(root)
        res = Result(name="check_constants")
        check_constants.check(res, cfg)
        self.assertEqual(res.failures, [])
        self.assertEqual(res.processed, 1)

    def test_forall_beta_exists_c_is_the_wrong_order_and_fails(self):
        """`∀ β, ∃ c`: β is bound as a parameter before the existential, so
        the "constant" may secretly depend on β. Caught by quantifier order
        alone, with no type error anywhere."""
        root = self._single_node_cfg(
            "theorem bad (β : ℝ) (hβ : 1 ≤ β) : ∃ c : ℝ, 0 < c ∧ c * β ≤ 1 := by sorry"
        )
        cfg = load(root)
        res = Result(name="check_constants")
        check_constants.check(res, cfg)
        self.assertEqual(len(res.failures), 1)
        self.assertIn("β", res.failures[0])

    def test_nested_type_ascription_is_not_read_as_a_top_level_parameter(self):
        """`Var (m : ℝ)` sits inside the body of hypothesis `hb`, two brackets
        deep. A bracket-oblivious regex over the whole binder string reads it
        as its own top-level `(m : ℝ)` parameter anyway (`m` is in
        FORBIDDEN); the bracket-depth-tracked scanner must not."""
        statement = (
            "theorem tricky (hb : ∀ z : ℝ, Var (m : ℝ) z ≤ 1) : "
            "∃ c : ℝ, 0 < c ∧ c ≤ 1 := by sorry"
        )
        binders, _ = check_constants.split_statement(statement)
        params = check_constants.parameters(binders)
        self.assertNotIn("m", params)
        self.assertIn("hb", params)

        # Contrast: the naive bracket-oblivious regex (as vendored in
        # Unique-Continuation-Planar and Parking-Sharpness) DOES pick up the
        # nested "m" as if it were a top-level parameter.
        import re
        naive = {tok for m in re.finditer(r"[({\[]([^:()\[\]{}]+):", binders)
                 for tok in m.group(1).split()}
        self.assertIn("m", naive, "the naive regex should exhibit the bug being avoided")

        root = self._single_node_cfg(statement)
        cfg = load(root)
        res = Result(name="check_constants")
        check_constants.check(res, cfg)
        self.assertEqual(res.failures, [])

    def test_declared_waiver_suppresses_failure_and_is_printed(self):
        root = self._single_node_cfg(
            "theorem bad (β : ℝ) (hβ : 1 ≤ β) : ∃ c : ℝ, 0 < c ∧ c * β ≤ 1 := by sorry"
        )
        self.write_readings(root, {
            "constants": {"thm-c": "β: the paper fixes β before every clause (rem:x, foo.tex:1-1)"}
        })
        cfg = load(root)
        rc, out = _run_capturing("check_constants", check_constants.check, cfg)
        self.assertEqual(rc, 0)
        self.assertIn("waiver on record", out)
        self.assertIn("the paper fixes β before every clause", out)

    def test_vacuous_manifest_exits_2(self):
        root = self.make_repo([], "no paper needed\n")
        cfg = load(root)
        rc, out = _run_capturing("check_constants", check_constants.check, cfg)
        self.assertEqual(rc, 2)
        self.assertIn("META-CHECK FAILED", out)


# ---------------------------------------------------------------------------
# check_exponents
# ---------------------------------------------------------------------------

PAPER_TRANSPOSE = (
    "preamble\n"                            # 1
    "\\begin{equation}\\label{thm:tr}\n"    # 2
    "  x^{2/3} = y\n"                       # 3
    "\\end{equation}\n"                     # 4
)

PAPER_TWICE = (
    "preamble\n"                            # 1
    "\\begin{equation}\\label{thm:two}\n"   # 2
    "  x^{2/3} = y\n"                       # 3
    "\\end{equation}\n"                     # 4
    "\\begin{equation}\n"                   # 5
    "  z^{2/3} = w\n"                       # 6
    "\\end{equation}\n"                     # 7
)


class TestCheckExponents(_TempRepoTestCase):
    def test_transposition_2_3_vs_1_3_is_caught(self):
        """No Lean type error would catch this; the exponent gate must."""
        root = self.make_repo(
            [_node("thm-tr", "foo.tex:2-4 (label thm:tr)", "Demo/Frozen/Tr.lean")],
            PAPER_TRANSPOSE,
        )
        self.write_lean(root, "Demo/Frozen/Tr.lean", "theorem tr_thing : y ^ (1/3) = x := by sorry")
        cfg = load(root)
        res = Result(name="check_exponents")
        check_exponents.check(res, cfg)
        self.assertEqual(len(res.failures), 1)
        self.assertIn("2/3", res.failures[0])

    def test_matching_exponent_passes(self):
        root = self.make_repo(
            [_node("thm-tr", "foo.tex:2-4 (label thm:tr)", "Demo/Frozen/Tr.lean")],
            PAPER_TRANSPOSE,
        )
        self.write_lean(root, "Demo/Frozen/Tr.lean", "theorem tr_thing : y ^ (2/3) = x := by sorry")
        cfg = load(root)
        res = Result(name="check_exponents")
        check_exponents.check(res, cfg)
        self.assertEqual(res.failures, [])
        self.assertEqual(res.processed, 1)

    def test_repeated_occurrence_mismatch_is_reported_but_does_not_fail(self):
        """The paper's line range asserts `2/3` twice; Lean has it once.

        This test originally asserted a failure. It is now a *note*, and the
        change is deliberate: the shape that produces it is
        `|R_t| = c t^{2/3} + o(t^{2/3})`, where the paper necessarily names
        the exponent twice and any faithful Lean rendering — a single
        `Tendsto (… / t ^ (2/3))` — names it once. rotor-23's
        `prop-path-reduction` and `prop-circuit-clock` are exactly this, and
        their incumbent checker passed. Failing here fires on a universal
        idiom and pushes a reviewer toward a blanket waiver, which would cost
        the real check.

        The original intent — that it must not *silently* pass — is kept: the
        difference is still surfaced, as a note naming both counts.
        """
        root = self.make_repo(
            [_node("thm-two", "foo.tex:2-7 (label thm:two)", "Demo/Frozen/Two.lean")],
            PAPER_TWICE,
        )
        self.write_lean(root, "Demo/Frozen/Two.lean", "theorem two_thing : x ^ (2/3) = w := by sorry")
        cfg = load(root)
        res = Result(name="check_exponents")
        check_exponents.check(res, cfg)
        self.assertEqual(res.failures, [])
        self.assertTrue(
            any("2/3" in n and "paper 2x" in n for n in res.notes),
            f"the multiplicity difference must still be surfaced; notes were {res.notes}",
        )

    def test_declared_waiver_suppresses_failure_and_is_printed(self):
        root = self.make_repo(
            [_node("thm-tr", "foo.tex:2-4 (label thm:tr)", "Demo/Frozen/Tr.lean")],
            PAPER_TRANSPOSE,
        )
        self.write_lean(root, "Demo/Frozen/Tr.lean", "theorem tr_thing : y ^ (1/3) = x := by sorry")
        self.write_readings(root, {
            "exponents": {"thm-tr": [
                {"kind": "notation", "detail": "2/3: Lean spells this fraction 1/3 elsewhere; read and matches"}
            ]}
        })
        cfg = load(root)
        rc, out = _run_capturing("check_exponents", check_exponents.check, cfg)
        self.assertEqual(rc, 0)
        self.assertIn("waiver [notation]", out)
        self.assertIn("Lean spells this fraction 1/3 elsewhere", out)

    def test_vacuous_manifest_exits_2(self):
        root = self.make_repo([], "no statements\n")
        cfg = load(root)
        rc, out = _run_capturing("check_exponents", check_exponents.check, cfg)
        self.assertEqual(rc, 2)
        self.assertIn("META-CHECK FAILED", out)

    def test_lean_exponents_handles_spaced_fraction_with_type_ascription(self):
        """rotor-23's `Rotor/Frozen/Shape/PathReduction.lean:64` writes the
        exponent as `^ (2 / 3 : ℝ)` — spaces around `/` and a trailing type
        ascription inside the same parens. This must read as `2/3`, not be
        dropped."""
        frag = "Tendsto (fun t : ℕ => (R t).card / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c)"
        self.assertEqual(check_exponents.lean_exponents(frag), {"2/3": 1})

    def test_frac_macro_normalizes_to_match_leans_division(self):
        """ORRW's paper writes `\\beta^{-\\frac{d}{d+1}} n^{\\frac{d}{d+1}}`;
        its Lean statement writes the same quantity as
        `β ^ (-((d:ℝ)/((d:ℝ)+1)))` and `n ^ ((d:ℝ)/((d:ℝ)+1))`. Without a
        `\\frac` normalizer every fractional exponent in that repo reads as
        present in the paper and absent in Lean."""
        seg = "\\beta^{-\\frac{d}{d+1}}n^{\\frac{d}{d+1}}\n"
        pe, _ = check_exponents.paper_exponents(seg)
        self.assertEqual(dict(pe), {"-d/(d+1)": 1, "d/(d+1)": 1})

        lean_frag = (
            "β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))"
        )
        le = check_exponents.lean_exponents(lean_frag)
        self.assertEqual(le.get("-d/(d+1)"), 1)
        self.assertEqual(le.get("d/(d+1)"), 1)

    def test_bare_identifier_is_not_an_exponent_only_when_declared_as_repo_noise(self):
        """ORRW's `lem:schur` writes `(A^+)^c` (set-complement notation);
        `c` is not an exponent there. But `c` is a real exponent letter in
        general (these papers reserve `c`/`C` for constants, never for a
        genuine power, so this is safe) and must NOT be filtered by
        default — only when the repo's own `readings.yaml['noise']` says so,
        the way ORRW's own incumbent NOISE set did. A blanket addition to
        the shared NOISE set would hide a real gap elsewhere (Dynamic-
        Dimensional-Reduction's `prop-no-reduction` genuinely needs a bare
        `d` to be tracked, for instance) — so the vocabulary must be
        per-repo, not global.
        """
        paper = (
            "preamble\n"                                     # 1
            "\\begin{equation}\\label{thm:schur}\n"          # 2
            "  \\Reff\\bigl(x\\leftrightarrow(A^+)^c\\bigr)\n"  # 3
            "\\end{equation}\n"                               # 4
        )
        root = self.make_repo(
            [_node("lem-schur", "foo.tex:2-4 (label thm:schur)", "Demo/Frozen/Schur.lean")],
            paper,
        )
        self.write_lean(root, "Demo/Frozen/Schur.lean", "theorem schur : True := trivial")
        cfg = load(root)

        res = Result(name="check_exponents")
        check_exponents.check(res, cfg)
        self.assertEqual(len(res.failures), 1, "by default 'c' is a real exponent, not noise")
        self.assertIn("c", res.failures[0])

        self.write_readings(root, {"noise": ["c"]})
        cfg2 = load(root)
        res2 = Result(name="check_exponents")
        check_exponents.check(res2, cfg2)
        self.assertEqual(res2.failures, [], "declaring 'c' as this repo's noise must suppress it")


# ---------------------------------------------------------------------------
# readings.py: loading and AST-based migration
# ---------------------------------------------------------------------------

class TestLoadReadings(_TempRepoTestCase):
    def test_missing_file_returns_empty_structure(self):
        root = self.make_repo([], "no statements\n")
        cfg = load(root)
        data = readings.load_readings(cfg)
        self.assertEqual(data, {"clauses": {}, "constants": {}, "exponents": {}})

    def test_reads_an_existing_file(self):
        root = self.make_repo([], "no statements\n")
        self.write_readings(root, {"clauses": {"n1": "a reading"}})
        cfg = load(root)
        data = readings.load_readings(cfg)
        self.assertEqual(data["clauses"], {"n1": "a reading"})
        self.assertEqual(data["constants"], {})
        self.assertEqual(data["exponents"], {})


class TestExtractRepo(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="leanform-extract-"))
        (self.root / "tools").mkdir(parents=True)

    def tearDown(self) -> None:
        shutil.rmtree(self.root, ignore_errors=True)

    def _write(self, name: str, text: str) -> None:
        (self.root / "tools" / name).write_text(text, encoding="utf-8")

    def test_clauses_dict_is_copied_verbatim(self):
        self._write("check_clauses.py", "REVIEWED: dict[str, str] = {\n"
                     "    'n1': 'paper: one claim; Lean: one conjunct, matches',\n"
                     "}\n")
        data = readings.extract_repo(self.root)
        self.assertEqual(
            data["clauses"], {"n1": "paper: one claim; Lean: one conjunct, matches"}
        )

    def test_constants_dict_is_flattened_to_one_string_per_node(self):
        self._write("check_constants.py", "REVIEWED: dict[str, dict[str, str]] = {\n"
                     "    'n1': {'y': 'reason y', 'x': 'reason x'},\n"
                     "}\n")
        data = readings.extract_repo(self.root)
        self.assertEqual(data["constants"]["n1"], "x: reason x; y: reason y")

    def test_exponents_dict_becomes_a_list_of_kind_detail_entries(self):
        self._write("check_exponents.py", "EXPECTED_ABSENT: dict[str, dict[str, str]] = {\n"
                     "    'n1': {'2/3': 'notation: paper writes the d=2 case'},\n"
                     "}\n")
        data = readings.extract_repo(self.root)
        self.assertEqual(len(data["exponents"]["n1"]), 1)
        entry = data["exponents"]["n1"][0]
        self.assertEqual(entry["kind"], "notation")
        self.assertIn("2/3", entry["detail"])
        self.assertIn("paper writes the d=2 case", entry["detail"])

    def test_missing_files_yield_empty_contributions_not_errors(self):
        # No tools/*.py written at all.
        data = readings.extract_repo(self.root)
        self.assertEqual(data, {"clauses": {}, "constants": {}, "exponents": {}})

    def test_extraction_does_not_execute_the_source(self):
        """AST-parse + ast.literal_eval only: a file that would blow up or
        have a side effect if imported/exec'd must still be readable."""
        sentinel = self.root / "sentinel.txt"
        self._write("check_clauses.py",
                    "import pathlib\n"
                    f"pathlib.Path({str(sentinel)!r}).write_text('EXECUTED')\n"
                    "raise RuntimeError('this file must never be executed')\n"
                    "REVIEWED = {'n1': 'a reading'}\n")
        data = readings.extract_repo(self.root)
        self.assertEqual(data["clauses"], {"n1": "a reading"})
        self.assertFalse(sentinel.exists(), "the incumbent file was executed, not just parsed")

    def test_cli_extract_writes_readings_yaml_under_out(self):
        self._write("check_clauses.py", "REVIEWED = {'n1': 'a reading'}\n")
        out_dir = Path(tempfile.mkdtemp(prefix="leanform-extract-out-"))
        try:
            rc = readings.main(["prog", "--extract", str(self.root), "--out", str(out_dir)])
            self.assertEqual(rc, 0)
            written = yaml.safe_load(
                (out_dir / "ledger" / "readings.yaml").read_text(encoding="utf-8")
            )
            self.assertEqual(written["clauses"], {"n1": "a reading"})
        finally:
            shutil.rmtree(out_dir, ignore_errors=True)

    def test_extracts_a_repos_own_noise_vocabulary(self):
        self._write("check_exponents.py", "NOISE = {\"c\", \"M\", \"R\", \"d\"}\n")
        data = readings.extract_repo(self.root)
        self.assertEqual(sorted(data["noise"]), ["M", "R", "c", "d"])


class TestMigrationGuardAgainstForeignKeys(_TempRepoTestCase):
    """Dynamic-Dimensional-Reduction and Exploding-Sandpiles copy-pasted
    rotor-23's tools/ verbatim: `REVIEWED`'s 26 keys are rotor-23 node ids,
    and none is either repo's own. Migrating that verbatim would trade a
    checker that inspected nothing for one that inspects real-looking
    readings that describe a different paper — worse than the original bug,
    because it would look correct. The migration must refuse any key that
    is not a node id of the repo being migrated, and say so.
    """

    def test_refuses_and_reports_keys_that_are_not_this_repos_nodes(self):
        root = self.make_repo(
            [_node("cor-axis-monotonicity", "foo.tex:2-4 (label thm:axis)",
                   "Demo/Frozen/Axis.lean")],
            "preamble\n\\begin{equation}\\label{thm:axis}\n a=b\n\\end{equation}\n",
        )
        tools = root / "tools"
        tools.mkdir()
        (tools / "check_clauses.py").write_text(
            "REVIEWED = {\n"
            "    'lem-least-action': 'a rotor-23 reading, not this repo\\'s',\n"
            "    'lem-boundary-routing': 'another rotor-23 reading',\n"
            "}\n",
            encoding="utf-8",
        )

        rc = readings.main(["prog", "--extract", str(root)])
        self.assertEqual(rc, 0)

        written = yaml.safe_load((root / "ledger" / "readings.yaml").read_text(encoding="utf-8"))
        self.assertEqual(written["clauses"], {}, "the foreign-keyed entries must not be written")

    def test_a_real_own_key_survives_the_guard(self):
        root = self.make_repo(
            [_node("cor-axis-monotonicity", "foo.tex:2-4 (label thm:axis)",
                   "Demo/Frozen/Axis.lean")],
            "preamble\n\\begin{equation}\\label{thm:axis}\n a=b\n\\end{equation}\n",
        )
        tools = root / "tools"
        tools.mkdir()
        (tools / "check_clauses.py").write_text(
            "REVIEWED = {\n"
            "    'cor-axis-monotonicity': 'a real reading against THIS paper',\n"
            "    'lem-least-action': 'a rotor-23 reading, foreign to this repo',\n"
            "}\n",
            encoding="utf-8",
        )

        rc = readings.main(["prog", "--extract", str(root)])
        self.assertEqual(rc, 0)

        written = yaml.safe_load((root / "ledger" / "readings.yaml").read_text(encoding="utf-8"))
        self.assertEqual(
            written["clauses"], {"cor-axis-monotonicity": "a real reading against THIS paper"}
        )


if __name__ == "__main__":
    unittest.main()
