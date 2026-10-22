"""Regressions for manifest status claims and exact natural-language proof records."""

from __future__ import annotations

import hashlib
import importlib.util
import sys
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "leanform"))

from leanform_tools.config import Node  # noqa: E402
from leanform_tools.gate import Result  # noqa: E402

SPEC = importlib.util.spec_from_file_location("verify_oct13_current_source",
                                             ROOT / "tools" / "verify_oct13.py")
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)


def final_config():
    """Load the actual pinned source and manifest without filling missing entries."""
    path = ROOT / "ledger" / "oct13.yaml"
    raw = yaml.safe_load(path.read_text())
    nodes = [Node(dict(node)) for node in raw["nodes"]]
    return VERIFY.PaperConfig(ROOT, path, raw, nodes)


class CurrentSourceStatusTests(unittest.TestCase):
    def setUp(self):
        self.cfg = final_config()

    def partial(self, cfg):
        text = VERIFY.status_text(cfg)
        self.assertNotIn("**All ", text)
        self.assertIn("manifest declarations:", text)
        return text

    def test_actual_final29_preserves_exact_complete_status(self):
        self.assertEqual(len(self.cfg.nodes), 29)
        self.assertIn("lem-separated-brackets-common-event", {node.id for node in self.cfg.nodes})
        self.assertEqual(VERIFY.status_text(self.cfg),
                         "**All 22 labeled results are proved in 29 checked declarations.** "
                         "The literal Section 5.1 event has polynomial exceptional probability, "
                         "and both contact and separated brackets use its produced "
                         "uniform constants.")

    def test_all_draft_ids_do_not_prove_any_source_label(self):
        nodes = [Node({**node.raw, "state": "DRAFT_SORRY"}) for node in self.cfg.nodes]
        text = self.partial(replace(self.cfg, nodes=nodes))
        self.assertIn("0 sealed/proved, 29 draft", text)
        self.assertIn("0/22 source result blocks", text)
        self.assertIn("Source consumers: 0/2", text)

    def test_only_two_sealed_consumers_do_not_cover_the_paper(self):
        nodes = [node for node in self.cfg.nodes if node.id in VERIFY.SOURCE_CONSUMERS]
        text = self.partial(replace(self.cfg, nodes=nodes))
        self.assertIn("2/22 source result blocks", text)
        self.assertIn("Source consumers: 2/2", text)
        self.assertIn("Probability producers: 0/2", text)

    def test_each_probability_producer_is_required(self):
        for ident in VERIFY.PROBABILITY_PRODUCERS:
            with self.subTest(producer=ident):
                nodes = [node for node in self.cfg.nodes if node.id != ident]
                text = self.partial(replace(self.cfg, nodes=nodes))
                self.assertIn("Probability producers: 1/2", text)

    def test_conditional_consumer_does_not_count_as_completed(self):
        nodes = [Node({**node.raw, "state": "CONDITIONAL"})
                 if node.id == "lem-contact-common-event" else node for node in self.cfg.nodes]
        text = self.partial(replace(self.cfg, nodes=nodes))
        self.assertIn("28 sealed/proved, 0 draft, 1 conditional", text)
        self.assertIn("Source consumers: 1/2", text)

    def test_draft_part_of_split_sharpness_block_prevents_complete_claim(self):
        nodes = [Node({**node.raw, "state": "DRAFT_SORRY"})
                 if node.id == "oct13-thm-sharp-bulk" else node for node in self.cfg.nodes]
        text = self.partial(replace(self.cfg, nodes=nodes))
        # Other sharpness parts still claim this label, but do not prove part (iii).
        self.assertIn("22/22 source result blocks", text)
        self.assertIn("28 sealed/proved, 1 draft", text)

    def test_deleted_sharpness_part_leaves_unowned_frozen_file(self):
        for ident in ["oct13-thm-sharp-radii", "oct13-thm-sharp-radii-lil",
                      "oct13-thm-sharp-bulk", "oct13-thm-sharp-width"]:
            with self.subTest(part=ident):
                deleted = next(node for node in self.cfg.nodes if node.id == ident)
                self.assertTrue((self.cfg.root / deleted.file).is_file())
                nodes = [node for node in self.cfg.nodes if node.id != ident]
                text = self.partial(replace(self.cfg, nodes=nodes))
                self.assertIn("22/22 source result blocks", text)
                self.assertIn("1 frozen files lack a unique sealed/proved owner", text)

    def test_missing_source_closure_remains_missing(self):
        nodes = [node for node in self.cfg.nodes
                 if node.id != "lem-separated-brackets-common-event"]
        self.assertIn("Source consumers: 1/2", self.partial(replace(self.cfg, nodes=nodes)))

    def test_complete_ids_with_wrong_source_claims_do_not_cover_labels(self):
        nodes = [Node({**node.raw, "source": "oct13.tex:1-1 (label unrelated)"})
                 for node in self.cfg.nodes]
        self.assertIn("0/22 source result blocks", self.partial(replace(self.cfg, nodes=nodes)))

    def test_required_ids_with_wrong_exports_do_not_count_as_producers(self):
        nodes = [Node({**node.raw, "export": "Demo.unrelated"})
                 if node.id in VERIFY.PROBABILITY_PRODUCERS else node for node in self.cfg.nodes]
        self.assertIn("Probability producers: 0/2", self.partial(replace(self.cfg, nodes=nodes)))

    def test_required_ids_with_definition_kind_are_not_probability_theorems(self):
        nodes = [Node({**node.raw, "kind": "definition"})
                 if node.id in VERIFY.PROBABILITY_PRODUCERS else node for node in self.cfg.nodes]
        self.assertIn("Probability producers: 0/2", self.partial(replace(self.cfg, nodes=nodes)))

    def test_empty_manifest_does_not_pass(self):
        self.assertIn("0 sealed/proved", self.partial(replace(self.cfg, nodes=[])))

    def test_unverified_pin_does_not_pass(self):
        raw = {**self.cfg.raw, "source_pin": {**self.cfg.raw["source_pin"], "sha256": "wrong"}}
        self.assertIn("Source pin is unverified", self.partial(replace(self.cfg, raw=raw)))

    def test_proved_state_is_accepted(self):
        nodes = [Node({**node.raw, "state": "PROVED"}) for node in self.cfg.nodes]
        self.assertEqual(VERIFY.status_text(replace(self.cfg, nodes=nodes)),
                         VERIFY.status_text(self.cfg))

    def test_shared_parser_honors_comments_aliases_and_unlabeled_results(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paper = "% \\begin{lemma}\\label{ignored}x\\end{lemma}\n"
            paper += "\\begin{prop}\\label{extra}Extra.\\end{prop}\n"
            paper += "\\begin{lemma}Unlabeled.\\end{lemma}\n"
            (root / "paper.tex").write_text(paper)
            raw = {"source_pin": {"file": "paper.tex",
                                  "sha256": hashlib.sha256(paper.encode()).hexdigest()}}
            cfg = replace(self.cfg, root=root, raw=raw)
            self.assertIn("0/2 source result blocks", self.partial(cfg))

    def test_empty_pinned_paper_cannot_pass_vacuously(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "paper.tex").write_text("")
            raw = {"source_pin": {"file": "paper.tex",
                                  "sha256": hashlib.sha256(b"").hexdigest()}}
            self.assertIn("No source result blocks", self.partial(
                replace(self.cfg, root=root, raw=raw)))


class NaturalLanguageProofTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "ledger" / "nl").mkdir(parents=True)
        self.source = "\\begin{lemma}\\label{demo}True.\\end{lemma}"
        self.statement = "theorem Demo.result : True"
        (self.root / "paper.tex").write_text(self.source + "\n")
        (self.root / "anchor.lean").write_text(
            "-- FROZEN-STATEMENT-BEGIN\n" + self.statement + "\n"
            "-- FROZEN-STATEMENT-END\n:= by trivial\n")
        raw = {"source_pin": {"file": "paper.tex"}}
        node = Node({"id": "demo", "source": "paper.tex:1-1 (label demo)",
                     "file": "anchor.lean", "state": "SEALED"})
        self.cfg = VERIFY.PaperConfig(self.root, self.root / "manifest.yaml", raw, [node])

    def check_proof(self, proof, source=None, statement=None):
        text = ("\\paragraph{Paper excerpt.}\n\\begin{verbatim}\n"
                + (self.source if source is None else source) + "\n\\end{verbatim}\n"
                "\\paragraph{Lean statement.}\n\\begin{verbatim}\n"
                + (self.statement if statement is None else statement) + "\n\\end{verbatim}\n"
                "\\paragraph{Proof of the registered statement.}\n" + proof
                + "\n\\paragraph{Lean status.}\nSealed.\n")
        (self.root / "ledger" / "nl" / "demo.tex").write_text(text)
        result = Result("nl_twins")
        VERIFY.check_nl_twins(result, self.cfg)
        self.assertEqual(result.processed, 1)
        return result.failures

    def test_substantive_proof_preserves_exact_twins(self):
        self.assertEqual(self.check_proof("Apply the proved truth constructor."), [])

    def test_empty_and_comment_only_proofs_cannot_borrow_status_text(self):
        for proof in ["", "  \n  ", "% Proof will follow.\n"]:
            with self.subTest(proof=proof):
                self.assertIn("demo: empty proof record", self.check_proof(proof))

    def test_sketch_marker_fails_even_with_nonempty_prose(self):
        for proof in ["SKETCH: apply a future estimate.", "Use the bound. \\textbf{SKETCH}",
                      "% SKETCH\nApply an estimate later."]:
            with self.subTest(proof=proof):
                self.assertIn("demo: SKETCH proof record", self.check_proof(proof))

    def test_exact_source_and_statement_checks_still_reject_drift(self):
        self.assertIn("demo: stale paper excerpt", self.check_proof("A proof.", source="wrong"))
        self.assertIn("demo: stale Lean statement", self.check_proof("A proof.", statement="wrong"))


if __name__ == "__main__":
    unittest.main()
