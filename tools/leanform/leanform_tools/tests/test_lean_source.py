"""Tests for the source reader.

Two of these guard relaxations made on 2026-09-23 after a first run produced
226 spurious failures in Manhattan-Transience and 208 in GMC. A relaxed check
has to be proven still to catch the thing it bans.
"""

import unittest

from leanform_tools import lean_source as ls


class TestCommentMasking(unittest.TestCase):
    def test_prose_beginning_with_theorem_is_not_a_declaration(self):
        """The documented failure: a header comment read as a declaration."""
        src = (
            "/- The\n"
            "theorem below is the paper's Theorem 1.1.\n"
            "-/\n"
            "theorem real_one : True := trivial\n"
        )
        self.assertEqual(ls.declarations(src), ["real_one"])

    def test_nested_block_comments(self):
        src = "/- outer /- inner def hidden -/ still outer def also_hidden -/\ndef visible : Nat := 0\n"
        self.assertEqual(ls.declarations(src), ["visible"])

    def test_masking_preserves_offsets_and_line_numbers(self):
        src = "-- comment\ndef a : Nat := 0\n"
        masked = ls.mask_comments(src)
        self.assertEqual(len(masked), len(src))
        self.assertEqual(masked.count("\n"), src.count("\n"))

    def test_line_comment_does_not_start_a_block(self):
        src = "--- not /- a block\ndef a : Nat := 0\n"
        self.assertEqual(ls.declarations(src), ["a"])


class TestAxiomBan(unittest.TestCase):
    def test_print_axioms_is_legal(self):
        """Every Certificate.lean asks Lean for a closure this way."""
        src = "#print axioms Rotor.Frozen.main\n#print axioms Foo.bar\n"
        self.assertEqual(ls.axiom_declarations(src), [])
        self.assertEqual(ls.token_hits(src, ("admit", "sorryAx")), [])

    def test_a_real_axiom_declaration_is_caught(self):
        src = "theorem a : True := trivial\naxiom extraAxiom : False\n"
        self.assertEqual(ls.axiom_declarations(src), [2])

    def test_an_indented_axiom_declaration_is_caught(self):
        src = "section\n  axiom sneaky : False\nend\n"
        self.assertEqual(ls.axiom_declarations(src), [2])

    def test_an_axiom_inside_a_comment_is_not_caught(self):
        src = "/- axiom foo : False -/\ndef a : Nat := 0\n"
        self.assertEqual(ls.axiom_declarations(src), [])

    def test_the_word_axioms_alone_is_not_a_declaration(self):
        src = "-- the axioms of the theory\ndef axiomatic : Nat := 0\n"
        self.assertEqual(ls.axiom_declarations(src), [])


class TestTokenBoundaries(unittest.TestCase):
    def test_native_decide_is_caught(self):
        src = "theorem a : True := by native_decide\n"
        self.assertEqual([t for t, _ in ls.token_hits(src, ("native_decide",))],
                         ["native_decide"])

    def test_admit_is_caught_but_not_as_a_substring(self):
        src = "def admitted : Nat := 0\ntheorem b : True := by admit\n"
        hits = ls.token_hits(src, ("admit",))
        self.assertEqual([line for _, line in hits], [2])


class TestFrozenBlocks(unittest.TestCase):
    SRC = (
        "import Mathlib\n"
        "-- FROZEN-STATEMENT-BEGIN\n"
        "theorem main : True :=\n"
        "-- FROZEN-STATEMENT-END\n"
        "  by trivial\n"
    )

    def test_one_block_found(self):
        self.assertEqual(len(ls.frozen_blocks(self.SRC)), 1)

    def test_hashed_body_drops_one_leading_newline_and_keeps_the_trailing_one(self):
        span = ls.frozen_blocks(self.SRC)[0]
        self.assertEqual(ls.block_body(self.SRC, span), "theorem main : True :=\n")

    def test_unterminated_block_is_reported(self):
        span = ls.frozen_blocks("-- FROZEN-STATEMENT-BEGIN\ntheorem a : True :=\n")[0]
        self.assertEqual(span[1], -1)

    def test_two_blocks_found(self):
        self.assertEqual(len(ls.frozen_blocks(self.SRC + self.SRC)), 2)


class TestTruncation(unittest.TestCase):
    def test_ascii_truncation_of_a_subscripted_name_is_flagged(self):
        """Manhattan's copy matched `e` against `e₁`."""
        self.assertTrue(ls.is_truncation("e", "e₁"))

    def test_an_exact_name_is_not_a_truncation(self):
        self.assertFalse(ls.is_truncation("e₁", "e₁"))

    def test_an_unrelated_name_is_not_a_truncation(self):
        self.assertFalse(ls.is_truncation("foo", "bar"))


if __name__ == "__main__":
    unittest.main()
