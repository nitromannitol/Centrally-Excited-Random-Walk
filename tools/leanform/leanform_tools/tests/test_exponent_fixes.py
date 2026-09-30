"""Regressions for defects found running the ported checkers against the fleet.

Each test here corresponds to a false failure the shared package produced on
2026-09-23 against a repo whose incumbent checker passed. A port that is
stricter than the tool it replaces is only useful if the extra strictness is
real; these pin the cases where it was not.
"""

import unittest

from leanform_tools.check_exponents import _missing, canon, paper_exponents
from leanform_tools.readings import drop_foreign_keys


class TestCanon(unittest.TestCase):
    def test_frac_normalizes_to_slash(self):
        """ORRW: paper `\\frac{d}{d+1}` vs Lean `d/(d+1)` are one exponent."""
        self.assertEqual(canon(r"\frac{d}{d+1}"), "d/(d+1)")

    def test_negated_frac(self):
        self.assertEqual(canon(r"-\frac{d}{d+1}"), "-d/(d+1)")

    def test_frac_with_simple_denominator_is_not_parenthesized(self):
        self.assertEqual(canon(r"\frac{1}{2}"), "1/2")

    def test_type_ascription_stripped_for_any_type(self):
        """rotor-23 `prop-circuit-clock`: `(3 : ℕ)` must equal the paper's `3`."""
        self.assertEqual(canon("(3 : ℕ)"), "3")
        self.assertEqual(canon("(2 / 3 : ℝ)"), "2/3")

    def test_sign_critical_parenthesis_is_preserved(self):
        """-(2-d/2) and -2-d/2 are different numbers; the paren must stay."""
        self.assertEqual(canon("-(2-d/2)"), "-(2-d/2)")

    def test_redundant_parenthesis_is_dropped(self):
        self.assertEqual(canon("-(x)"), "-x")


class TestMultiplicityIsANoteNotAFailure(unittest.TestCase):
    """rotor-23: `|R_t| = c t^{2/3} + o(t^{2/3})` names 2/3 twice; Lean once."""

    def test_fewer_occurrences_is_not_a_failure(self):
        from collections import Counter

        absent, fewer = _missing(Counter({"2/3": 2}), Counter({"2/3": 1}))
        self.assertEqual(absent, [])
        self.assertEqual(len(fewer), 1)
        self.assertIn("paper 2x, Lean 1x", fewer[0])

    def test_an_exponent_absent_entirely_is_still_a_failure(self):
        from collections import Counter

        absent, fewer = _missing(Counter({"1/3": 1}), Counter({"2/3": 1}))
        self.assertEqual(absent, ["1/3"])
        self.assertEqual(fewer, [])

    def test_the_transposition_this_gate_exists_for_is_caught(self):
        from collections import Counter

        absent, _ = _missing(Counter({"2/3": 1}), Counter({"1/3": 1}))
        self.assertEqual(absent, ["2/3"])


class TestPerRepoNoise(unittest.TestCase):
    """ORRW's `c`, `M`, `R` are named constants, not exponents."""

    def test_bare_symbol_is_an_exponent_by_default(self):
        counts, _ = paper_exponents("$x^c$")
        self.assertEqual(counts.get("c"), 1)

    def test_per_repo_noise_suppresses_it(self):
        counts, _ = paper_exponents("$x^c$", {"c"})
        self.assertNotIn("c", counts)

    def test_per_repo_noise_does_not_suppress_a_real_exponent(self):
        counts, _ = paper_exponents("$x^{2/3}$", {"c", "M", "R"})
        self.assertEqual(counts.get("2/3"), 1)


class TestForeignKeyGuard(unittest.TestCase):
    """The migration trap: DimRed/Exploding's REVIEWED dict is rotor-23's."""

    def test_foreign_keys_are_dropped_and_counted(self):
        data = {
            "clauses": {"mine": "ok", "lem-least-action": "rotor's"},
            "constants": {"prop-path-reduction": "rotor's"},
            "exponents": {},
        }
        cleaned, refused = drop_foreign_keys(data, {"mine"})
        self.assertEqual(cleaned["clauses"], {"mine": "ok"})
        self.assertEqual(cleaned["constants"], {})
        self.assertEqual(refused, {"clauses": 1, "constants": 1})

    def test_a_clean_migration_refuses_nothing(self):
        data = {"clauses": {"a": "x"}, "constants": {}, "exponents": {}}
        cleaned, refused = drop_foreign_keys(data, {"a"})
        self.assertEqual(refused, {})
        self.assertEqual(cleaned["clauses"], {"a": "x"})


if __name__ == "__main__":
    unittest.main()
