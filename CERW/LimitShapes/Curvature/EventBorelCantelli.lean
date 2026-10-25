module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

@[expose] public section

/-!
# Polynomial exceptional probabilities and eventual conclusions

The first Borel--Cantelli lemma gives the eventual assertion in Theorem `thm:fluctuations`.
-/

universe u

open MeasureTheory Filter
open scoped ENNReal

namespace CERW.LimitShapes.Curvature

/-- Summable polynomial bounds from time two imply an almost sure eventual predicate. -/
theorem ae_eventually_of_polynomial_bound {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : ℕ → Ω → Prop) {C p : ℝ} (hp : 1 < p)
    (h : ∀ n : ℕ, 2 ≤ n → μ {ω | ¬ P n ω} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, P n ω := by
  let s : ℕ → Set Ω := fun n => if 2 ≤ n then {ω | ¬ P n ω} else ∅
  have hs : ∀ n, μ (s n) ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
    intro n
    dsimp only [s]
    split_ifs with hn
    · exact h n hn
    · simp only [measure_empty, zero_le]
  have hsum : Summable (fun n : ℕ => C * (n : ℝ) ^ (-p)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -p < -1)).mul_left C
  have hfinite : (∑' n, μ (s n)) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hs) hsum.tsum_ofReal_lt_top).ne
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω, eventually_ge_atTop 2] with n hn hn2
  simpa only [s, if_pos hn2, Set.mem_setOf_eq, not_not] using hn

end CERW.LimitShapes.Curvature
