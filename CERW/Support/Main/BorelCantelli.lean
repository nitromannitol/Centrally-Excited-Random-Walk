import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.PSeries

/-!
# From polynomially small failure probabilities to almost sure eventual validity

If for all `n ≥ n₀` the event `P n` fails with outer probability at most `C n^{-p}`, with `p > 1`,
then almost surely `P n` holds for all large `n`. The failure probabilities are summable, and the
Borel–Cantelli lemma applies. This turns the probability bound of `thm:fluctuations` into its
almost-sure conjunct.
-/

namespace CERW.Support.Main

open MeasureTheory Filter

/-- Borel–Cantelli for polynomially small failure probabilities: if `μ {¬ P n} ≤ C n^{-p}` for all
`n ≥ n₀` with `p > 1`, then `∀ᵐ ω, ∀ᶠ n, P n ω`. -/
theorem ae_eventually_of_le_rpow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {P : ℕ → Ω → Prop} {C p : ℝ} (hp : 1 < p) {n₀ : ℕ}
    (h : ∀ n, n₀ ≤ n → μ {ω | ¬ P n ω} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, P n ω := by
  classical
  set s : ℕ → Set Ω := fun n => if n₀ ≤ n then {ω | ¬ P n ω} else ∅ with hs
  have hf_nonneg : ∀ n : ℕ, 0 ≤ max C 0 * ((n : ℝ) ^ p)⁻¹ := by
    intro n
    exact mul_nonneg (le_max_right C 0)
      (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) p))
  have hf_summable : Summable (fun n : ℕ => max C 0 * ((n : ℝ) ^ p)⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr hp).mul_left (max C 0)
  have hbound : ∀ n : ℕ, μ (s n) ≤ ENNReal.ofReal (max C 0 * ((n : ℝ) ^ p)⁻¹) := by
    intro n
    by_cases hn : n₀ ≤ n
    · simp only [hs, hn, ite_true]
      calc μ {ω | ¬ P n ω} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := h n hn
        _ = ENNReal.ofReal (C * ((n : ℝ) ^ p)⁻¹) := by
              rw [Real.rpow_neg (Nat.cast_nonneg n) p]
        _ ≤ ENNReal.ofReal (max C 0 * ((n : ℝ) ^ p)⁻¹) :=
              ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (le_max_left C 0)
                  (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) p)))
    · simp only [hs, hn, ite_false, measure_empty]
      positivity
  have hfin : (∑' n, μ (s n)) ≠ ⊤ := by
    have hle : (∑' n : ℕ, μ (s n)) ≤
        ENNReal.ofReal (∑' n : ℕ, max C 0 * ((n : ℝ) ^ p)⁻¹) := by
      calc (∑' n : ℕ, μ (s n)) ≤
              ∑' n : ℕ, ENNReal.ofReal (max C 0 * ((n : ℝ) ^ p)⁻¹) :=
            ENNReal.tsum_le_tsum hbound
        _ = ENNReal.ofReal (∑' n : ℕ, max C 0 * ((n : ℝ) ^ p)⁻¹) :=
            (ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf_summable).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ s n := ae_eventually_notMem hfin
  filter_upwards [hae] with ω hω
  filter_upwards [hω, Filter.eventually_ge_atTop n₀] with n hnc hn
  by_contra hPn
  exact hnc (by simp only [hs, hn, ite_true, Set.mem_setOf_eq]; exact hPn)

end CERW.Support.Main
