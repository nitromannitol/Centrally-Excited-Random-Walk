import CERW.Model

/-!
# Drift crossing

Let `Z_t = X_t + ε ∑_{j < t} I_j ξ(X_j)`, where `I_j` marks a first departure. If the
increments of `Z` are bounded by `C √((t - s) log n)` and every drift vector `ξ(X_j)` at a
first departure in `[s, t)` has nonnegative projection onto a unit vector `u`, then the
projection `u · (X_t - X_s)` of the underlying increment obeys the same bound.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

theorem drift_crossing {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ) (C : ℝ) :
    let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => CERW.toSpace (x t) + ε •
      ∑ j ∈ Finset.range t, if x j ∉ CERW.departureRange x j then ξ (x j) else 0
    (∀ s t : ℕ, s < t → t ≤ n → ‖Z t - Z s‖ ≤ C * Real.sqrt ((t - s : ℝ) * Real.log n)) →
    ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ s t : ℕ, s < t → t ≤ n →
      (∀ j : ℕ, s ≤ j → j < t → x j ∉ CERW.departureRange x j → 0 ≤ inner ℝ u (ξ (x j))) →
      inner ℝ u (CERW.toSpace (x t) - CERW.toSpace (x s))
        ≤ C * Real.sqrt ((t - s : ℝ) * Real.log n) := by
  intro Z hZ u hu s t hst htn hxi
  let f : ℕ → EuclideanSpace ℝ (Fin d) := fun j =>
    if x j ∉ CERW.departureRange x j then ξ (x j) else 0
  let T : EuclideanSpace ℝ (Fin d) := ∑ j ∈ Finset.Ico s t, f j
  have hsum : ∑ j ∈ Finset.range t, f j
      = ∑ j ∈ Finset.range s, f j + ∑ j ∈ Finset.Ico s t, f j :=
    (Finset.sum_range_add_sum_Ico f (le_of_lt hst)).symm
  have hZeq : Z t - Z s
      = (CERW.toSpace (x t) - CERW.toSpace (x s)) + ε • T := by
    simp only [Z, T, f, hsum, smul_add]
    abel
  have hT_nonneg : 0 ≤ inner ℝ u T := by
    simp only [T, f, inner_sum]
    refine Finset.sum_nonneg fun j hj => ?_
    by_cases hdep : x j ∉ CERW.departureRange x j
    · rw [if_pos hdep]
      exact hxi j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2 hdep
    · rw [if_neg hdep, inner_zero_right]
  have hinner : inner ℝ u (Z t - Z s)
      = inner ℝ u (CERW.toSpace (x t) - CERW.toSpace (x s)) + ε * inner ℝ u T := by
    rw [hZeq, inner_add_right, inner_smul_right]
  have hAle : inner ℝ u (CERW.toSpace (x t) - CERW.toSpace (x s))
      ≤ inner ℝ u (Z t - Z s) := by
    rw [hinner]
    have hεT : 0 ≤ ε * inner ℝ u T := mul_nonneg hε hT_nonneg
    linarith
  calc
    inner ℝ u (CERW.toSpace (x t) - CERW.toSpace (x s))
        ≤ inner ℝ u (Z t - Z s) := hAle
    _ ≤ ‖u‖ * ‖Z t - Z s‖ := real_inner_le_norm u (Z t - Z s)
    _ = ‖Z t - Z s‖ := by rw [hu, one_mul]
    _ ≤ C * Real.sqrt ((t - s : ℝ) * Real.log n) := hZ s t hst htn

end CERW.Support.Norm
