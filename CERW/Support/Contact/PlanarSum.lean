import CERW.Generic.Lattice.Packing
import CERW.Generic.Lattice.SummableSums
import CERW.Support.Occupation.Facts

/-!
# The planar contact sum

In the plane, the bracket at the unvisited contact site `z` is controlled by
`Σ_{|x - z| ≤ R} (b - |x|)_+ (1 + |x - z|)^{-2}`. Since `|z| ≥ b`, each weight `(b - |x|)_+` is
at most `|x - z|`, and `Σ_{|w| ≤ R} |w| (1 + |w|)^{-2}` grows linearly in `R`. This is the
bound `B_z ≤ CN` of the planar contact variance.
-/

namespace CERW.Support.Contact

open LatticeProb

variable {d : ℕ}

/-- If `b ≤ |z|` then `(b - |x|)_+ ≤ |x - z|`. -/
theorem max_sub_euclidNorm_le {x z : Site d} {b : ℝ} (hz : b ≤ euclidNorm z) :
    max (b - euclidNorm x) 0 ≤ euclidNorm (x - z) := by
  have hsub : euclidNorm z - euclidNorm x ≤ euclidNorm (x - z) := by
    have h := CERW.Support.Occupation.euclidNorm_add_le x (z - x)
    rw [show x + (z - x) = z by abel] at h
    rw [show z - x = -(x - z) by abel, CERW.Generic.Lattice.euclidNorm_neg] at h
    linarith
  exact max_le (by linarith) (euclidNorm_nonneg _)

/-- In the plane, `Σ_{|w| ≤ R} |w| (1 + |w|)^{-2} ≤ C (R + 1)`. -/
theorem sum_ballFinset_norm_mul_rpow_le_two :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      ∑ w ∈ ballFinset 2 R, euclidNorm w * (1 + euclidNorm w) ^ (-2 : ℝ) ≤ C * (R + 1) := by
  obtain ⟨C, hCpos, hC⟩ :=
    CERW.Generic.Lattice.sum_ballFinset_rpow_one_sub_le (d := 2) (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro R hR
  calc ∑ w ∈ ballFinset 2 R, euclidNorm w * (1 + euclidNorm w) ^ (-2 : ℝ)
      ≤ ∑ w ∈ ballFinset 2 R, (1 + euclidNorm w) ^ (-1 : ℝ) := by
        refine Finset.sum_le_sum fun w _ => ?_
        have hbase : 0 < 1 + euclidNorm w := by linarith [euclidNorm_nonneg w]
        have hnorm : euclidNorm w ≤ 1 + euclidNorm w := by linarith [euclidNorm_nonneg w]
        have hnonneg : 0 ≤ (1 + euclidNorm w) ^ (-2 : ℝ) :=
          Real.rpow_nonneg (le_of_lt hbase) _
        calc euclidNorm w * (1 + euclidNorm w) ^ (-2 : ℝ)
            ≤ (1 + euclidNorm w) * (1 + euclidNorm w) ^ (-2 : ℝ) :=
              mul_le_mul_of_nonneg_right hnorm hnonneg
          _ = (1 + euclidNorm w) ^ (1 : ℝ) * (1 + euclidNorm w) ^ (-2 : ℝ) := by
              rw [Real.rpow_one]
          _ = (1 + euclidNorm w) ^ ((1 : ℝ) + -2) := (Real.rpow_add hbase 1 (-2)).symm
          _ = (1 + euclidNorm w) ^ (-1 : ℝ) := by
              rw [show (1 : ℝ) + -2 = -1 by norm_num]
    _ = ∑ w ∈ ballFinset 2 R, (1 + euclidNorm w) ^ (1 - (2 : ℝ)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [show (1 : ℝ) - 2 = -1 by norm_num]
    _ ≤ C * (R + 1) := hC R hR

/-- The planar contact sum: for `b ≤ |z|` and `R ≥ 0`,
`Σ_{|w| ≤ R} (b - |z + w|)_+ (1 + |w|)^{-2} ≤ C (R + 1)`. -/
theorem sum_max_sub_mul_rpow_le_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Site 2) (b R : ℝ), b ≤ euclidNorm z → 0 ≤ R →
      ∑ w ∈ ballFinset 2 R, max (b - euclidNorm (z + w)) 0 * (1 + euclidNorm w) ^ (-2 : ℝ)
        ≤ C * (R + 1) := by
  obtain ⟨C, hCpos, hC⟩ := sum_ballFinset_norm_mul_rpow_le_two
  refine ⟨C, hCpos, ?_⟩
  intro z b R hz hR
  calc ∑ w ∈ ballFinset 2 R, max (b - euclidNorm (z + w)) 0
          * (1 + euclidNorm w) ^ (-2 : ℝ)
      ≤ ∑ w ∈ ballFinset 2 R, euclidNorm w * (1 + euclidNorm w) ^ (-2 : ℝ) := by
        refine Finset.sum_le_sum fun w _ => ?_
        have h1 : max (b - euclidNorm (z + w)) 0 ≤ euclidNorm w := by
          have h := max_sub_euclidNorm_le (x := z + w) (z := z) hz
          simpa only [add_sub_cancel_left] using h
        have h2 : 0 ≤ (1 + euclidNorm w) ^ (-2 : ℝ) :=
          Real.rpow_nonneg (by linarith [euclidNorm_nonneg w]) _
        exact mul_le_mul_of_nonneg_right h1 h2
    _ ≤ C * (R + 1) := hC R hR

end CERW.Support.Contact
