import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import CERW.Support.Occupation.CellSetVolume

/-!
# The first moment of the range and of its cell set

The cell replacement after `eq:quadratic`:
`|Σ_{x ∈ A_n} |x| - ∫_{D_n} |v| dv| ≤ (√d/2) |A_n|`.
Each cell has unit volume, and `||v| - |x|| ≤ |v - x| ≤ √d/2` on `C_x`.
-/

namespace CERW.Support.Contact

open MeasureTheory LatticeProb CERW CERW.Support.Occupation

variable {d : ℕ}

/-- `|Σ_{x ∈ A_n} |x| - ∫_{D_n} |v| dv| ≤ (√d/2) |A_n|`. -/
theorem abs_sum_euclidNorm_sub_integral_le (X : ℕ → Site d) (n : ℕ) :
    |∑ x ∈ departureRange X n, euclidNorm x - ∫ v in cellSet X n, ‖v‖| ≤
      Real.sqrt d / 2 * (departureRange X n).card := by
  have hInt : ∀ x ∈ departureRange X n,
      IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (cell x) := by
    intro x _
    refine IntegrableOn.of_bound (C := ‖toSpace x‖ + Real.sqrt d / 2) ?_ ?_ ?_
    · rw [volume_cell]
      norm_num
    · exact continuous_norm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_cell x)] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
      calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ :=
            norm_le_norm_add_norm_sub' v (toSpace x)
        _ ≤ ‖toSpace x‖ + Real.sqrt d / 2 :=
            add_le_add le_rfl (norm_sub_toSpace_le_of_mem_cell hv)
  have hIntConst : ∀ x ∈ departureRange X n,
      IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => euclidNorm x) (cell x) :=
    fun x _ => integrableOn_const (C := euclidNorm x) (by rw [volume_cell]; norm_num)
  have hconst : ∀ x ∈ departureRange X n,
      ∫ v in cell x, euclidNorm x = euclidNorm x := by
    intro x _
    rw [setIntegral_const, Measure.real_def, volume_cell, ENNReal.toReal_one, one_smul]
  have hsplit : ∫ v in cellSet X n, ‖v‖ =
      ∑ x ∈ departureRange X n, ∫ v in cell x, ‖v‖ := by
    rw [cellSet]
    exact integral_biUnion_finset (departureRange X n) (fun x _ => measurableSet_cell x)
      (fun x _ y _ hxy => cell_disjoint hxy) (fun x hx => hInt x hx)
  rw [hsplit]
  calc |∑ x ∈ departureRange X n, euclidNorm x -
          ∑ x ∈ departureRange X n, ∫ v in cell x, ‖v‖|
      = |∑ x ∈ departureRange X n, ∫ v in cell x, (euclidNorm x - ‖v‖)| := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        conv_lhs => rw [← hconst x hx]
        rw [← integral_sub (hIntConst x hx) (hInt x hx)]
    _ ≤ ∑ x ∈ departureRange X n, |∫ v in cell x, (euclidNorm x - ‖v‖)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ departureRange X n, Real.sqrt d / 2 := by
        apply Finset.sum_le_sum
        intro x hx
        have hpt : ∀ v ∈ cell x, ‖(euclidNorm x - ‖v‖ : ℝ)‖ ≤ Real.sqrt d / 2 := by
          intro v hv
          rw [Real.norm_eq_abs, ← norm_toSpace x]
          calc |‖toSpace x‖ - ‖v‖| ≤ ‖toSpace x - v‖ := abs_norm_sub_norm_le _ _
            _ = ‖v - toSpace x‖ := norm_sub_rev _ _
            _ ≤ Real.sqrt d / 2 := norm_sub_toSpace_le_of_mem_cell hv
        calc |∫ v in cell x, (euclidNorm x - ‖v‖)|
            = ‖∫ v in cell x, (euclidNorm x - ‖v‖)‖ := (Real.norm_eq_abs _).symm
          _ ≤ Real.sqrt d / 2 * volume.real (cell x) :=
              norm_setIntegral_le_of_norm_le_const (by rw [volume_cell]; norm_num) hpt
          _ = Real.sqrt d / 2 := by
              rw [Measure.real_def, volume_cell, ENNReal.toReal_one, mul_one]
    _ = Real.sqrt d / 2 * (departureRange X n).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end CERW.Support.Contact
