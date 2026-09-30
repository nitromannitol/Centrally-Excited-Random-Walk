import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The weight of a cell far from the origin

For a site with `|x| ≥ √d`, every point of its cell has norm between `|x|/2` and `2|x|`. So the
weight `|v|^{1-d}` on the cell is comparable to `|x|^{1-d}`, and since the cell has volume one so
is its integral. This comparison converts sums over departure sites into the tail `F` in
`lem:radial` and in the cell counts of `prop:coarse` and the outer bound.
-/

namespace CERW.Support.Occupation

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- If `|x| ≥ √d` and `v ∈ C_x`, then `|x|/2 ≤ |v| ≤ 2|x|`. -/
theorem norm_mem_Icc_of_mem_cell {x : Site d} (hx : Real.sqrt d ≤ euclidNorm x)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cell x) :
    euclidNorm x / 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * euclidNorm x := by
  have hsub : ‖v - toSpace x‖ ≤ euclidNorm x / 2 := by
    calc ‖v - toSpace x‖ ≤ Real.sqrt d / 2 := norm_sub_toSpace_le_of_mem_cell hv
      _ ≤ euclidNorm x / 2 := by linarith
  constructor
  · have h : ‖toSpace x‖ ≤ ‖v‖ + ‖v - toSpace x‖ := by
      have h' := norm_le_norm_add_norm_sub' (toSpace x) v
      rwa [show toSpace x - v = -(v - toSpace x) by rw [neg_sub], norm_neg] at h'
    rw [norm_toSpace] at h
    linarith
  · have h : ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ :=
      norm_le_norm_add_norm_sub' v (toSpace x)
    rw [norm_toSpace] at h
    linarith [euclidNorm_nonneg x]

/-- If `|x| ≥ √d`, `d ≥ 1` and `v ∈ C_x`, then
`2^{1-d} |x|^{1-d} ≤ |v|^{1-d} ≤ 2^{d-1} |x|^{1-d}`. -/
theorem rpow_mem_Icc_of_mem_cell (hd : 1 ≤ d) {x : Site d} (hx : Real.sqrt d ≤ euclidNorm x)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cell x) :
    (2 : ℝ) ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ)) ≤ ‖v‖ ^ (1 - (d : ℝ)) ∧
      ‖v‖ ^ (1 - (d : ℝ)) ≤ (2 : ℝ) ^ ((d : ℝ) - 1) * euclidNorm x ^ (1 - (d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hxpos : 0 < euclidNorm x := lt_of_lt_of_le (Real.sqrt_pos.mpr hdR) hx
  have hmem := norm_mem_Icc_of_mem_cell hx hv
  have hvpos : 0 < ‖v‖ := by linarith [hmem.1, hxpos]
  have he : (1 : ℝ) - (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hmul2 : (2 * euclidNorm x) ^ (1 - (d : ℝ)) =
      2 ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ)) :=
    Real.mul_rpow (by norm_num) (euclidNorm_nonneg x)
  have hdiv2 : (euclidNorm x / 2) ^ (1 - (d : ℝ)) =
      (2 : ℝ) ^ ((d : ℝ) - 1) * euclidNorm x ^ (1 - (d : ℝ)) := by
    calc (euclidNorm x / 2) ^ (1 - (d : ℝ))
        = euclidNorm x ^ (1 - (d : ℝ)) / 2 ^ (1 - (d : ℝ)) :=
          Real.div_rpow (euclidNorm_nonneg x) (by norm_num) _
      _ = euclidNorm x ^ (1 - (d : ℝ)) * (2 ^ (1 - (d : ℝ)))⁻¹ := by rw [div_eq_mul_inv]
      _ = euclidNorm x ^ (1 - (d : ℝ)) * 2 ^ (-(1 - (d : ℝ))) := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = euclidNorm x ^ (1 - (d : ℝ)) * 2 ^ ((d : ℝ) - 1) := by
          rw [show -(1 - (d : ℝ)) = (d : ℝ) - 1 by ring]
      _ = (2 : ℝ) ^ ((d : ℝ) - 1) * euclidNorm x ^ (1 - (d : ℝ)) := by ring
  constructor
  · have h := Real.rpow_le_rpow_of_nonpos hvpos hmem.2 he
    rwa [hmul2] at h
  · have h := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < euclidNorm x / 2) hmem.1 he
    rwa [hdiv2] at h

/-- If `|x| ≥ √d` and `d ≥ 1`, the cell integral of `|v|^{1-d}` lies between
`2^{1-d} |x|^{1-d}` and `2^{d-1} |x|^{1-d}`. -/
theorem setIntegral_rpow_mem_Icc (hd : 1 ≤ d) {x : Site d} (hx : Real.sqrt d ≤ euclidNorm x) :
    (2 : ℝ) ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ)) ≤
        ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) ∧
      ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ))
        ≤ (2 : ℝ) ^ ((d : ℝ) - 1) * euclidNorm x ^ (1 - (d : ℝ)) := by
  have hcell : MeasurableSet (cell x) := measurableSet_cell x
  have hvol_ne : volume (cell x) ≠ ⊤ := by rw [volume_cell]; exact ENNReal.one_ne_top
  have hvol_real : (volume (cell x)).toReal = 1 := by
    rw [volume_cell, ENNReal.toReal_one]
  have hbdd : ∀ᵐ a ∂(volume.restrict (cell x)),
      ‖(fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ))) a‖ ≤
        (2 : ℝ) ^ ((d : ℝ) - 1) * euclidNorm x ^ (1 - (d : ℝ)) := by
    filter_upwards [ae_restrict_mem hcell] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg a) _)]
    exact (rpow_mem_Icc_of_mem_cell hd hx ha).2
  have hint : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (cell x) volume :=
    Measure.integrableOn_of_bounded hvol_ne (measurable_norm.pow_const _).aestronglyMeasurable hbdd
  have hconst_lo :
      IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) =>
        (2 : ℝ) ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ))) (cell x) volume :=
    integrableOn_const (by rw [volume_cell]; exact ENNReal.one_ne_top)
  have hconst_hi :
      IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) =>
        (2 : ℝ) ^ ((d : ℝ) - 1) * euclidNorm x ^ (1 - (d : ℝ))) (cell x) volume :=
    integrableOn_const (by rw [volume_cell]; exact ENNReal.one_ne_top)
  constructor
  · have h := setIntegral_mono_on hconst_lo hint hcell fun v hv =>
      (rpow_mem_Icc_of_mem_cell hd hx hv).1
    rwa [setIntegral_const, measureReal_def, hvol_real, one_smul] at h
  · have h := setIntegral_mono_on hint hconst_hi hcell fun v hv =>
      (rpow_mem_Icc_of_mem_cell hd hx hv).2
    rwa [setIntegral_const, measureReal_def, hvol_real, one_smul] at h

end CERW.Support.Occupation
