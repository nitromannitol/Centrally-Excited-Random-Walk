import CERW.Support.Occupation.CellNorm

/-!
# Directions across a cell

Two directions differ by at most twice the distance of the points over the length of either:
`|u_a - u_b| ≤ 2|a - b|/|a|` for `a ≠ 0`. On the cell `C_x` this gives
`|u_x - u_v| ≤ 2(1 + √d)/(1 + |v|)`, the direction bound `|u_x - u_v| ≤ C_d/(1 + |v|)` used
before `eq:direction-error`.
-/

namespace CERW.Support.Occupation

open LatticeProb CERW

variable {d : ℕ}

/-- For positive `A` and `B`, `|A⁻¹ - B⁻¹| * B = |B - A| / A`. -/
theorem abs_inv_sub_inv_mul_eq {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    |A⁻¹ - B⁻¹| * B = |B - A| / A := by
  have h1 : A⁻¹ - B⁻¹ = (B - A) / (A * B) := by
    field_simp
  rw [h1, abs_div, abs_of_pos (mul_pos hA hB)]
  field_simp

/-- For `a ≠ 0`, `|u_a - u_b| ≤ 2|a - b|/|a|`. -/
theorem norm_unitDir_sub_le {a b : EuclideanSpace ℝ (Fin d)} (ha : a ≠ 0) :
    ‖unitDir a - unitDir b‖ ≤ 2 * ‖a - b‖ / ‖a‖ := by
  rcases eq_or_ne b 0 with rfl | hb
  · have h : 2 * ‖a - 0‖ / ‖a‖ = 2 := by
      rw [sub_zero, mul_comm 2 ‖a‖, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr ha)]
    rw [h, unitDir_zero, sub_zero]
    calc ‖unitDir a‖ ≤ 1 := norm_unitDir_le a
      _ ≤ 2 := by norm_num
  · have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hdecomp : unitDir a - unitDir b
        = ‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b := by
      rw [unitDir, unitDir, smul_sub, sub_smul]
      module
    have hsecond : |‖a‖⁻¹ - ‖b‖⁻¹| * ‖b‖ ≤ ‖a - b‖ / ‖a‖ := by
      calc |‖a‖⁻¹ - ‖b‖⁻¹| * ‖b‖ = |‖b‖ - ‖a‖| / ‖a‖ :=
            abs_inv_sub_inv_mul_eq hA hB
        _ ≤ ‖b - a‖ / ‖a‖ := by
            gcongr
            exact abs_norm_sub_norm_le b a
        _ = ‖a - b‖ / ‖a‖ := by rw [norm_sub_rev]
    calc ‖unitDir a - unitDir b‖
        = ‖‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b‖ := by rw [hdecomp]
      _ ≤ ‖‖a‖⁻¹ • (a - b)‖ + ‖(‖a‖⁻¹ - ‖b‖⁻¹) • b‖ := norm_add_le _ _
      _ = ‖a‖⁻¹ * ‖a - b‖ + |‖a‖⁻¹ - ‖b‖⁻¹| * ‖b‖ := by
            simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg a)]
      _ ≤ ‖a - b‖ / ‖a‖ + ‖a - b‖ / ‖a‖ :=
            add_le_add (le_of_eq (inv_mul_eq_div ‖a‖ ‖a - b‖)) hsecond
      _ = 2 * ‖a - b‖ / ‖a‖ := by ring

/-- On the cell of `x`, `|u_x - u_v| ≤ 2(1 + √d)/(1 + |v|)`. -/
theorem norm_unitDir_sub_le_of_mem_cell (hd : 1 ≤ d) {x : Site d}
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cell x) :
    ‖unitDir (toSpace x) - unitDir v‖ ≤ 2 * (1 + Real.sqrt d) / (1 + ‖v‖) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hd
  rcases le_or_gt ‖v‖ 1 with hv1 | hv1
  · have hden : 0 < 1 + ‖v‖ := by positivity
    rw [le_div_iff₀ hden]
    have hnorm : ‖unitDir (toSpace x) - unitDir v‖ ≤ 2 := by
      calc ‖unitDir (toSpace x) - unitDir v‖
          ≤ ‖unitDir (toSpace x)‖ + ‖unitDir v‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (norm_unitDir_le _) (norm_unitDir_le _)
        _ = 2 := by norm_num
    calc ‖unitDir (toSpace x) - unitDir v‖ * (1 + ‖v‖)
        ≤ 2 * (1 + ‖v‖) := mul_le_mul_of_nonneg_right hnorm hden.le
      _ ≤ 2 * (1 + Real.sqrt d) := by
          have : ‖v‖ ≤ Real.sqrt d := le_trans hv1 hsqrt
          linarith
  · have hvne : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at hv1
      linarith
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have hcell : ‖v - toSpace x‖ ≤ Real.sqrt d / 2 := norm_sub_toSpace_le_of_mem_cell hv
    calc ‖unitDir (toSpace x) - unitDir v‖
        = ‖unitDir v - unitDir (toSpace x)‖ := norm_sub_rev _ _
      _ ≤ 2 * ‖v - toSpace x‖ / ‖v‖ := norm_unitDir_sub_le hvne
      _ ≤ 2 * (Real.sqrt d / 2) / ‖v‖ := by
            rw [mul_div_assoc, mul_div_assoc]
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hcell hpos.le) (by norm_num)
      _ = Real.sqrt d / ‖v‖ := by ring
      _ ≤ 2 * (1 + Real.sqrt d) / (1 + ‖v‖) := by
            rw [div_le_div_iff₀ hpos (by positivity)]
            have hst : Real.sqrt d ≤ Real.sqrt d * ‖v‖ := by
              calc Real.sqrt d = Real.sqrt d * 1 := by ring
                _ ≤ Real.sqrt d * ‖v‖ :=
                    mul_le_mul_of_nonneg_left hv1.le (Real.sqrt_nonneg d)
            linarith

end CERW.Support.Occupation
