import CERW.Model.Space

/-!
# Positivity of the potential kernel beyond the contact radius

If `|v| ≥ |y|`, the kernel `u_v · (v - y) |v - y|^{-d}` of the potential is at least
`2^{1-d} |v|^{1-d}`. This is the inequality that makes every part of the range outside the
inner ball contribute positively to the potential at a contact point (`eq:contactbound`).
-/

namespace CERW.Support.Contact

open CERW

variable {d : ℕ}

/-- For `|y| ≤ |v|` and `v ≠ y`, `2 (|v|² - v·y) ≥ |v - y|²`. -/
theorem sq_norm_sub_le_two_mul {v y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ ≤ ‖v‖) :
    ‖v - y‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 - inner ℝ v y) := by
  have hy2 : ‖y‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
  rw [norm_sub_sq_real v y]
  linarith

/-- For `d ≥ 2`, `|y| ≤ |v|` and `v ≠ y`:
`2^{1-d} |v|^{1-d} ≤ u_v · (v - y) / |v - y|^d`. -/
theorem rpow_le_inner_unitDir_div {v y : EuclideanSpace ℝ (Fin d)} (hd : 2 ≤ d)
    (hy : ‖y‖ ≤ ‖v‖) (hvy : v ≠ y) :
    (2 : ℝ) ^ (1 - (d : ℝ)) * ‖v‖ ^ (1 - (d : ℝ)) ≤ inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := by
  have hv : v ≠ 0 := by
    rintro rfl
    exact hvy (norm_le_zero_iff.mp (by simpa using hy)).symm
  have hs : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hr : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvy)
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hz : (2 : ℝ) - (d : ℝ) ≤ 0 := by linarith
  have hle : ‖v - y‖ ≤ 2 * ‖v‖ := by linarith [norm_sub_le v y, hy]
  have hinner : inner ℝ (unitDir v) (v - y) = ‖v‖⁻¹ * (‖v‖ ^ 2 - inner ℝ v y) := by
    rw [unitDir, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
  have hlow : ‖v - y‖ ^ 2 / (2 * ‖v‖) ≤ inner ℝ (unitDir v) (v - y) := by
    rw [hinner]
    have hdiv : ‖v - y‖ ^ 2 / 2 ≤ ‖v‖ ^ 2 - inner ℝ v y := by
      have hsq := sq_norm_sub_le_two_mul (d := d) hy
      linarith
    have hmul := mul_le_mul_of_nonneg_left hdiv (inv_nonneg.mpr (le_of_lt hs))
    calc
      ‖v - y‖ ^ 2 / (2 * ‖v‖) = ‖v‖⁻¹ * (‖v - y‖ ^ 2 / 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
      _ ≤ ‖v‖⁻¹ * (‖v‖ ^ 2 - inner ℝ v y) := hmul
  have hstep : (‖v - y‖ ^ 2 / (2 * ‖v‖)) / ‖v - y‖ ^ d ≤
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d :=
    div_le_div_of_nonneg_right hlow (le_of_lt (pow_pos hr d))
  have hpow : (2 * ‖v‖) ^ (1 - (d : ℝ)) = (2 * ‖v‖) ^ (2 - (d : ℝ)) / (2 * ‖v‖) := by
    have hx : 0 < 2 * ‖v‖ := by positivity
    rw [show (1 : ℝ) - (d : ℝ) = (2 - (d : ℝ)) - 1 by ring,
      Real.rpow_sub hx (2 - (d : ℝ)) 1, Real.rpow_one]
  have hEq : ‖v - y‖ ^ (2 - (d : ℝ)) / (2 * ‖v‖) =
      (‖v - y‖ ^ 2 / (2 * ‖v‖)) / ‖v - y‖ ^ d := by
    rw [Real.rpow_sub hr (2 : ℝ) (d : ℝ), Real.rpow_two, Real.rpow_natCast, div_div,
      div_div, mul_comm (‖v - y‖ ^ d) (2 * ‖v‖)]
  calc
    (2 : ℝ) ^ (1 - (d : ℝ)) * ‖v‖ ^ (1 - (d : ℝ))
        = (2 * ‖v‖) ^ (1 - (d : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) (le_of_lt hs)]
    _ = (2 * ‖v‖) ^ (2 - (d : ℝ)) / (2 * ‖v‖) := hpow
    _ ≤ ‖v - y‖ ^ (2 - (d : ℝ)) / (2 * ‖v‖) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact Real.rpow_le_rpow_of_nonpos hr hle hz
    _ = (‖v - y‖ ^ 2 / (2 * ‖v‖)) / ‖v - y‖ ^ d := hEq
    _ ≤ inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := hstep

end CERW.Support.Contact
