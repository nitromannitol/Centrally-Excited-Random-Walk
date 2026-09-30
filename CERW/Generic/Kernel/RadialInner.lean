import CERW.Model.Space

/-!
# The radial component of the Newtonian kernel

For `v ≠ 0` the identity `2(|v|² - v·y) = |v - y|² + |v|² - |y|²` controls `u_v · (v - y)`: it is
at least `|v - y|²/(2|v|)` when `|y| ≤ |v|` (`eq:contact-sign`), at most `|v - y|²/(2|v|)` when
`|v| ≤ |y|` (Step 1 of the outer bound), and at most `|v - y|²/(2|v|) + (|v|² - |y|²)/(2|v|)` in
general (the near/far lemma).
-/

namespace CERW.Generic.Kernel

open CERW

variable {d : ℕ}

/-- `u_v · (v - y) = (|v - y|² + |v|² - |y|²)/(2|v|)` for `v ≠ 0`. -/
theorem inner_unitDir_sub_eq {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (unitDir v) (v - y) = (‖v - y‖ ^ 2 + ‖v‖ ^ 2 - ‖y‖ ^ 2) / (2 * ‖v‖) := by
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [unitDir, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq,
    norm_sub_sq_real]
  field_simp [hv']
  ring

/-- If `|y| ≤ |v|` and `v ≠ 0`, then `u_v · (v - y) ≥ |v - y|²/(2|v|)`. -/
theorem sq_div_le_inner_unitDir_sub {v y : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (hyv : ‖y‖ ≤ ‖v‖) : ‖v - y‖ ^ 2 / (2 * ‖v‖) ≤ inner ℝ (unitDir v) (v - y) := by
  rw [inner_unitDir_sub_eq hv]
  rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * ‖v‖)]
  nlinarith [pow_le_pow_left₀ (norm_nonneg y) hyv 2]

/-- If `|v| ≤ |y|` and `v ≠ 0`, then `u_v · (v - y) ≤ |v - y|²/(2|v|)`. -/
theorem inner_unitDir_sub_le_sq_div {v y : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0)
    (hvy : ‖v‖ ≤ ‖y‖) : inner ℝ (unitDir v) (v - y) ≤ ‖v - y‖ ^ 2 / (2 * ‖v‖) := by
  rw [inner_unitDir_sub_eq hv]
  rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * ‖v‖)]
  nlinarith [pow_le_pow_left₀ (norm_nonneg v) hvy 2]

end CERW.Generic.Kernel
