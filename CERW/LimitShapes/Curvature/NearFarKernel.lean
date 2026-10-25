module

public import CERW.LimitShapes.Curvature.Mass

@[expose] public section

/-! # Radial kernel estimates for `lem:near-far` -/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

variable {d : ℕ}

/-- Between the two radii, the radial component of the direction of `v` along `v - y` is at most
`|v - y|² / (2b) + (K+2)w/2`: this is the identity `2(|v|² - v·y) = |v - y|² + |v|² - |y|²`
together with `|v|² - |y|² ≤ (K+2)bw`. -/
lemma inner_unitDir_le_of_ratio {b w K : ℝ} (hb : 0 < b) (hw : 0 < w) (hK : 1 ≤ K)
    (hwb : w ≤ K * b)
    {v y : EuclideanSpace ℝ (Fin d)} (hv : b ≤ ‖v‖) (hv' : ‖v‖ ≤ b + w) (hy : b ≤ ‖y‖) :
    inner ℝ (unitDir v) (v - y) ≤ ‖v - y‖ ^ 2 / (2 * b) + (K + 2) * w / 2 := by
  have hvpos : 0 < ‖v‖ := hb.trans_le hv
  have hid : 2 * inner ℝ v (v - y) = ‖v - y‖ ^ 2 + (‖v‖ ^ 2 - ‖y‖ ^ 2) := by
    rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have h1 : ‖v‖ ^ 2 ≤ (b + w) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv' 2
  have h2 : b ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hb.le hy 2
  have h3 : w * w ≤ K * b * w := mul_le_mul_of_nonneg_right hwb hw.le
  have hX : inner ℝ v (v - y) ≤ (‖v - y‖ ^ 2 + (K + 2) * b * w) / 2 := by
    have : ‖v‖ ^ 2 - ‖y‖ ^ 2 ≤ (K + 2) * b * w := by linarith
    linarith
  have hnn : 0 ≤ (‖v - y‖ ^ 2 + (K + 2) * b * w) / 2 := by positivity
  calc inner ℝ (unitDir v) (v - y) = ‖v‖⁻¹ * inner ℝ v (v - y) := by
        rw [unitDir, real_inner_smul_left]
    _ ≤ ‖v‖⁻¹ * ((‖v - y‖ ^ 2 + (K + 2) * b * w) / 2) :=
        mul_le_mul_of_nonneg_left hX (inv_nonneg.mpr hvpos.le)
    _ ≤ b⁻¹ * ((‖v - y‖ ^ 2 + (K + 2) * b * w) / 2) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hb hv) hnn
    _ = ‖v - y‖ ^ 2 / (2 * b) + (K + 2) * w / 2 := by field_simp

/-- Outside `B(y, w)`, between the two radii, the positive part of the potential integrand is at
most `|v - y|^{2-d} / (2b) + ((K+2)w/2) |v - y|^{-d}`. -/
lemma integrand_far_le_of_ratio {b w K : ℝ} (hb : 0 < b) (hw : 0 < w) (hK : 1 ≤ K)
    (hwb : w ≤ K * b)
    {v y : EuclideanSpace ℝ (Fin d)} (hv : b ≤ ‖v‖) (hv' : ‖v‖ ≤ b + w) (hy : b ≤ ‖y‖)
    (hvy : w ≤ ‖v - y‖) :
    max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      ≤ 1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)) + (K + 2) * w / 2 * (‖v - y‖ ^ d)⁻¹ := by
  have hr : 0 < ‖v - y‖ := hw.trans_le hvy
  have hrd : 0 < ‖v - y‖ ^ d := pow_pos hr d
  have hrpow : ‖v - y‖ ^ (2 - (d : ℝ)) = ‖v - y‖ ^ 2 / ‖v - y‖ ^ d := by
    rw [Real.rpow_sub hr, Real.rpow_two, Real.rpow_natCast]
  have hrhs : 1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)) + (K + 2) * w / 2 * (‖v - y‖ ^ d)⁻¹
      = (‖v - y‖ ^ 2 / (2 * b) + (K + 2) * w / 2) / ‖v - y‖ ^ d := by
    rw [hrpow]
    field_simp
  rw [hrhs]
  refine max_le (div_le_div_of_nonneg_right
    (inner_unitDir_le_of_ratio hb hw hK hwb hv hv' hy) hrd.le) ?_
  positivity

end CERW.LimitShapes.Curvature
