import CERW.Generic.Kernel.RadialInner
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kernel estimates for an outer cap

The geometric negative contribution and curvature bound used in `eq:outer-cap-mass`.
-/

namespace CERW.LimitShapes.Curvature

open CERW

/-- The outer cap has a negative radial component and controlled distance
in `eq:outer-cap-mass`. -/
theorem cap_inner_neg_and_norm_le {d : ℕ}
    (v u : EuclideanSpace ℝ (Fin d)) (A t : ℝ)
    (hA : 0 < A) (ht : 0 < t) (htA : t ≤ A / 2) (hu : ‖u‖ = 1)
    (hv : ‖v‖ ≤ A) (hcap : ‖v - A • u‖ ≤ t) :
    inner ℝ (CERW.unitDir v) (v - (A + 4 * t) • u) ≤ -t ∧
      ‖v - (A + 4 * t) • u‖ ≤ 5 * t := by
  have hAu : ‖A • u‖ = A := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA, hu, mul_one]
  have hr : A - t ≤ ‖v‖ := by
    have := norm_sub_norm_le (A • u) v
    rw [hAu, norm_sub_rev] at this
    linarith
  have hrpos : 0 < ‖v‖ := by linarith
  have hsq : ‖v‖ ^ 2 + A ^ 2 - 2 * A * inner ℝ v u ≤ t ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hcap 2
    rw [norm_sub_sq_real, hAu, inner_smul_right] at this
    nlinarith
  have hangle : 1 - t / A ≤ inner ℝ (unitDir v) u := by
    rw [unitDir, real_inner_smul_left]
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hrpos).2
    have halg : A * ‖v‖ - t * ‖v‖ ≤ A * inner ℝ v u := by
      nlinarith [sq_nonneg (‖v‖ - A)]
    have := (div_le_div_iff_of_pos_right hA).2 halg
    field_simp at this ⊢
    nlinarith
  have hself : inner ℝ (unitDir v) v = ‖v‖ := by
    rw [unitDir, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  constructor
  · rw [inner_sub_right, inner_smul_right, hself]
    have hmul := mul_le_mul_of_nonneg_left hangle (by linarith : 0 ≤ A + 4 * t)
    have hfrac : (A + 4 * t) * (1 - t / A) ≥ A + t := by
      apply (le_of_mul_le_mul_right ?_ hA)
      field_simp
      nlinarith
    linarith
  · calc
      ‖v - (A + 4 * t) • u‖ = ‖(v - A • u) - (4 * t) • u‖ := by
        congr 1
        rw [add_smul]
        abel
      _ ≤ ‖v - A • u‖ + ‖(4 * t) • u‖ := norm_sub_le _ _
      _ ≤ 5 * t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hu]
        linarith

/-- The explicit negative cap kernel bound in `eq:outer-cap-mass`. -/
theorem cap_kernel_le {d : ℕ}
    (v u : EuclideanSpace ℝ (Fin d)) (A t : ℝ)
    (hA : 0 < A) (ht : 0 < t) (htA : t ≤ A / 2) (hu : ‖u‖ = 1)
    (hv : ‖v‖ ≤ A) (hcap : ‖v - A • u‖ ≤ t) :
    inner ℝ (CERW.unitDir v) (v - (A + 4 * t) • u) /
        ‖v - (A + 4 * t) • u‖ ^ d ≤
      -(1 / ((5 : ℝ) ^ d)) * t ^ ((1 : ℝ) - d) := by
  obtain ⟨hi, hn⟩ := cap_inner_neg_and_norm_le v u A t hA ht htA hu hv hcap
  have hpos : 0 < ‖v - (A + 4 * t) • u‖ := by
    by_contra h
    have hz := norm_eq_zero.mp (le_antisymm (le_of_not_gt h) (norm_nonneg _))
    rw [hz, inner_zero_right] at hi
    linarith
  calc
    _ ≤ -t / ‖v - (A + 4 * t) • u‖ ^ d :=
      div_le_div_of_nonneg_right hi (by positivity)
    _ ≤ -t / (5 * t) ^ d := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hp := pow_le_pow_left₀ (norm_nonneg _) hn d
      nlinarith
    _ = _ := by
      rw [Real.rpow_sub ht, Real.rpow_one, Real.rpow_natCast, mul_pow]
      ring

/-- The positive kernel is bounded by curvature when the observation point is farther out. -/
theorem positive_kernel_le_curvature {d : ℕ} (hd : 2 ≤ d)
    (v y : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) (hvy : v ≠ y)
    (hsize : ‖v‖ ≤ ‖y‖) :
    max (inner ℝ (CERW.unitDir v) (v - y) / ‖v - y‖ ^ d) 0 ≤
      (‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖) / 2 := by
  have _hd : 2 ≤ d := hd
  have hr : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvy)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  apply max_le
  · have hi := Generic.Kernel.inner_unitDir_sub_le_sq_div hv hsize
    calc
      _ ≤ (‖v - y‖ ^ 2 / (2 * ‖v‖)) / ‖v - y‖ ^ d :=
        div_le_div_of_nonneg_right hi (by positivity)
      _ = _ := by
        rw [Real.rpow_sub hr, Real.rpow_natCast, Real.rpow_two]
        ring
  · positivity

end CERW.LimitShapes.Curvature
