import CERW.LimitShapes.Curvature.RadialIntegralAux
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Endpoint bounds for differences of Newtonian kernels

The scalar mean-value theorem bounds a kernel difference by the sum of the
order-one Riesz kernels at its endpoints. This gives an integrable majorant
for the continuity needed in `eq:curvature-improved`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- A negative power has a difference bound controlled by its two endpoint derivatives. -/
theorem abs_rpow_sub_rpow_le {p r s : ℝ} (hp : p ≤ 0) (hr : 0 < r) (hs : 0 < s) :
    |r ^ p - s ^ p| ≤ (-p) * (r ^ (p - 1) + s ^ (p - 1)) * |r - s| := by
  have ordered {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      |b ^ p - a ^ p| ≤ (-p) * (a ^ (p - 1) + b ^ (p - 1)) * (b - a) := by
    have hder : ∀ x ∈ Set.Icc a b, HasDerivWithinAt (fun x : ℝ => x ^ p)
        (p * x ^ (p - 1)) (Set.Icc a b) x := by
      intro x hx
      exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (ha.trans_le hx.1)))).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico a b,
        ‖p * x ^ (p - 1)‖ ≤ (-p) * (a ^ (p - 1) + b ^ (p - 1)) := by
      intro x hx
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonpos hp,
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (ha.trans_le hx.1).le _)]
      apply mul_le_mul_of_nonneg_left _ (neg_nonneg.mpr hp)
      exact (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (ha.trans_le hab).le _))
    simpa only [Real.norm_eq_abs] using
      norm_image_sub_le_of_norm_deriv_le_segment' hder hbound b ⟨hab, le_rfl⟩
  rcases le_total r s with h | h
  · rw [abs_sub_comm (r ^ p), abs_sub_comm r s,
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered hr h
  · have hh := ordered hs h
    rw [add_comm] at hh
    simpa only [abs_sub_comm s r, abs_of_nonneg (sub_nonneg.mpr h)] using hh

/-- Away from its two singular endpoints, a Newtonian kernel difference is bounded by
an endpoint Riesz majorant times the distance between the evaluation points. -/
theorem abs_newtonian_sub_le {d : ℕ} (hd : 3 ≤ d)
    (v y z : EuclideanSpace ℝ (Fin d)) (hy : v ≠ y) (hz : v ≠ z) :
    |‖v - y‖ ^ ((2 : ℝ) - d) - ‖v - z‖ ^ ((2 : ℝ) - d)| ≤
      ((d : ℝ) - 2) * (‖v - y‖ ^ (1 - (d : ℝ)) +
        ‖v - z‖ ^ (1 - (d : ℝ))) * ‖y - z‖ := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hh := abs_rpow_sub_rpow_le (p := (2 : ℝ) - d) (by linarith)
    (norm_pos_iff.mpr (sub_ne_zero.mpr hy)) (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  have he : (2 : ℝ) - d - 1 = 1 - (d : ℝ) := by ring
  rw [he, neg_sub] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _)))
  calc
    |‖v - y‖ - ‖v - z‖| ≤ ‖(v - y) - (v - z)‖ := abs_norm_sub_norm_le _ _
    _ = ‖y - z‖ := by rw [sub_sub_sub_cancel_left, norm_sub_rev]

end CERW.LimitShapes.Curvature
