import CERW.Generic.Kernel.RadialInner
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Radial differentiation of the curvature kernel

The differentiated integrand used in the proof of `eq:curvature-improved`.
-/

namespace CERW.LimitShapes.Curvature

open CERW

/-- The weighted radial kernel derivative in `eq:curvature-improved`. -/
theorem hasDerivAt_weighted_radial_kernel {d : ℕ} (hd : 3 ≤ d)
    (v u : EuclideanSpace ℝ (Fin d)) (t : ℝ)
    (hv : v ≠ 0) (ht : 0 < t) (hvt : v - t • u ≠ 0) :
    HasDerivAt (fun s : ℝ =>
      s ^ (d - 2) * (‖v - s • u‖ ^ ((2 : ℝ) - d) / ‖v‖))
      (((d : ℝ) - 2) * t ^ (d - 3) *
        (inner ℝ (CERW.unitDir v) (v - t • u) / ‖v - t • u‖ ^ d)) t := by
  have hn : ‖v - t • u‖ ≠ 0 := norm_ne_zero_iff.mpr hvt
  have hnpos : 0 < ‖v - t • u‖ := norm_pos_iff.mpr hvt
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have ha : HasDerivAt (fun s : ℝ => v - s • u) (-u) t := by
    convert (hasDerivAt_const t v).sub ((hasDerivAt_id t).smul_const u) using 1 <;>
      first | rfl | simp only [zero_sub, one_smul]
  have hn' : HasDerivAt (fun s : ℝ => ‖v - s • u‖)
      (inner ℝ (v - t • u) (-u) / ‖v - t • u‖) t := by
    simpa only [zero_sub, one_smul, Real.sqrt_sq (norm_nonneg _),
      mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      ha.norm_sq.sqrt (pow_ne_zero 2 hn)
  have hp := (hn'.rpow_const (p := (2 : ℝ) - d) (Or.inl hn)).div_const ‖v‖
  have hd2 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ d)]; norm_num
  have hd3 : d - 2 - 1 = d - 3 := by omega
  have ht2 : t ^ (d - 2) = t ^ (d - 3) * t := by
    conv_lhs => rw [show d - 2 = (d - 3) + 1 by omega, pow_succ]
  convert ((hasDerivAt_id t).pow (d - 2)).mul hp using 1 <;> try rfl
  dsimp only [id_eq, Pi.pow_apply]
  rw [hd2, hd3, ht2]
  rw [Real.rpow_sub hnpos, Real.rpow_natCast, Real.rpow_two]
  have he : (2 : ℝ) - (d : ℝ) - 1 = 1 - (d : ℝ) := by ring
  rw [he, Real.rpow_sub hnpos, Real.rpow_one, Real.rpow_natCast]
  rw [unitDir, real_inner_smul_left]
  have hi : ‖v - t • u‖ ^ 2 + t * inner ℝ (v - t • u) u =
      inner ℝ v (v - t • u) := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, real_inner_smul_left,
      real_inner_comm u (v - t • u)]
    ring
  rw [← hi, inner_neg_right]
  field_simp [hn, hvn, ne_of_gt ht]
  ring

end CERW.LimitShapes.Curvature
