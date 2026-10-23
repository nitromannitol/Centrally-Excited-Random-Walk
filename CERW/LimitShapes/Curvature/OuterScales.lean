import CERW.LimitShapes.Curvature.FluctuationProbabilityAux
import CERW.LimitShapes.Energy.SiteScales

/-! # Outer error scales

The contact error multiplied by the crossing logarithms is the error rate of
Proposition `prop:stronger-outer`.
-/

namespace CERW.LimitShapes.Curvature

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.ContactEvent

/-- The contact error times the width logarithms equals the outer error rate. -/
theorem contact_error_mul_log_pow {d : ℕ} {ε : ℝ} {n : ℕ}
    (hr : 0 < scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n)
    (hlog : 0 < Real.log n) :
    (scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
      contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n) * Real.log n ^ d =
    if d = 2 then Real.sqrt (CERW.Support.Outer.Radius.radius d ε n) *
      Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1) := by
  rw [Energy.scale_mul_contactRate _ ε n hr, euclidean_scale_eq_radius]
  split_ifs with hd
  · subst d
    rw [Real.sqrt_mul (le_of_lt (by rwa [← euclidean_scale_eq_radius])),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, mul_assoc,
      ← Real.rpow_natCast, ← Real.rpow_add hlog]
    congr 2
    norm_num
  · calc
      Real.log n * Real.log n ^ d = Real.log n ^ (d + 1) := by
        rw [pow_succ]; ring
      _ = Real.log n ^ ((d : ℝ) + 1) := by
        rw [← Real.rpow_natCast, Nat.cast_add, Nat.cast_one]

end CERW.LimitShapes.Curvature
