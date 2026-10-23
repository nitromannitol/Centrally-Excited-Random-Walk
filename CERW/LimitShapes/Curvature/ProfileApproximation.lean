import CERW.LimitShapes.Curvature.ProfilePotential

/-!
# From the annular potential to the local-time profile

The ball potential and the annular remainder give the deterministic comparison used in
`sec:global-profile`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory
open LatticeProb (Site)

/-- The cone profile is Lipschitz in its radius. -/
theorem cone_radius_lipschitz {a b t k : ℝ} (hk : 0 ≤ k) :
    |k * max (a - t) 0 - k * max (b - t) 0| ≤ k * |a - b| := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hk]
  apply mul_le_mul_of_nonneg_left _ hk
  simpa only [sub_sub_sub_cancel_right] using abs_max_sub_max_le_abs (a - t) (b - t) 0

/-- The full potential differs from the radius cone by the annular error and radius error. -/
theorem potential_profile_error {d : ℕ} (hd : 2 ≤ d) {ε r F G : ℝ}
    (hε : 0 ≤ ε) (X : ℕ → Site d) (n : ℕ) (hb : 0 < innerRadius X n)
    (hradius : |innerRadius X n - r| ≤ F)
    (hpotential : ∀ y : EuclideanSpace ℝ (Fin d),
      |potential d ε (cellSet X n \ Metric.ball 0 (innerRadius X n)) y| ≤ G)
    (y : EuclideanSpace ℝ (Fin d)) :
    |potential d ε (cellSet X n) y - 2 * d * ε * max (r - ‖y‖) 0| ≤
      G + 2 * d * ε * F := by
  rw [CERW.Support.Outer.Radius.potential_split hd ε
    (CERW.Support.Occupation.measurableSet_cellSet X n)
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ d) X n)) hb
    (CERW.Support.Outer.Radius.ball_innerRadius_subset (by omega) X n) y]
  have hk : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  calc
    _ = |potential d ε (cellSet X n \ Metric.ball 0 (innerRadius X n)) y +
        (2 * d * ε * max (innerRadius X n - ‖y‖) 0 -
          2 * d * ε * max (r - ‖y‖) 0)| := by congr 1; ring
    _ ≤ |potential d ε (cellSet X n \ Metric.ball 0 (innerRadius X n)) y| +
        |2 * d * ε * max (innerRadius X n - ‖y‖) 0 -
          2 * d * ε * max (r - ‖y‖) 0| := abs_add_le _ _
    _ ≤ G + 2 * d * ε * F := add_le_add (hpotential y)
      ((cone_radius_lipschitz hk).trans (mul_le_mul_of_nonneg_left hradius hk))

/-- The approximation error and the potential profile error add. -/
theorem local_time_profile_error {d : ℕ} (hd : 2 ≤ d) {ε r F G H : ℝ}
    (hε : 0 ≤ ε) (X : ℕ → Site d) (n : ℕ) (hb : 0 < innerRadius X n)
    (hradius : |innerRadius X n - r| ≤ F)
    (hpotential : ∀ y : EuclideanSpace ℝ (Fin d),
      |potential d ε (cellSet X n \ Metric.ball 0 (innerRadius X n)) y| ≤ G)
    (y : EuclideanSpace ℝ (Fin d))
    (hlocal : |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ H) :
    |cellLocalTime X n y - 2 * d * ε * max (r - ‖y‖) 0| ≤
      H + G + 2 * d * ε * F := by
  exact (abs_sub_le (cellLocalTime X n y) (potential d ε (cellSet X n) y) _).trans
    ((add_le_add hlocal (potential_profile_error hd hε X n hb hradius hpotential y)).trans
      (by ring_nf; exact le_refl _))

/-- Outside a ball containing the cells and the cone both profiles vanish. -/
theorem local_time_profile_eq_zero {d : ℕ} (hd : 1 ≤ d) {r T : ℝ}
    (X : ℕ → Site d) (n : ℕ) (hcell : maxRadius X n + Real.sqrt d ≤ T)
    (hr : r ≤ T) (y : EuclideanSpace ℝ (Fin d)) (hy : T < ‖y‖) (k : ℝ) :
    |cellLocalTime X n y - k * max (r - ‖y‖) 0| = 0 := by
  have hout : y ∉ cellSet X n := by
    intro h
    have hnorm := CERW.Support.Occupation.cellSet_subset_ball hd X n h
    rw [mem_ball_zero_iff] at hnorm
    linarith
  rw [CERW.Support.Occupation.cellLocalTime_eq_zero_of_not_mem X n hout,
    max_eq_right (by linarith : r - ‖y‖ ≤ 0), mul_zero, sub_self, abs_zero]

end CERW.LimitShapes.Curvature
