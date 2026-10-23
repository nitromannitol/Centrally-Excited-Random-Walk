import CERW.LimitShapes.Curvature.SegmentDerivative
import CERW.LimitShapes.Curvature.Mass

/-!
# Global continuity of the curvature integral

An endpoint mean-value estimate and the uniform order-one Riesz integral bound
give a global Lipschitz constant. In dimension two the integral is constant.
This supplies the continuity needed for the maximum principle in
`eq:curvature-improved`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The actual curvature integral is globally Lipschitz on a bounded radial band. -/
theorem exists_lipschitz_curvatureIntegral {d : ℕ} (hd : 2 ≤ d)
    {b R : ℝ} (hb : 0 < b) (hR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y z : EuclideanSpace ℝ (Fin d),
      |curvatureIntegral E y - curvatureIntegral E z| ≤ L * ‖y - z‖ := by
  have hRpos : 0 < R := hb.trans_le hR
  by_cases hd2 : d = 2
  · subst d
    refine ⟨0, le_rfl, ?_⟩
    intro y z
    simp only [curvatureIntegral, Nat.cast_ofNat, sub_self, Real.rpow_zero,
      sub_self, abs_zero, zero_mul, le_refl]
  have hd3 : 3 ≤ d := by omega
  haveI : NeZero d := ⟨by omega⟩
  let C : ℝ := ((d : ℝ) - 2) / b
  let K : ℝ := d * unitBallVolume d *
    ((volume E).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)
  have hC : 0 ≤ C := div_nonneg (by exact_mod_cast Nat.sub_le_sub_right hd 2) hb.le
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (unitBallVolume_pos d).le)
      (Real.rpow_nonneg (div_nonneg ENNReal.toReal_nonneg (unitBallVolume_pos d).le) _)
  refine ⟨C * (K + K), mul_nonneg hC (add_nonneg hK hK), ?_⟩
  intro y z
  let f := fun w : EuclideanSpace ℝ (Fin d) =>
    fun v : EuclideanSpace ℝ (Fin d) => ‖v - w‖ ^ ((2 : ℝ) - d) / ‖v‖
  let g := fun w : EuclideanSpace ℝ (Fin d) =>
    fun v : EuclideanSpace ℝ (Fin d) => ‖v - w‖ ^ (1 - (d : ℝ))
  have hf (w) : IntegrableOn (f w) E := integrableOn_curvature hd hb hE hband w
  have hg (w) : IntegrableOn (g w) E ∧ (∫ v in E, g w v) ≤ K :=
    Generic.Kernel.integrableOn_and_setIntegral_le (by omega) hE
      (band_measure_ne_top (R := R + R) (fun v hv =>
        (hband v hv).2.trans (le_add_of_nonneg_right hRpos.le))) w
  have hy : ∀ᵐ v : EuclideanSpace ℝ (Fin d), v ≠ y := by
    simp only [ae_iff, not_not, Set.setOf_eq_eq_singleton, measure_singleton]
  have hz : ∀ᵐ v : EuclideanSpace ℝ (Fin d), v ≠ z := by
    simp only [ae_iff, not_not, Set.setOf_eq_eq_singleton, measure_singleton]
  have hpoint : ∀ᵐ v ∂volume.restrict E,
      |f y v - f z v| ≤ C * (g y v + g z v) * ‖y - z‖ := by
    filter_upwards [ae_restrict_mem hE, ae_restrict_of_ae hy,
      ae_restrict_of_ae hz] with v hv hvy hvz
    have hnum := abs_newtonian_sub_le hd3 v y z hvy hvz
    have hn : 0 < ‖v‖ := hb.trans_le (hband v hv).1
    dsimp only [f, g, C]
    rw [← sub_div, abs_div, abs_of_pos hn]
    calc
      _ ≤ (((d : ℝ) - 2) * (‖v - y‖ ^ (1 - (d : ℝ)) +
          ‖v - z‖ ^ (1 - (d : ℝ))) * ‖y - z‖) / ‖v‖ :=
        div_le_div_of_nonneg_right hnum hn.le
      _ ≤ (((d : ℝ) - 2) * (‖v - y‖ ^ (1 - (d : ℝ)) +
          ‖v - z‖ ^ (1 - (d : ℝ))) * ‖y - z‖) / b := by
        apply div_le_div_of_nonneg_left _ hb (hband v hv).1
        exact mul_nonneg (mul_nonneg (by exact_mod_cast Nat.sub_le_sub_right hd 2)
          (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_nonneg (norm_nonneg _) _))) (norm_nonneg _)
      _ = _ := by ring
  change |(∫ v in E, f y v) - ∫ v in E, f z v| ≤ _
  rw [← integral_sub (hf y) (hf z)]
  calc
    _ ≤ ∫ v in E, |f y v - f z v| := abs_integral_le_integral_abs
    _ ≤ ∫ v in E, C * (g y v + g z v) * ‖y - z‖ :=
      integral_mono_ae ((hf y).sub (hf z)).abs
        ((((hg y).1.add (hg z).1).const_mul C).mul_const _) hpoint
    _ = C * ((∫ v in E, g y v) + ∫ v in E, g z v) * ‖y - z‖ := by
      rw [integral_mul_const, integral_const_mul, integral_add (hg y).1 (hg z).1]
    _ ≤ C * (K + K) * ‖y - z‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (hg y).2 (hg z).2) hC) (norm_nonneg _)

/-- Global continuity of the actual curvature integral used in `eq:curvature-improved`. -/
theorem continuous_curvatureIntegral {d : ℕ} (hd : 2 ≤ d)
    {b R : ℝ} (hb : 0 < b) (hR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) :
    Continuous (curvatureIntegral E) := by
  obtain ⟨L, hL, hbound⟩ := exists_lipschitz_curvatureIntegral hd hb hR hE hband
  apply (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) ?_).continuous
  intro y z
  change dist (curvatureIntegral E y) (curvatureIntegral E z) ≤ L * dist y z
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hbound y z

end CERW.LimitShapes.Curvature
