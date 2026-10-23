import CERW.LimitShapes.Curvature.RadialDerivative
import CERW.Generic.Kernel.Integrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrability for the integrated radial curvature identity

The absolute curvature kernel is dominated by the locally integrable Riesz kernel.
The uniform Riesz bound gives joint integrability on a bounded time interval and a
bounded measurable spatial set, as needed for Fubini in `eq:curvature-improved`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The absolute radial curvature kernel is bounded by the Riesz kernel of order one. -/
theorem abs_radial_curvature_kernel_le {d : ℕ} (hd : 3 ≤ d)
    (v y : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d| ≤ ‖v - y‖ ^ (1 - (d : ℝ)) := by
  by_cases h : v - y = 0
  · simp [h, zero_pow (by omega : d ≠ 0), Real.zero_rpow (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith : 1 - (d : ℝ) ≠ 0)]
  have hn : 0 < ‖v - y‖ := norm_pos_iff.mpr h
  calc
    |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d|
        ≤ ‖v - y‖ / ‖v - y‖ ^ d := by
      rw [abs_div, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact div_le_div_of_nonneg_right
        ((abs_real_inner_le_norm _ _).trans (by
          simpa using mul_le_mul_of_nonneg_right (norm_unitDir_le v) (norm_nonneg (v - y))))
        (pow_nonneg (norm_nonneg _) _)
    _ = ‖v - y‖ ^ (1 - (d : ℝ)) := by
      rw [Real.rpow_sub hn, Real.rpow_one, Real.rpow_natCast]

/-- The order-one Riesz kernel is jointly integrable on a finite interval and a finite-volume
measurable set, uniformly along any radial line. -/
theorem integrable_radial_riesz_prod {d : ℕ} (hd : 1 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hfin : volume E ≠ ⊤) (u : EuclideanSpace ℝ (Fin d)) (t T : ℝ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      ‖p.2 - p.1 • u‖ ^ (1 - (d : ℝ)))
      ((volume.restrict (Set.Ioc t T)).prod (volume.restrict E)) := by
  have hm : StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      ‖p.2 - p.1 • u‖ ^ (1 - (d : ℝ))) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun s =>
      (Generic.Kernel.integrableOn_and_setIntegral_le hd hE hfin (s • u)).1
  · apply Integrable.mono' (integrable_const
        (d * unitBallVolume d * ((volume E).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)))
        hm.norm.integral_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro s
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [abs_of_nonneg
      (integral_nonneg (fun v => Real.rpow_nonneg (norm_nonneg _) _))]
    exact (Generic.Kernel.integrableOn_and_setIntegral_le hd hE hfin (s • u)).2

/-- The curvature kernel is jointly absolutely integrable on a finite time interval. -/
theorem integrable_radial_curvature_prod {d : ℕ} (hd : 3 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hfin : volume E ≠ ⊤) (u : EuclideanSpace ℝ (Fin d)) (t T : ℝ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir p.2) (p.2 - p.1 • u) / ‖p.2 - p.1 • u‖ ^ d)
      ((volume.restrict (Set.Ioc t T)).prod (volume.restrict E)) := by
  apply (integrable_radial_riesz_prod (by omega : 1 ≤ d) hE hfin u t T).mono'
  · exact (by unfold unitDir; fun_prop : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
        inner ℝ (unitDir p.2) (p.2 - p.1 • u) / ‖p.2 - p.1 • u‖ ^ d)
      ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using abs_radial_curvature_kernel_le hd p.2 (p.1 • u)

/-- Multiplication by the radial polynomial preserves joint integrability on positive intervals. -/
theorem integrable_weighted_radial_curvature_prod {d : ℕ} (hd : 3 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hfin : volume E ≠ ⊤) (u : EuclideanSpace ℝ (Fin d))
    {t T : ℝ} (ht : 0 < t) (_htT : t ≤ T) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      p.1 ^ (d - 3) *
        (inner ℝ (unitDir p.2) (p.2 - p.1 • u) / ‖p.2 - p.1 • u‖ ^ d))
      ((volume.restrict (Set.Ioc t T)).prod (volume.restrict E)) := by
  apply (integrable_radial_curvature_prod hd hE hfin u t T).bdd_mul
    (c := T ^ (d - 3))
    (by fun_prop : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      p.1 ^ (d - 3))).aestronglyMeasurable
  have ha : ∀ᵐ s ∂volume.restrict (Set.Ioc t T), s ∈ Set.Ioc t T :=
    ae_restrict_mem measurableSet_Ioc
  have hp : ∀ᵐ p ∂(volume.restrict (Set.Ioc t T)).prod (volume.restrict E),
      p.1 ∈ Set.Ioc t T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ha] with s hs using Filter.Eventually.of_forall (fun _ => hs)
  filter_upwards [hp] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt (ht.trans hp.1)) _)]
  exact pow_le_pow_left₀ (le_of_lt (ht.trans hp.1)) hp.2 _

/-- A measurable set contained in a bounded radial band has finite volume. -/
theorem volume_ne_top_of_radial_band {d : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))} {R : ℝ}
    (hband : ∀ v ∈ E, ‖v‖ ≤ R) : volume E ≠ ⊤ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono (show E ⊆ Metric.ball 0 (R + 1) from ?_))
    measure_ball_lt_top
  intro v hv
  simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt (hband v hv) (lt_add_one R)

/-- Factoring out one power of the radius lowers the Newtonian kernel to the Riesz kernel. -/
theorem rpow_two_sub_eq_mul {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 ≤ r) :
    r ^ ((2 : ℝ) - d) = r * r ^ (1 - (d : ℝ)) := by
  rcases hr.eq_or_lt with h | h
  · subst r
    rw [Real.zero_rpow (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith : (2 : ℝ) - d ≠ 0), zero_mul]
  · calc
      r ^ ((2 : ℝ) - d) = r ^ (1 + (1 - (d : ℝ))) := by congr 1; ring
      _ = r ^ (1 : ℝ) * r ^ (1 - (d : ℝ)) := Real.rpow_add h _ _
      _ = r * r ^ (1 - (d : ℝ)) := by rw [Real.rpow_one]

/-- The endpoint Newtonian kernel divided by radius is integrable on a bounded radial band
separated from the origin. -/
theorem integrableOn_radial_endpoint {d : ℕ} (hd : 3 ≤ d)
    {b R : ℝ} (hb : 0 < b)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => ‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖) E := by
  have hfin := volume_ne_top_of_radial_band (fun v hv => (hband v hv).2)
  have hi := (Generic.Kernel.integrableOn_and_setIntegral_le
    (by omega : 1 ≤ d) hE hfin y).1
  have hi' : IntegrableOn (fun v =>
      (‖v - y‖ / ‖v‖) * ‖v - y‖ ^ (1 - (d : ℝ))) E := by
    apply hi.bdd_mul (c := (R + ‖y‖) / b)
      ((by fun_prop : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
        ‖v - y‖ / ‖v‖)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hE] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact div_le_div₀
      (by linarith [(hband v hv).2, norm_nonneg v, norm_nonneg y])
      (by linarith [norm_sub_le v y, (hband v hv).2]) hb (hband v hv).1
  apply hi'.congr
  exact Filter.Eventually.of_forall fun v => by
    dsimp only
    rw [rpow_two_sub_eq_mul hd (norm_nonneg (v - y))]
    ring

end CERW.LimitShapes.Curvature
