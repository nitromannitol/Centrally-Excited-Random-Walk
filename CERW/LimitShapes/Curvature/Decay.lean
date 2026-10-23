import CERW.LimitShapes.Curvature.FarPoint
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Decay of the actual potentials

Separation from a bounded radial band gives decay at infinity, as used in
`eq:curvature-improved` and `sec:global-profile`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory Filter Topology

/-- The curvature integral of a bounded radial band tends to zero at infinity. -/
theorem tendsto_curvatureIntegral_cobounded {d : ℕ} (hd : 3 ≤ d)
    {b R : ℝ} (hb : 0 < b) (hR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) :
    Filter.Tendsto (curvatureIntegral E)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin d))) (nhds (0 : ℝ)) := by
  have ht : Tendsto (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ / 2)
      (Bornology.cobounded _) atTop :=
    tendsto_norm_cobounded_atTop.atTop_div_const (by norm_num)
  have hp : Tendsto (fun y : EuclideanSpace ℝ (Fin d) =>
      (‖y‖ / 2) ^ ((2 : ℝ) - d)) (Bornology.cobounded _) (nhds 0) := by
    have hpos : 0 < (d : ℝ) - 2 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    simpa only [neg_sub, Function.comp_def] using (tendsto_rpow_neg_atTop hpos).comp ht
  have hlim : Tendsto (fun y : EuclideanSpace ℝ (Fin d) =>
      volume.real E * (‖y‖ / 2) ^ ((2 : ℝ) - d) / b)
      (Bornology.cobounded _) (nhds 0) := by
    simpa only [mul_zero, zero_div] using
      (tendsto_const_nhds.mul hp).div_const b
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall (fun y =>
      show 0 ≤ curvatureIntegral E y from integral_nonneg (fun v =>
        div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)))
  · filter_upwards [eventually_cobounded_le_norm (2 * R)] with y hy
    have hhalf : b ≤ ‖y‖ / 2 := by linarith
    have hband' : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ ‖y‖ / 2 := by
      intro v hv
      exact ⟨(hband v hv).1, (hband v hv).2.trans (by linarith)⟩
    have he := curvatureIntegral_le_far_point hd hb hhalf hE hband' y (by linarith)
    simpa only [mul_div_assoc] using he

/-- The actual inward-drift potential of a bounded radial band decays at infinity. -/
theorem tendsto_potential_cobounded {d : ℕ} (hd : 2 ≤ d)
    {ε b R : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) (hR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) :
    Filter.Tendsto (CERW.potential d ε E)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin d))) (nhds (0 : ℝ)) := by
  have hfin := band_measure_ne_top (fun v hv => (hband v hv).2)
  have hc : 0 ≤ 2 * ε / unitBallVolume d :=
    div_nonneg (mul_nonneg (by norm_num) hε) (unitBallVolume_pos d).le
  have ht : Tendsto (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ / 2)
      (Bornology.cobounded _) atTop :=
    tendsto_norm_cobounded_atTop.atTop_div_const (by norm_num)
  have hlim : Tendsto (fun y : EuclideanSpace ℝ (Fin d) =>
      (2 * ε / unitBallVolume d) * ((volume E).toReal / (‖y‖ / 2)))
      (Bornology.cobounded _) (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_const_nhds.div_atTop ht)
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_cobounded_le_norm (max (2 * R) 2)] with y hy
  have hyR : 2 * R ≤ ‖y‖ := (le_max_left _ _).trans hy
  have hy1 : 1 ≤ ‖y‖ / 2 := by linarith [(le_max_right (2 * R) 2).trans hy]
  have hbd : ∀ v ∈ E,
      ‖inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d‖ ≤ 1 / (‖y‖ / 2) := by
    intro v hv
    have hsep : ‖y‖ / 2 ≤ ‖v - y‖ := by
      have hn := norm_sub_norm_le y v
      rw [norm_sub_rev y v] at hn
      linarith [(hband v hv).2]
    have hw1 : 1 ≤ ‖v - y‖ := hy1.trans hsep
    have hw : 0 < ‖v - y‖ := lt_of_lt_of_le zero_lt_one hw1
    have hn := CERW.Support.Geometry.abs_potentialIntegrand_le v y
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖v - y‖ ^ (1 - (d : ℝ)) := hn
      _ = ‖v - y‖ / ‖v - y‖ ^ d :=
        (CERW.Support.Geometry.div_pow_eq_rpow_sub hw d).symm
      _ ≤ 1 / (‖y‖ / 2) := by
        rw [div_le_div_iff₀ (pow_pos hw d) (by linarith : 0 < ‖y‖ / 2)]
        calc
          ‖v - y‖ * (‖y‖ / 2) ≤ ‖v - y‖ * ‖v - y‖ :=
            mul_le_mul_of_nonneg_left hsep hw.le
          _ = ‖v - y‖ ^ 2 := (pow_two _).symm
          _ ≤ 1 * ‖v - y‖ ^ d := by
            rw [one_mul]
            exact pow_le_pow_right₀ hw1 hd
  have hi := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) hfin.lt_top
    (ae_restrict_of_forall_mem hE hbd)
  change ‖(2 * ε / unitBallVolume d) *
    (∫ v in E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    _ ≤ (1 / (‖y‖ / 2)) * volume.real E := hi
    _ = (volume E).toReal / (‖y‖ / 2) := by rw [Measure.real]; ring

end CERW.LimitShapes.Curvature
