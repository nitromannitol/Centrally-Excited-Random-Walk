module

public import CERW.Support.Outer.Radius.ProbeGeometry

@[expose] public section

/-!
# Cap Mass

Cap bounds control local exterior mass at all larger scales. Layer-cake integration expresses radial
power integrals in terms of these mass bounds.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

section

open CERW.Generic.Kernel CERW.Support.Geometry

/-- A ball of radius `t ≥ w` meets `E` in at most `3^{d-1}` times the cap bound. -/
theorem local_mass_of_cap (hd : 1 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    {b w lam : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w}) (hlam : 0 ≤ lam)
    (hcap : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
      volume (E ∩ Metric.ball (((b + w) : ℝ) • u) t) ≤ ENNReal.ofReal (lam * t ^ (d - 1)))
    (y : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : w ≤ t) (ht0 : 0 < t) :
    (volume (E ∩ Metric.ball y t)).toReal ≤ lam * 3 ^ (d - 1) * t ^ (d - 1) := by
  by_cases hne : (E ∩ Metric.ball y t).Nonempty
  · obtain ⟨v, hvE, hvB⟩ := hne
    obtain ⟨hb1, hb2⟩ := hsub hvE
    obtain ⟨u, hu, huv⟩ : ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧ ‖v - (b + w) • u‖ ≤ w := by
      by_cases hv0 : v = 0
      · haveI : NeZero d := ⟨by omega⟩
        obtain ⟨u, hu⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin d)) zero_le_one
        refine ⟨u, hu, ?_⟩
        rw [hv0, norm_zero] at hb1
        rw [hv0, zero_sub, norm_neg, norm_smul, hu, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (by rw [hv0, norm_zero] at hb2; exact hb2)]
        linarith
      · have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv0
        refine ⟨unitDir v, ?_, ?_⟩
        · rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
        · have h1 : v = ‖v‖ • unitDir v := by
            rw [unitDir, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
          have h2 : ‖unitDir v‖ = 1 := by
            rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
          have h3 : v - (b + w) • unitDir v = (‖v‖ - (b + w)) • unitDir v := by
            rw [sub_smul, ← h1]
          rw [h3, norm_smul, h2, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          linarith
    have hball : Metric.ball y t ⊆ Metric.ball (((b + w) : ℝ) • u) (3 * t) := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      rw [Metric.mem_ball, dist_eq_norm] at hvB
      calc ‖z - (b + w) • u‖ = ‖(z - y) + (y - v) + (v - (b + w) • u)‖ := by
            congr 1
            abel
        _ ≤ ‖(z - y) + (y - v)‖ + ‖v - (b + w) • u‖ := norm_add_le _ _
        _ ≤ ‖z - y‖ + ‖y - v‖ + ‖v - (b + w) • u‖ := by
            gcongr
            exact norm_add_le _ _
        _ < 3 * t := by
            rw [norm_sub_rev y v]
            linarith
    have hvol : volume (E ∩ Metric.ball y t) ≤ ENNReal.ofReal (lam * (3 * t) ^ (d - 1)) :=
      (measure_mono (Set.inter_subset_inter_right E hball)).trans
        (hcap u hu (3 * t) (by linarith))
    calc (volume (E ∩ Metric.ball y t)).toReal
        ≤ (ENNReal.ofReal (lam * (3 * t) ^ (d - 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
      _ = lam * (3 * t) ^ (d - 1) := ENNReal.toReal_ofReal (by positivity)
      _ = lam * 3 ^ (d - 1) * t ^ (d - 1) := by rw [mul_pow]; ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty, ENNReal.toReal_zero]
    positivity

end

/-- The volume of a ball of radius `t ≥ 0` is `ω_d t^d`. -/
lemma gmb_volume_ball (hd : 1 ≤ d) (y : EuclideanSpace ℝ (Fin d)) {t : ℝ}
    (ht : 0 ≤ t) :
    volume (Metric.ball y t) = ENNReal.ofReal (unitBallVolume d * t ^ d) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [Measure.addHaar_ball volume y ht, finrank_euclideanSpace_fin, unitBallVolume,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    mul_comm]

/-- The tail integral `(d-2) ∫_r^∞ t^{1-d} dt = r^{2-d}`. -/
lemma gmb_lintegral_tail (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    ∫⁻ t in Set.Ioi r, ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) =
      ENNReal.ofReal (r ^ (2 - (d : ℝ))) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : (1 - (d : ℝ)) < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => t ^ (1 - (d : ℝ))) (Set.Ioi r) :=
    integrableOn_Ioi_rpow_of_lt ha hr
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hr]
    congr 1
    have h1 : (1 - (d : ℝ)) + 1 = 2 - d := by ring
    rw [h1]
    have h2 : (2 - (d : ℝ)) ≠ 0 := by linarith
    field_simp
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (hr.le.trans ht.le) _)

/-- Layer-cake formula (as an inequality): `∫_E |v-y|^{2-d} ≤ (d-2) ∫_0^∞ |E ∩ B(y,t)| t^{1-d} dt`,
in `[0, ∞]`-valued integrals. -/
lemma gmb_layer_cake (hd : 3 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (y : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ))) ≤
      ∫⁻ t, ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) *
        volume (E ∩ Metric.ball y t) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) with hf
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul (measurable_id.pow_const _)
  set G : EuclideanSpace ℝ (Fin d) → ℝ → ENNReal :=
    fun v t => if ‖v - y‖ < t then f t else 0 with hG
  have hGm : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {q : EuclideanSpace ℝ (Fin d) × ℝ | ‖q.1 - y‖ < q.2} :=
      measurableSet_lt ((measurable_fst.sub_const y).norm) measurable_snd
    exact Measurable.ite hS (hfm.comp measurable_snd) measurable_const
  have h1 : ∀ v, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ))) ≤ ∫⁻ t, G v t := by
    intro v
    by_cases hv : v = y
    · subst hv
      have h2 : (2 - (d : ℝ)) ≠ 0 := by linarith
      simp [Real.zero_rpow h2]
    · have hr : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
      have hvt : (fun t => G v t) = (Set.Ioi ‖v - y‖).indicator f := by
        funext t
        simp [hG, Set.indicator]
      rw [hvt, lintegral_indicator measurableSet_Ioi, hf, gmb_lintegral_tail hd hr]
  calc ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ)))
      ≤ ∫⁻ v in E, ∫⁻ t, G v t := lintegral_mono h1
    _ = ∫⁻ t, ∫⁻ v in E, G v t := lintegral_lintegral_swap hGm.aemeasurable
    _ = ∫⁻ t, f t * volume (E ∩ Metric.ball y t) := by
        congr 1
        funext t
        have hvt : (fun v => G v t) = (Metric.ball y t).indicator (fun _ => f t) := by
          funext v
          simp [hG, Set.indicator, dist_eq_norm]
        rw [hvt, lintegral_indicator_const Metric.isOpen_ball.measurableSet,
          Measure.restrict_apply' hE, Set.inter_comm]

/-- For `t > 0`, `t^{1-d} t^d = t`. -/
lemma gmb_rpow_mul_pow (d : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ (1 - (d : ℝ)) * t ^ d = t := by
  rw [← Real.rpow_natCast t d, ← Real.rpow_add ht]
  simp

/-- For `t > 0` and `d ≥ 1`, `t^{1-d} t^{d-1} = 1`. -/
lemma gmb_rpow_mul_pow_pred (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    t ^ (1 - (d : ℝ)) * t ^ (d - 1) = 1 := by
  rw [← Real.rpow_natCast t (d - 1), ← Real.rpow_add ht, Nat.cast_sub hd]
  simp

end CERW.Support.Outer.Radius
