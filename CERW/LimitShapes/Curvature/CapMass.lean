import CERW.LimitShapes.Curvature.Mass

/-!
# Integrated outer cap mass

The negative cap kernel and positive curvature bound give `eq:outer-cap-mass`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The explicit integrated outer cap estimate in `eq:outer-cap-mass`. -/
theorem cap_measure_le_of_curvature {d : ℕ} (hd : 2 ≤ d)
    {ε b A t delta F₀ : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hbA : b ≤ A) (ht : 0 < t) (htA : t ≤ A / 2)
    (hdelta : 0 ≤ delta) (hF : 0 ≤ F₀)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ A)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (hpotential : -delta ≤ CERW.potential d ε E ((A + 4 * t) • u))
    (hcurvature : curvatureIntegral E ((A + 4 * t) • u) ≤ F₀) :
    volume.real (E ∩ Metric.ball (A • u) t) ≤
      (5 : ℝ) ^ d * (CERW.unitBallVolume d / (2 * ε) * delta + F₀ / 2) *
        t ^ (d - 1) := by
  haveI : NeZero d := ⟨by omega⟩
  have hA : 0 < A := hb.trans_le hbA
  let y := (A + 4 * t) • u
  let B := Metric.ball (A • u) t
  let f := fun v => inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d
  let c : ℝ := (1 / (5 : ℝ) ^ d) * t ^ ((1 : ℝ) - d)
  have hc : 0 < c := by dsimp [c]; positivity
  have hfin := band_measure_ne_top (fun v hv => (hband v hv).2)
  have hi : IntegrableOn f E :=
    CERW.Support.Geometry.integrableOn_potentialIntegrand (by omega) hE hfin y
  have hB : MeasurableSet B := measurableSet_ball
  have hcap : ∫ v in E ∩ B, f v ≤ volume.real (E ∩ B) * (-c) := by
    rw [← smul_eq_mul, ← setIntegral_const]
    apply integral_mono_ae (hi.mono_set Set.inter_subset_left)
      (integrableOn_const (C := -c)
        (band_measure_ne_top (fun v hv => (hband v hv.1).2)))
    · apply ae_restrict_of_forall_mem (hE.inter hB)
      intro v hv
      simpa only [f, y, c, neg_mul] using
        cap_kernel_le v u A t hA ht htA hu (hband v hv.1).2
        (by simpa only [Metric.mem_ball, dist_eq_norm] using hv.2.le)
  have hip : IntegrableOn (fun v => max (f v) 0) E := hi.pos_part
  have hrest : ∫ v in E \ B, f v ≤ ∫ v in E, max (f v) 0 := by
    calc
      _ ≤ ∫ v in E \ B, max (f v) 0 := by
        apply integral_mono_ae (hi.mono_set Set.sdiff_subset)
          (hip.mono_set Set.sdiff_subset)
        exact Filter.Eventually.of_forall (fun v => le_max_left _ _)
      _ ≤ _ := setIntegral_mono_set hip
        (Filter.Eventually.of_forall (fun v => le_max_right _ _))
        (Filter.Eventually.of_forall (fun v hv => hv.1))
  have hsum := integral_inter_add_sdiff hB hi
  have hraw : c * volume.real (E ∩ B) ≤
      (∫ v in E, max (f v) 0) - ∫ v in E, f v := by
    linarith
  have hω := unitBallVolume_pos d
  have hk : 0 < 2 * ε / unitBallVolume d := by positivity
  have hy : A ≤ ‖y‖ := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hu, mul_one]
    linarith
  have hp := positivePotential_le_curvatureIntegral hd hε.le hb hbA hE hband y hy
  have hpF : 2 * ε / unitBallVolume d * (∫ v in E, max (f v) 0) ≤
      ε / unitBallVolume d * F₀ := by
    exact hp.trans (mul_le_mul_of_nonneg_left hcurvature (by positivity))
  have hl : -delta ≤ 2 * ε / unitBallVolume d * ∫ v in E, f v := hpotential
  have hscaled := mul_le_mul_of_nonneg_left hraw hk.le
  have hbound : c * volume.real (E ∩ B) ≤
      unitBallVolume d / (2 * ε) * delta + F₀ / 2 := by
    apply le_of_mul_le_mul_left (a := 2 * ε / unitBallVolume d) _ hk
    have heq : 2 * ε / unitBallVolume d *
        (unitBallVolume d / (2 * ε) * delta + F₀ / 2) =
        delta + ε / unitBallVolume d * F₀ := by
      field_simp
    rw [heq]
    nlinarith [hscaled]
  have hcp : c * ((5 : ℝ) ^ d * t ^ (d - 1)) = 1 := by
    dsimp [c]
    rw [show (1 : ℝ) - d = -((d - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring,
      Real.rpow_neg ht.le, Real.rpow_natCast]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hbound
    (show 0 ≤ (5 : ℝ) ^ d * t ^ (d - 1) by positivity)
  have _ := hdelta
  have _ := hF
  calc
    volume.real (E ∩ Metric.ball (A • u) t) =
        c * volume.real (E ∩ B) * ((5 : ℝ) ^ d * t ^ (d - 1)) := by
      rw [mul_right_comm c, hcp, one_mul]
    _ ≤ _ := hmul
    _ = _ := by ring

end CERW.LimitShapes.Curvature
