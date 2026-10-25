module

public import CERW.LimitShapes.Curvature.CapKernel
public import CERW.Generic.Kernel.RadialPower
public import CERW.Support.Geometry.Bound

@[expose] public section

/-!
# Integrated contact and curvature bounds

The contact sign gives the mass comparison in `eq:mass`; the positive part of the
potential is controlled by the curvature integral in `eq:curvature-size`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The curvature integral in `eq:curvature-size`. -/
noncomputable def curvatureIntegral {d : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ v in E, ‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖

/-- The potential with its kernel replaced by its positive part. -/
noncomputable def positivePotential (d : ℕ) (ε : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * ε / CERW.unitBallVolume d *
    ∫ v in E, max (inner ℝ (CERW.unitDir v) (v - y) / ‖v - y‖ ^ d) 0

/-- A set in a bounded radial band has finite volume. -/
lemma band_measure_ne_top {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))} {R : ℝ}
    (hE : ∀ v ∈ E, ‖v‖ ≤ R) : volume E ≠ ⊤ := by
  apply (lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 R) ?_)
    measure_closedBall_lt_top).ne
  intro v hv
  simpa only [Metric.mem_closedBall, dist_zero_right] using hE v hv

/-- The curvature kernel is integrable on a bounded set separated from the origin. -/
lemma integrableOn_curvature {d : ℕ} (hd : 2 ≤ d) {b R : ℝ} (hb : 0 < b)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => ‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖) E := by
  by_cases hempty : E.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hempty]
    simp only [IntegrableOn, Measure.restrict_empty]
    exact integrable_zero_measure
  obtain ⟨v, hv⟩ := hempty
  have hρ : 0 < R + ‖y‖ + 1 := by
    linarith [(hband v hv).1, (hband v hv).2, norm_nonneg y]
  have hint := (Generic.Kernel.integrableOn_ball_rpow_neg_and_integral_eq
    (d := d) (by omega) (s := (d : ℝ) - 2) (by linarith) hρ).1
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) y
  have htrans := (hmp.integrableOn_comp_preimage (measurableEmbedding_subRight y)
    (f := fun v => ‖v‖ ^ (-((d : ℝ) - 2)))).mpr hint
  have hsub : E ⊆ (fun v => v - y) ⁻¹' Metric.ball 0 (R + ‖y‖ + 1) := by
    intro v hv
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    linarith [norm_sub_le v y, (hband v hv).2]
  have hi : IntegrableOn (fun v => ‖v - y‖ ^ ((2 : ℝ) - d)) E := by
    simpa only [neg_sub, Function.comp_def] using htrans.mono_set hsub
  have hm : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖⁻¹)
      (volume.restrict E) := by fun_prop
  have hw : ∀ᵐ v ∂volume.restrict E, ‖‖v‖⁻¹‖ ≤ b⁻¹ := by
    apply ae_restrict_of_forall_mem hE
    intro v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_anti₀ hb (hband v hv).1
  simpa only [IntegrableOn, div_eq_mul_inv] using hi.mul_bdd hm hw

/-- Integrating the contact sign gives the mass bound in `eq:mass`. -/
theorem measure_le_contact_potential {d : ℕ} (hd : 2 ≤ d)
    {ε b R : ℝ} (hε : 0 < ε) (hb : 0 < b) (hR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ = b) :
    volume.real E ≤ (CERW.unitBallVolume d / (2 * ε)) *
      (2 : ℝ) ^ (d - 1) * R ^ (d - 1) * CERW.potential d ε E y := by
  haveI : NeZero d := ⟨by omega⟩
  have hRp : 0 < R := hb.trans_le hR
  let C : ℝ := (2 : ℝ) ^ (d - 1) * R ^ (d - 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hfin := band_measure_ne_top (fun v hv => (hband v hv).2)
  have hi := CERW.Support.Geometry.integrableOn_potentialIntegrand (by omega) hE hfin y
  have hne : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ y := by
    rw [ae_iff]; simp
  have hl : ∀ᵐ v ∂volume.restrict E,
      1 ≤ C * (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) := by
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem hE] with v hvy hvE
    have hvp : 0 < ‖v‖ := hb.trans_le (hband v hvE).1
    have hr : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvy)
    have hs := Generic.Kernel.sq_div_le_inner_unitDir_sub
      (norm_pos_iff.mp hvp) (by rw [hy]; exact (hband v hvE).1)
    have hn : ‖v - y‖ ≤ 2 * R := by
      linarith [norm_sub_le v y, (hband v hvE).2]
    have hp := Real.rpow_le_rpow_of_nonpos hr hn
      (show (2 : ℝ) - d ≤ 0 by exact_mod_cast (show (2 : ℤ) - d ≤ 0 by omega))
    have hk : (2 * R) ^ ((2 : ℝ) - d) / (2 * R) ≤
        inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := by
      calc
        _ ≤ ‖v - y‖ ^ ((2 : ℝ) - d) / (2 * R) :=
          div_le_div_of_nonneg_right hp (by positivity)
        _ ≤ ‖v - y‖ ^ ((2 : ℝ) - d) / (2 * ‖v‖) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left (hband v hvE).2 (by norm_num))
        _ = (‖v - y‖ ^ 2 / (2 * ‖v‖)) / ‖v - y‖ ^ d := by
          rw [Real.rpow_sub hr, Real.rpow_two, Real.rpow_natCast]; ring
        _ ≤ _ := div_le_div_of_nonneg_right hs (by positivity)
    have heq : (2 * R) ^ ((2 : ℝ) - d) / (2 * R) = C⁻¹ := by
      rw [show (2 : ℝ) - d = 1 - ((d - 1 : ℕ) : ℝ) by
        rw [Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring,
        Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_natCast]
      dsimp [C]
      rw [mul_pow]
      field_simp
    rw [heq] at hk
    have := mul_le_mul_of_nonneg_left hk hC.le
    simpa only [mul_inv_cancel₀ hC.ne'] using this
  have hint := integral_mono_ae (integrableOn_const (C := (1 : ℝ)) hfin) (hi.const_mul C) hl
  rw [integral_const, smul_eq_mul, mul_one, integral_const_mul] at hint
  have hω := unitBallVolume_pos d
  unfold potential
  have heq : unitBallVolume d / (2 * ε) * (2 : ℝ) ^ (d - 1) *
      R ^ (d - 1) * (2 * ε / unitBallVolume d *
        ∫ v in E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) =
      C * ∫ v in E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := by
    dsimp [C]
    field_simp [hω.ne', hε.ne']
  rw [heq]
  simpa only [Measure.real, Measure.restrict_apply_univ] using hint

/-- Integrating the positive kernel bound proves `eq:curvature-size`. -/
theorem positivePotential_le_curvatureIntegral {d : ℕ} (hd : 2 ≤ d)
    {ε b R : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) (hR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (y : EuclideanSpace ℝ (Fin d)) (hy : R ≤ ‖y‖) :
    positivePotential d ε E y ≤ ε / CERW.unitBallVolume d * curvatureIntegral E y := by
  haveI : NeZero d := ⟨by omega⟩
  have _hR := hR
  have hfin := band_measure_ne_top (fun v hv => (hband v hv).2)
  have hi := CERW.Support.Geometry.integrableOn_potentialIntegrand (by omega) hE hfin y
  have hc := integrableOn_curvature hd hb hE hband y
  have hne : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ y := by
    rw [ae_iff]; simp
  have hle := integral_mono_ae hi.pos_part (hc.div_const 2) (by
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem hE] with v hvy hv
    exact positive_kernel_le_curvature hd v y
      (norm_pos_iff.mp (hb.trans_le (hband v hv).1)) hvy ((hband v hv).2.trans hy))
  rw [integral_div] at hle
  have hω := unitBallVolume_pos d
  have h := mul_le_mul_of_nonneg_left hle
    (show 0 ≤ 2 * ε / unitBallVolume d by positivity)
  unfold positivePotential curvatureIntegral
  calc
    _ ≤ (2 * ε / unitBallVolume d) *
        ((∫ v in E, ‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖) / 2) := h
    _ = _ := by ring

end CERW.LimitShapes.Curvature
