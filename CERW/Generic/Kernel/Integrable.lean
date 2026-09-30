import CERW.Generic.Kernel.Bathtub
import CERW.Model.Potential
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Integrability of the Newtonian field

The field `|v - y|^{1-d}` is integrable on every ball, with `∫_{B(y,ρ)} |v - y|^{1-d} = σ_d ρ`
where `σ_d = d ω_d`. By the bathtub principle its integral over any measurable set of volume `R`
is at most `σ_d (R/ω_d)^{1/d}`, uniformly in `y`. This is the bound behind `eq:potential-bound`
and `eq:packing`, and it is the Fubini hypothesis of `eq:newton`.
-/

namespace CERW.Generic.Kernel

open MeasureTheory CERW

variable {d : ℕ}

/-- The radial weight `t^(d-1)` of polar coordinates cancels the kernel `t^(1-d)` for `t > 0`. -/
theorem pow_smul_rpow_one_sub (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    t ^ (d - 1) • t ^ (1 - (d : ℝ)) = 1 := by
  rw [smul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_add ht, Nat.cast_sub hd]
  simp

/-- Integrability and the value of the integral of `|v|^{1-d}` over a ball centred at `0`. -/
theorem integrableOn_ball_zero_and_integral_eq (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
        (Metric.ball 0 ρ) ∧
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ, ‖v‖ ^ (1 - (d : ℝ))
        = d * unitBallVolume d * ρ := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hcancel : ∀ t ∈ Set.Ioo (0 : ℝ) ρ,
      t ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) • t ^ (1 - (d : ℝ)) = 1 := by
    intro t ht
    rw [hfin]
    exact pow_smul_rpow_one_sub hd ht.1
  refine ⟨?_, ?_⟩
  · rw [integrableOn_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (f := fun t : ℝ => t ^ (1 - (d : ℝ)))]
    refine (integrableOn_const (μ := volume) (by simp) (C := (1 : ℝ))).congr_fun
      (fun t ht => (hcancel t ht).symm) measurableSet_Ioo
  · have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ).indicator
        (fun v => ‖v‖ ^ (1 - (d : ℝ)))
        = fun v => (Set.Iio ρ).indicator (fun t : ℝ => t ^ (1 - (d : ℝ))) ‖v‖ := by
      funext v
      by_cases hv : ‖v‖ < ρ <;> simp [Set.indicator, hv]
    rw [← integral_indicator Metric.isOpen_ball.measurableSet, hind,
      integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))), hfin]
    have hrad : ∫ t in Set.Ioi (0 : ℝ),
        t ^ (d - 1) • (Set.Iio ρ).indicator (fun t : ℝ => t ^ (1 - (d : ℝ))) t = ρ := by
      have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
          t ^ (d - 1) • (Set.Iio ρ).indicator (fun t : ℝ => t ^ (1 - (d : ℝ))) t
            = (Set.Iio ρ).indicator (fun _ => (1 : ℝ)) t := by
        intro t ht
        by_cases htρ : t < ρ
        · simp only [Set.indicator_of_mem (Set.mem_Iio.mpr htρ)]
          exact pow_smul_rpow_one_sub hd ht
        · simp [Set.indicator_of_notMem (mt Set.mem_Iio.mp htρ)]
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
        setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
      simp [hρ.le]
    rw [hrad]
    simp only [unitBallVolume, Measure.real, nsmul_eq_mul, smul_eq_mul]
    ring

/-- Translating by `y` carries the ball `B(0, ρ)` to the ball `B(y, ρ)`. -/
theorem ball_eq_preimage_sub (y : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) :
    Metric.ball y ρ = (fun v : EuclideanSpace ℝ (Fin d) => v - y) ⁻¹' Metric.ball 0 ρ := by
  ext v
  simp only [Set.mem_preimage, mem_ball_iff_norm, sub_zero]

/-- For `d ≥ 1` and `ρ > 0`, `|v - y|^{1-d}` is integrable on `B(y, ρ)` with integral
`d ω_d ρ`. -/
theorem integrableOn_ball_and_integral_eq (hd : 1 ≤ d) (y : EuclideanSpace ℝ (Fin d)) {ρ : ℝ}
    (hρ : 0 < ρ) :
    IntegrableOn (fun v => ‖v - y‖ ^ (1 - (d : ℝ))) (Metric.ball y ρ) ∧
      ∫ v in Metric.ball y ρ, ‖v - y‖ ^ (1 - (d : ℝ)) = d * unitBallVolume d * ρ := by
  obtain ⟨hint, hval⟩ := integrableOn_ball_zero_and_integral_eq (d := d) hd hρ
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) y
  have hemb := measurableEmbedding_subRight y
  rw [ball_eq_preimage_sub]
  refine ⟨?_, ?_⟩
  · exact (hmp.integrableOn_comp_preimage hemb (f := fun v => ‖v‖ ^ (1 - (d : ℝ)))).mpr hint
  · rw [hmp.setIntegral_preimage_emb hemb (fun v => ‖v‖ ^ (1 - (d : ℝ))), hval]

/-- For `d ≥ 1` and a measurable set `D` of finite volume, `|v - y|^{1-d}` is integrable on `D`
and `∫_D |v - y|^{1-d} ≤ d ω_d (|D| / ω_d)^{1/d}`, uniformly in `y`. -/
theorem integrableOn_and_setIntegral_le (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => ‖v - y‖ ^ (1 - (d : ℝ))) D ∧
      ∫ v in D, ‖v - y‖ ^ (1 - (d : ℝ))
        ≤ d * unitBallVolume d * ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d) := by
  haveI : NeZero d := ⟨by omega⟩
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rcases eq_or_ne (volume D) 0 with h0 | h0
  · have hzero : volume.restrict D = 0 := Measure.restrict_eq_zero.mpr h0
    refine ⟨by rw [IntegrableOn, hzero]; exact integrable_zero_measure, ?_⟩
    rw [hzero, integral_zero_measure, h0]
    simp only [ENNReal.toReal_zero, zero_div]
    rw [Real.zero_rpow (by positivity)]
    simp
  · set ρ : ℝ := ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d) with hρdef
    have hvpos : 0 < (volume D).toReal := ENNReal.toReal_pos h0 hDfin
    have hρ : 0 < ρ := Real.rpow_pos_of_pos (div_pos hvpos hω) _
    have hρpow : ρ ^ d = (volume D).toReal / unitBallVolume d := by
      rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hvpos hω).le]
      simp [hd0.ne']
    have hvol : volume D = volume (Metric.ball y ρ) := by
      rw [Measure.addHaar_ball_of_pos volume y hρ, finrank_euclideanSpace_fin]
      have hball : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))
          = ENNReal.ofReal (unitBallVolume d) := by
        rw [unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
      rw [hball, ← ENNReal.ofReal_mul (by positivity), hρpow, div_mul_cancel₀ _ hω.ne',
        ENNReal.ofReal_toReal hDfin]
    obtain ⟨hint, hval⟩ := integrableOn_ball_and_integral_eq hd y hρ
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hanti : AntitoneOn (fun t : ℝ => t ^ (1 - (d : ℝ))) (Set.Ioi 0) := by
      intro a ha b _ hab
      exact Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
    obtain ⟨hintD, hle⟩ := setIntegral_le_ball_of_antitoneOn hanti
      (fun t ht => Real.rpow_nonneg ht.le _) hD y hρ hvol hint
    exact ⟨hintD, hle.trans_eq hval⟩

end CERW.Generic.Kernel
