import CERW.Model.Potential
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmic radial integrals

The two norm powers in the Hölder step of `eq:direction-error` are logarithmic. In polar
coordinates, `∫_{B(0,R)} (1 + |v|)^{-d} ≤ σ_d log(1 + R)` because `t^{d-1} ≤ (1 + t)^{d-1}`,
and `∫_{ρ ≤ |v| < R} |v|^{-d} = σ_d log(R/ρ)`, where `σ_d = d ω_d`.
-/

namespace CERW.Generic.Kernel

open MeasureTheory CERW

variable {d : ℕ}

/-- For `t > 0` the radial weight dominates the logarithmic integrand:
`t^(d-1) * (1 + t)^(-d) ≤ (1 + t)⁻¹`. -/
theorem pow_mul_rpow_one_add_le_inv (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    t ^ (d - 1) * (1 + t) ^ (-(d : ℝ)) ≤ (1 + t)⁻¹ := by
  have hbase : (0 : ℝ) < 1 + t := by linarith
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
  have hmono : t ^ (d - 1) ≤ (1 + t) ^ (d - 1) :=
    pow_le_pow_left₀ ht.le (by linarith) (d - 1)
  calc
    t ^ (d - 1) * (1 + t) ^ (-(d : ℝ))
        ≤ (1 + t) ^ (d - 1) * (1 + t) ^ (-(d : ℝ)) :=
          mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hbase.le _)
    _ = (1 + t) ^ (((d - 1 : ℕ) : ℝ) + (-(d : ℝ))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hbase]
    _ = (1 + t) ^ (-1 : ℝ) := by
          congr 1
          rw [hcast]
          ring
    _ = (1 + t)⁻¹ := Real.rpow_neg_one _

/-- On the annulus `ρ ≤ t < R` the polar weight `t^(d-1)` cancels `t^(-d)`, leaving `t⁻¹`. -/
theorem indicator_Ico_mul_rpow_neg_eq (hd : 1 ≤ d) {ρ R : ℝ} (hρ : 0 < ρ) :
    (fun t : ℝ => t ^ (d - 1) •
        (Set.Ico ρ R).indicator (fun t : ℝ => t ^ (-(d : ℝ))) t)
      = (Set.Ico ρ R).indicator (fun t : ℝ => t⁻¹) := by
  funext t
  by_cases ht : t ∈ Set.Ico ρ R
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul,
      ← Real.rpow_natCast, ← Real.rpow_add (lt_of_lt_of_le hρ ht.1)]
    rw [Nat.cast_sub hd, Nat.cast_one,
      show (d : ℝ) - 1 + -(d : ℝ) = -1 by ring, Real.rpow_neg_one]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]

/-- `(1 + |v|)^{-d}` is integrable on `B(0, R)` with integral at most `σ_d log(1 + R)`. -/
theorem integrableOn_ball_one_add_norm_rpow_and_integral_le (hd : 1 ≤ d) {R : ℝ}
    (hR : 0 < R) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => (1 + ‖v‖) ^ (-(d : ℝ)))
        (Metric.ball 0 R) ∧
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R, (1 + ‖v‖) ^ (-(d : ℝ))
        ≤ d * unitBallVolume d * Real.log (1 + R) := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hω := unitBallVolume_pos d
  have hradInt : IntegrableOn (fun t : ℝ => t ^ (d - 1) • (1 + t) ^ (-(d : ℝ)))
      (Set.Ioo (0 : ℝ) R) := by
    have hcont : ContinuousOn (fun t : ℝ => t ^ (d - 1) • (1 + t) ^ (-(d : ℝ)))
        (Set.Icc (0 : ℝ) R) := by
      refine ContinuousOn.smul (continuousOn_id.pow (d - 1)) ?_
      exact ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
        (fun t ht => Or.inl (by linarith [ht.1]))
    exact (hcont.integrableOn_Icc (μ := volume)).mono_set Set.Ioo_subset_Icc_self
  have hballInt : IntegrableOn
      (fun v : EuclideanSpace ℝ (Fin d) => (1 + ‖v‖) ^ (-(d : ℝ)))
      (Metric.ball 0 R) := by
    rw [integrableOn_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (f := fun t : ℝ => (1 + t) ^ (-(d : ℝ))), hfin]
    exact hradInt
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R).indicator
        (fun v => (1 + ‖v‖) ^ (-(d : ℝ)))
        = fun v => (Set.Iio R).indicator (fun t : ℝ => (1 + t) ^ (-(d : ℝ))) ‖v‖ := by
    funext v
    by_cases hv : ‖v‖ < R <;> simp [Set.indicator, hv]
  have hgint : Integrable ((Set.Ioo (0 : ℝ) R).indicator (fun t : ℝ => (1 + t)⁻¹))
      volume := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    have hcont : ContinuousOn (fun t : ℝ => (1 + t) ^ (-1 : ℝ)) (Set.Icc (0 : ℝ) R) :=
      ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
        (fun t ht => Or.inl (by linarith [ht.1]))
    have hint : IntegrableOn (fun t : ℝ => (1 + t) ^ (-1 : ℝ)) (Set.Ioo (0 : ℝ) R) :=
      (hcont.integrableOn_Icc (μ := volume)).mono_set Set.Ioo_subset_Icc_self
    simpa only [Real.rpow_neg_one] using hint
  have hf_nonneg : 0 ≤ᵐ[volume] (Set.Ioi (0 : ℝ)).indicator
      (fun t : ℝ => t ^ (d - 1) • (Set.Iio R).indicator
        (fun t : ℝ => (1 + t) ^ (-(d : ℝ))) t) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · by_cases htR : t < R
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (Set.mem_Iio.mpr htR), smul_eq_mul]
        exact mul_nonneg (pow_nonneg (Set.mem_Ioi.mp ht).le _)
          (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) _)
      · rw [Set.indicator_of_mem ht]
        simp [Set.indicator, htR]
    · simp [Set.indicator, ht]
  have hpt : (Set.Ioi (0 : ℝ)).indicator
        (fun t : ℝ => t ^ (d - 1) • (Set.Iio R).indicator
          (fun t : ℝ => (1 + t) ^ (-(d : ℝ))) t)
      ≤ (Set.Ioo (0 : ℝ) R).indicator (fun t : ℝ => (1 + t)⁻¹) := by
    intro t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · by_cases htR : t < R
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ht, htR⟩),
          Set.indicator_of_mem (Set.mem_Iio.mpr htR), smul_eq_mul]
        exact pow_mul_rpow_one_add_le_inv hd ht
      · rw [Set.indicator_of_mem ht]
        simp [Set.indicator, htR]
    · have ht' : t ∉ Set.Ioo (0 : ℝ) R := fun h => ht h.1
      simp [Set.indicator, ht, ht']
  have hbound : ∫ t in Set.Ioi (0 : ℝ),
        t ^ (d - 1) • (Set.Iio R).indicator (fun t : ℝ => (1 + t) ^ (-(d : ℝ))) t
      ≤ Real.log (1 + R) := by
    calc
      ∫ t in Set.Ioi (0 : ℝ),
          t ^ (d - 1) • (Set.Iio R).indicator (fun t : ℝ => (1 + t) ^ (-(d : ℝ))) t
          = ∫ t, (Set.Ioi (0 : ℝ)).indicator
              (fun t : ℝ => t ^ (d - 1) • (Set.Iio R).indicator
                (fun t : ℝ => (1 + t) ^ (-(d : ℝ))) t) t :=
            (integral_indicator measurableSet_Ioi).symm
      _ ≤ ∫ t, (Set.Ioo (0 : ℝ) R).indicator (fun t : ℝ => (1 + t)⁻¹) t :=
            integral_mono_of_nonneg hf_nonneg hgint (Filter.Eventually.of_forall hpt)
      _ = ∫ t in Set.Ioo (0 : ℝ) R, (1 + t)⁻¹ := integral_indicator measurableSet_Ioo
      _ = Real.log (1 + R) := by
            rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
              intervalIntegral.integral_comp_add_left]
            rw [show (1 : ℝ) + 0 = 1 by ring,
              integral_inv_of_pos zero_lt_one (by linarith)]
            simp
  refine ⟨hballInt, ?_⟩
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, hind,
    integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))), hfin]
  have hC : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) = unitBallVolume d :=
    rfl
  rw [hC]
  rw [show (d : ℝ) * unitBallVolume d * Real.log (1 + R)
      = d • (unitBallVolume d • Real.log (1 + R)) by
        simp only [smul_eq_mul, nsmul_eq_mul]
        ring]
  exact smul_le_smul_of_nonneg_left (smul_le_smul_of_nonneg_left hbound hω.le)
    (Nat.zero_le d)

/-- `|v|^{-d}` is integrable on the annulus `ρ ≤ |v| < R`, with integral `σ_d log(R/ρ)`. -/
theorem integrableOn_annulus_norm_rpow_and_integral_eq (hd : 1 ≤ d) {ρ R : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ R) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (-(d : ℝ)))
        (Metric.ball 0 R \ Metric.ball 0 ρ) ∧
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R \ Metric.ball 0 ρ, ‖v‖ ^ (-(d : ℝ))
        = d * unitBallVolume d * Real.log (R / ρ) := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hR : 0 < R := lt_of_lt_of_le hρ hρR
  have hsubIoi : Set.Ico ρ R ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hρ ht.1
  have hIntRadial : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ico ρ R) := by
    have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc ρ R) :=
      continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le hρ ht.1))
    exact (hcont.integrableOn_Icc (μ := volume)).mono_set Set.Ico_subset_Icc_self
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R \ Metric.ball 0 ρ).indicator
        (fun v => ‖v‖ ^ (-(d : ℝ)))
        = fun v => (Set.Ico ρ R).indicator (fun t : ℝ => t ^ (-(d : ℝ))) ‖v‖ := by
    funext v
    by_cases hvR : ‖v‖ < R
    · by_cases hvρ : ‖v‖ < ρ
      · have hle : ¬ ρ ≤ ‖v‖ := not_le_of_gt hvρ
        simp [Set.indicator, Metric.mem_ball, dist_eq_norm, hvR, hvρ, hle]
      · have hle : ρ ≤ ‖v‖ := le_of_not_gt hvρ
        simp [Set.indicator, Metric.mem_ball, dist_eq_norm, hvR, hvρ, hle]
    · simp [Set.indicator, Metric.mem_ball, dist_eq_norm, hvR]
  have hannInt : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (-(d : ℝ)))
      (Metric.ball 0 R \ Metric.ball 0 ρ) := by
    rw [← integrable_indicator_iff (measurableSet_ball.diff measurableSet_ball), hind,
      integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))), hfin,
      indicator_Ico_mul_rpow_neg_eq hd hρ,
      integrableOn_indicator_iff measurableSet_Ico, Set.inter_eq_left.mpr hsubIoi]
    exact hIntRadial
  have hradval : ∫ t in Set.Ioi (0 : ℝ),
        t ^ (d - 1) • (Set.Ico ρ R).indicator (fun t : ℝ => t ^ (-(d : ℝ))) t
      = Real.log (R / ρ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
        (fun t _ => congr_fun (indicator_Ico_mul_rpow_neg_eq hd hρ) t),
      setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.mpr hsubIoi,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hρR, integral_inv_of_pos hρ hR]
  refine ⟨hannInt, ?_⟩
  rw [← integral_indicator (measurableSet_ball.diff measurableSet_ball), hind,
    integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))), hfin, hradval]
  have hC : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) = unitBallVolume d :=
    rfl
  rw [hC]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

end CERW.Generic.Kernel
