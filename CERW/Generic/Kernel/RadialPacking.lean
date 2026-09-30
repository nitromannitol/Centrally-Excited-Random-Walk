import CERW.Generic.Kernel.Bathtub
import CERW.Model.Potential
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# The first moment of a set is least for the centred ball

`∫_{B(0,ρ)} |v| dv = d ω_d ρ^{d+1}/(d+1)`. By the reverse bathtub principle, every measurable
set of volume `R` has `∫_D |v| ≥ (d/(d+1)) ω_d^{-1/d} R^{1+1/d}` (`eq:radial-packing`). This closes
the mass argument of `prop:coarse`.
-/

namespace CERW.Generic.Kernel

open MeasureTheory CERW

variable {d : ℕ}

/-- For `d ≥ 1` and `ρ ≥ 0`, `∫_{B(0,ρ)} |v| = d ω_d ρ^{d+1}/(d+1)`. -/
theorem integral_ball_norm (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ, ‖v‖
      = d * unitBallVolume d * ρ ^ (d + 1) / (d + 1) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rcases hρ.eq_or_lt with rfl | hρpos
  · simp
  have h1 : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ, ‖v‖
      = ∫ v : EuclideanSpace ℝ (Fin d), (Set.Iio ρ).indicator (fun r : ℝ => r) ‖v‖ := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Set.indicator, mem_ball_zero_iff, Set.mem_Iio]
  rw [h1, integral_fun_norm_addHaar volume, finrank_euclideanSpace_fin]
  have h2 : ∫ y in Set.Ioi (0 : ℝ), y ^ (d - 1) • (Set.Iio ρ).indicator (fun r : ℝ => r) y
      = ∫ y in Set.Ioi (0 : ℝ), (Set.Iio ρ).indicator (fun r : ℝ => r ^ d) y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y < ρ
    · simp only [Set.indicator_of_mem (Set.mem_Iio.mpr hy), smul_eq_mul]
      rw [← pow_succ, Nat.sub_add_cancel hd]
    · simp only [Set.indicator_of_notMem (mt Set.mem_Iio.mp hy), smul_zero]
  rw [h2, setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρpos.le, integral_pow]
  simp only [smul_eq_mul, Measure.real, unitBallVolume]
  ring

/-- The `d`-th power of the `d`-th root `x^{1/d}` of a nonnegative `x` is `x`. -/
theorem rpow_one_div_natCast_pow {x : ℝ} (hx : 0 ≤ x) (hd : 1 ≤ d) :
    (x ^ ((1 : ℝ) / d)) ^ d = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx,
    one_div_mul_cancel (Nat.cast_ne_zero.mpr (by omega)), Real.rpow_one]

/-- The constant `(d/(d+1)) ω^{-1/d} R^{1+1/d}` equals `d ω ρ^{d+1}/(d+1)` with
`ρ = (R/ω)^{1/d}`. -/
theorem radialPacking_constant (hd : 1 ≤ d) {ω R : ℝ} (hω : 0 < ω) (hR : 0 < R) :
    d / (d + 1) * ω ^ (-(1 : ℝ) / d) * R ^ (1 + (1 : ℝ) / d)
      = d * ω * ((R / ω) ^ ((1 : ℝ) / d)) ^ (d + 1) / (d + 1) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ω ^ (-(1 : ℝ) / d) = (ω ^ ((1 : ℝ) / d))⁻¹ := by
    rw [neg_div, Real.rpow_neg hω.le]
  have h2 : R ^ (1 + (1 : ℝ) / d) = R * R ^ ((1 : ℝ) / d) := by
    rw [Real.rpow_add hR, Real.rpow_one]
  have h3 : (R / ω) ^ ((1 : ℝ) / d) = R ^ ((1 : ℝ) / d) / ω ^ ((1 : ℝ) / d) :=
    Real.div_rpow hR.le hω.le _
  have hpos : 0 < ω ^ ((1 : ℝ) / d) := Real.rpow_pos_of_pos hω _
  rw [h1, h2, pow_succ, rpow_one_div_natCast_pow (div_pos hR hω).le hd, h3]
  field_simp

/-- `eq:radial-packing`: for `d ≥ 1` and a bounded measurable set `D`,
`∫_D |v| ≥ (d/(d+1)) ω_d^{-1/d} |D|^{1+1/d}`. -/
theorem le_setIntegral_norm (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) :
    d / (d + 1) * unitBallVolume d ^ (-(1 : ℝ) / d) * (volume D).toReal ^ (1 + (1 : ℝ) / d)
      ≤ ∫ v in D, ‖v‖ := by
  have hfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hω := unitBallVolume_pos d
  rcases eq_or_ne (volume D) 0 with h0 | h0
  · have hd0 : (1 + (1 : ℝ) / d) ≠ 0 := by positivity
    rw [h0, ENNReal.toReal_zero, Real.zero_rpow hd0, mul_zero]
    exact setIntegral_nonneg hD fun v _ => norm_nonneg v
  have hR : 0 < (volume D).toReal := ENNReal.toReal_pos h0 hfin
  set R := (volume D).toReal with hRdef
  set ρ : ℝ := (R / unitBallVolume d) ^ ((1 : ℝ) / d) with hρdef
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (div_pos hR hω) _
  have hvol : volume D = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ) := by
    rw [Measure.addHaar_ball_of_pos volume _ hρ, finrank_euclideanSpace_fin,
      rpow_one_div_natCast_pow (div_pos hR hω).le hd]
    have hball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
        = ENNReal.ofReal (unitBallVolume d) :=
      (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
    rw [hball, ← ENNReal.ofReal_mul (div_pos hR hω).le, div_mul_cancel₀ _ hω.ne',
      hRdef, ENNReal.ofReal_toReal hfin]
  obtain ⟨C, hC⟩ := hDb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hint : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) D :=
    Measure.integrableOn_of_bounded (M := C) hfin measurable_norm.aestronglyMeasurable
      (ae_restrict_of_forall_mem hD fun v hv => by
        rw [norm_norm]
        exact mem_closedBall_zero_iff.mp (hC hv))
  have hmain := setIntegral_ball_le_of_monotoneOn (g := fun t : ℝ => t)
    (fun a _ b _ hab => hab) (fun t ht => ht) hD hρ hvol hint
  rw [integral_ball_norm hd hρ.le] at hmain
  rw [radialPacking_constant hd hω hR]
  exact hmain

end CERW.Generic.Kernel
