import CERW.Generic.Kernel.Integrable
import CERW.Generic.Kernel.LogRadial

/-!
# The direction error

`eq:direction-error`: `∫_{B(0,R)} dv / ((1 + |v|) |v - y|^{d-1}) ≤ C_d log(R + 2)` for `R ≥ 1`
and `|y| ≤ 2R`. Near `y`, the kernel `|v - y|^{1-d}` has integral `σ_d` over `B(y, 1)`. Away
from `y`, Young's inequality with exponents `d` and `d/(d-1)` bounds the integrand by
`(1 + |v|)^{-d}/d + |v - y|^{-d}(d-1)/d`. The integral of each term is logarithmic.
-/

namespace CERW.Generic.Kernel

open MeasureTheory CERW

variable {d : ℕ}

/-- Young's inequality bounds the direction-error integrand by the sum of the two logarithmic
kernels. For `d ≥ 2` and all `v y`,
`(1 + ‖v‖)⁻¹ * ‖v - y‖ ^ (1 - d) ≤ (1 + ‖v‖) ^ (-d) + ‖v - y‖ ^ (-d)`. -/
theorem direction_integrand_le_young (hd : 2 ≤ d) (v y : EuclideanSpace ℝ (Fin d)) :
    (1 + ‖v‖)⁻¹ * ‖v - y‖ ^ (1 - (d : ℝ))
      ≤ (1 + ‖v‖) ^ (-(d : ℝ)) + ‖v - y‖ ^ (-(d : ℝ)) := by
  have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
  have hbase : (0 : ℝ) ≤ 1 + ‖v‖ := by positivity
  have hw : (0 : ℝ) ≤ ‖v - y‖ := norm_nonneg _
  have hq : ((d : ℝ)).HolderConjugate ((d : ℝ) / ((d : ℝ) - 1)) :=
    Real.HolderConjugate.conjExponent hd1
  have hy := Real.young_inequality_of_nonneg (inv_nonneg.mpr hbase)
    (Real.rpow_nonneg hw (1 - (d : ℝ))) hq
  have h1 : ((1 + ‖v‖)⁻¹) ^ (d : ℝ) = (1 + ‖v‖) ^ (-(d : ℝ)) := by
    rw [Real.inv_rpow hbase, Real.rpow_neg hbase]
  have h2 : (‖v - y‖ ^ (1 - (d : ℝ))) ^ ((d : ℝ) / ((d : ℝ) - 1))
      = ‖v - y‖ ^ (-(d : ℝ)) := by
    rw [← Real.rpow_mul hw (1 - (d : ℝ)) ((d : ℝ) / ((d : ℝ) - 1))]
    congr 1
    have hne : ((d : ℝ) - 1) ≠ 0 := by linarith
    field_simp
    ring
  calc
    (1 + ‖v‖)⁻¹ * ‖v - y‖ ^ (1 - (d : ℝ))
        ≤ ((1 + ‖v‖)⁻¹) ^ (d : ℝ) / (d : ℝ)
          + (‖v - y‖ ^ (1 - (d : ℝ))) ^ ((d : ℝ) / ((d : ℝ) - 1))
            / ((d : ℝ) / ((d : ℝ) - 1)) := hy
    _ = (1 + ‖v‖) ^ (-(d : ℝ)) / (d : ℝ)
          + ‖v - y‖ ^ (-(d : ℝ)) / ((d : ℝ) / ((d : ℝ) - 1)) := by
          rw [h1, h2]
    _ ≤ (1 + ‖v‖) ^ (-(d : ℝ)) + ‖v - y‖ ^ (-(d : ℝ)) := by
          have hgfar : 0 ≤ (1 + ‖v‖) ^ (-(d : ℝ)) := Real.rpow_nonneg hbase _
          have hhfar : 0 ≤ ‖v - y‖ ^ (-(d : ℝ)) := Real.rpow_nonneg hw _
          have hq1 : (1 : ℝ) ≤ (d : ℝ) / ((d : ℝ) - 1) := by
            rw [le_div_iff₀ (by linarith)]
            linarith
          have hA : (1 + ‖v‖) ^ (-(d : ℝ)) / (d : ℝ) ≤ (1 + ‖v‖) ^ (-(d : ℝ)) :=
            div_le_self hgfar (by linarith)
          have hB : ‖v - y‖ ^ (-(d : ℝ)) / ((d : ℝ) / ((d : ℝ) - 1))
              ≤ ‖v - y‖ ^ (-(d : ℝ)) :=
            div_le_self hhfar hq1
          linarith

/-- The logarithmic arithmetic in the direction-error bound:
`1 + log(1 + R) + log(3R) ≤ 4 log(R + 2)` for `R ≥ 1`. -/
theorem log_direction_arith {R : ℝ} (hR : 1 ≤ R) :
    1 + Real.log (1 + R) + Real.log (3 * R) ≤ 4 * Real.log (R + 2) := by
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    linarith [Real.exp_one_lt_d9]
  have hlogR2 : 1 ≤ Real.log (R + 2) := by
    have h3 : (3 : ℝ) ≤ R + 2 := by linarith
    exact le_trans hlog3.le (Real.log_le_log (by norm_num) h3)
  have hlog1R : Real.log (1 + R) ≤ Real.log (R + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog3R : Real.log (3 * R) ≤ 2 * Real.log (R + 2) := by
    have hpos : 0 < 3 * R := by linarith
    have hle : 3 * R ≤ (R + 2) ^ 2 := by nlinarith [sq_nonneg R]
    calc Real.log (3 * R) ≤ Real.log ((R + 2) ^ 2) := Real.log_le_log hpos hle
      _ = 2 * Real.log (R + 2) := by rw [Real.log_pow]; norm_num
  linarith

/-- Translation carries the annulus integral of `‖v - y‖^(-d)` to the centred annulus.
For `0 < ρ ≤ R`, the function is integrable on `B(y, R) \ B(y, ρ)` with integral
`d ω_d log(R/ρ)`. -/
theorem integrableOn_shifted_annulus_norm_rpow_and_integral_eq (hd : 1 ≤ d)
    (y : EuclideanSpace ℝ (Fin d)) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    IntegrableOn (fun v => ‖v - y‖ ^ (-(d : ℝ))) (Metric.ball y R \ Metric.ball y ρ) ∧
      ∫ v in Metric.ball y R \ Metric.ball y ρ, ‖v - y‖ ^ (-(d : ℝ))
        = d * unitBallVolume d * Real.log (R / ρ) := by
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) y
  have hemb := measurableEmbedding_subRight y
  have hpre : Metric.ball y R \ Metric.ball y ρ
      = (fun v : EuclideanSpace ℝ (Fin d) => v - y) ⁻¹'
          (Metric.ball 0 R \ Metric.ball 0 ρ) := by
    rw [Set.preimage_sdiff, ball_eq_preimage_sub y R, ball_eq_preimage_sub y ρ]
  obtain ⟨hint, hval⟩ := integrableOn_annulus_norm_rpow_and_integral_eq (d := d) hd hρ hρR
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact (hmp.integrableOn_comp_preimage hemb (f := fun w => ‖w‖ ^ (-(d : ℝ)))).mpr hint
  · rw [hpre, hmp.setIntegral_preimage_emb hemb (fun w => ‖w‖ ^ (-(d : ℝ))), hval]

/-- `eq:direction-error`: for `R ≥ 1` and `|y| ≤ 2R`, the kernel
`(1 + |v|)^{-1} |v - y|^{1-d}` is integrable on `B(0, R)` with integral at most
`C_d log(R + 2)`. -/
theorem exists_direction_error (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R →
      IntegrableOn (fun v => (1 + ‖v‖)⁻¹ * ‖v - y‖ ^ (1 - (d : ℝ))) (Metric.ball 0 R) ∧
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R, (1 + ‖v‖)⁻¹ * ‖v - y‖ ^ (1 - (d : ℝ))
        ≤ C * Real.log (R + 2) := by
  refine ⟨4 * ((d : ℝ) * unitBallVolume d), ?_, ?_⟩
  · have hω : 0 < unitBallVolume d := unitBallVolume_pos d
    positivity
  · intro R hR y hy
    have hd1 : 1 ≤ d := by omega
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    let B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 R
    let N : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball y 1
    let f : EuclideanSpace ℝ (Fin d) → ℝ :=
      fun v => (1 + ‖v‖)⁻¹ * ‖v - y‖ ^ (1 - (d : ℝ))
    let gnear : EuclideanSpace ℝ (Fin d) → ℝ := fun v => ‖v - y‖ ^ (1 - (d : ℝ))
    let gfar : EuclideanSpace ℝ (Fin d) → ℝ := fun v => (1 + ‖v‖) ^ (-(d : ℝ))
    let hfar : EuclideanSpace ℝ (Fin d) → ℝ := fun v => ‖v - y‖ ^ (-(d : ℝ))
    have hgnear_int_B : IntegrableOn gnear B :=
      (integrableOn_and_setIntegral_le hd1 measurableSet_ball measure_ball_lt_top.ne y).1
    have hf_meas : AEStronglyMeasurable f (volume.restrict B) := by
      have hfac : Measurable (fun v : EuclideanSpace ℝ (Fin d) => (1 + ‖v‖)⁻¹) :=
        (measurable_const.add measurable_norm).inv
      exact hfac.aestronglyMeasurable.mul hgnear_int_B.aestronglyMeasurable
    have hf_le_gnear : ∀ᵐ v ∂(volume.restrict B), ‖f v‖ ≤ gnear v := by
      refine Filter.Eventually.of_forall (fun v => ?_)
      have hgnear_nonneg : 0 ≤ gnear v := Real.rpow_nonneg (norm_nonneg _) _
      have hf_nonneg : 0 ≤ f v :=
        mul_nonneg (inv_nonneg.mpr (by positivity)) hgnear_nonneg
      rw [Real.norm_of_nonneg hf_nonneg]
      calc f v = (1 + ‖v‖)⁻¹ * gnear v := rfl
        _ ≤ 1 * gnear v :=
            mul_le_mul_of_nonneg_right
              (inv_le_one_of_one_le₀ (by linarith [norm_nonneg v])) hgnear_nonneg
        _ = gnear v := one_mul _
    have hf_int_B : IntegrableOn f B := hgnear_int_B.mono' hf_meas hf_le_gnear
    -- Near `y`
    have hgnear_int_N : IntegrableOn gnear N :=
      (integrableOn_ball_and_integral_eq hd1 y one_pos).1
    have hgnear_val_N : ∫ v in N, gnear v = (d : ℝ) * unitBallVolume d * 1 :=
      (integrableOn_ball_and_integral_eq hd1 y one_pos).2
    have hf_int_BN : IntegrableOn f (B ∩ N) := hf_int_B.mono_set (fun v hv => hv.1)
    have hgnear_int_BN : IntegrableOn gnear (B ∩ N) := hgnear_int_N.mono_set (fun v hv => hv.2)
    have hnear1 : ∫ v in B ∩ N, f v ≤ ∫ v in B ∩ N, gnear v :=
      setIntegral_mono_on hf_int_BN hgnear_int_BN (measurableSet_ball.inter measurableSet_ball)
        (fun v _ => by
          have hgnear_nonneg : 0 ≤ gnear v := Real.rpow_nonneg (norm_nonneg _) _
          calc f v = (1 + ‖v‖)⁻¹ * gnear v := rfl
            _ ≤ 1 * gnear v :=
                mul_le_mul_of_nonneg_right
                  (inv_le_one_of_one_le₀ (by linarith [norm_nonneg v])) hgnear_nonneg
            _ = gnear v := one_mul _)
    have hnear2 : ∫ v in B ∩ N, gnear v ≤ ∫ v in N, gnear v :=
      setIntegral_mono_set hgnear_int_N
        (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg _) _))
        (Filter.Eventually.of_forall (fun _ hv => hv.2))
    have hnear : ∫ v in B ∩ N, f v ≤ (d : ℝ) * unitBallVolume d := by
      calc ∫ v in B ∩ N, f v ≤ ∫ v in N, gnear v := le_trans hnear1 hnear2
        _ = (d : ℝ) * unitBallVolume d * 1 := hgnear_val_N
        _ = (d : ℝ) * unitBallVolume d := by ring
    -- Far from `y`
    have hgfar_int_B : IntegrableOn gfar B :=
      (integrableOn_ball_one_add_norm_rpow_and_integral_le hd1 hRpos).1
    have hgfar_val_B : ∫ v in B, gfar v ≤ (d : ℝ) * unitBallVolume d * Real.log (1 + R) :=
      (integrableOn_ball_one_add_norm_rpow_and_integral_le hd1 hRpos).2
    have h3R : (1 : ℝ) ≤ 3 * R := by linarith
    have hAnn : IntegrableOn hfar (Metric.ball y (3 * R) \ Metric.ball y 1) ∧
        ∫ v in Metric.ball y (3 * R) \ Metric.ball y 1, hfar v
          = (d : ℝ) * unitBallVolume d * Real.log ((3 * R) / 1) :=
      integrableOn_shifted_annulus_norm_rpow_and_integral_eq hd1 y one_pos h3R
    have hsub_Ann : B \ N ⊆ Metric.ball y (3 * R) \ Metric.ball y 1 := by
      intro v hv
      refine ⟨?_, hv.2⟩
      have hvB : ‖v‖ < R := by
        have h := hv.1
        rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖v - y‖ ≤ ‖v‖ + ‖y‖ := norm_sub_le v y
        _ < R + 2 * R := by linarith
        _ = 3 * R := by ring
    have hf_int_diff : IntegrableOn f (B \ N) := hf_int_B.mono_set (fun v hv => hv.1)
    have hgfar_int_diff : IntegrableOn gfar (B \ N) := hgfar_int_B.mono_set (fun v hv => hv.1)
    have hhfar_int_diff : IntegrableOn hfar (B \ N) := hAnn.1.mono_set hsub_Ann
    have hfar_sum : ∫ v in B \ N, f v ≤ ∫ v in B \ N, (gfar v + hfar v) :=
      setIntegral_mono_on hf_int_diff (hgfar_int_diff.add hhfar_int_diff)
        (measurableSet_ball.diff measurableSet_ball)
        (fun v _ => direction_integrand_le_young hd v y)
    have hfar_split : ∫ v in B \ N, (gfar v + hfar v)
        = (∫ v in B \ N, gfar v) + (∫ v in B \ N, hfar v) :=
      integral_add hgfar_int_diff hhfar_int_diff
    have hgfar_le : ∫ v in B \ N, gfar v ≤ (d : ℝ) * unitBallVolume d * Real.log (1 + R) := by
      have hmono : ∫ v in B \ N, gfar v ≤ ∫ v in B, gfar v :=
        setIntegral_mono_set hgfar_int_B
          (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (by positivity) _))
          (Filter.Eventually.of_forall (fun _ hv => hv.1))
      exact le_trans hmono hgfar_val_B
    have hhfar_le : ∫ v in B \ N, hfar v ≤ (d : ℝ) * unitBallVolume d * Real.log (3 * R) := by
      have hmono : ∫ v in B \ N, hfar v
          ≤ ∫ v in Metric.ball y (3 * R) \ Metric.ball y 1, hfar v :=
        setIntegral_mono_set hAnn.1
          (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg _) _))
          (Filter.Eventually.of_forall hsub_Ann)
      refine le_trans hmono ?_
      rw [hAnn.2]
      have hdiv : Real.log ((3 * R) / 1) = Real.log (3 * R) := by rw [div_one]
      rw [hdiv]
    have hfar : ∫ v in B \ N, f v
        ≤ (d : ℝ) * unitBallVolume d * Real.log (1 + R)
          + (d : ℝ) * unitBallVolume d * Real.log (3 * R) := by
      calc ∫ v in B \ N, f v ≤ ∫ v in B \ N, (gfar v + hfar v) := hfar_sum
        _ = (∫ v in B \ N, gfar v) + (∫ v in B \ N, hfar v) := hfar_split
        _ ≤ (d : ℝ) * unitBallVolume d * Real.log (1 + R)
              + (d : ℝ) * unitBallVolume d * Real.log (3 * R) :=
            add_le_add hgfar_le hhfar_le
    have hsplit := integral_inter_add_sdiff (μ := volume) (f := f) (s := B) (t := N)
      measurableSet_ball hf_int_B
    have hfin : ∫ v in B, f v ≤ 4 * ((d : ℝ) * unitBallVolume d) * Real.log (R + 2) := by
      calc ∫ v in B, f v = (∫ v in B ∩ N, f v) + (∫ v in B \ N, f v) := hsplit.symm
        _ ≤ (d : ℝ) * unitBallVolume d
              + ((d : ℝ) * unitBallVolume d * Real.log (1 + R)
                + (d : ℝ) * unitBallVolume d * Real.log (3 * R)) :=
            add_le_add hnear hfar
        _ = (d : ℝ) * unitBallVolume d * (1 + Real.log (1 + R) + Real.log (3 * R)) := by ring
        _ ≤ (d : ℝ) * unitBallVolume d * (4 * Real.log (R + 2)) :=
            mul_le_mul_of_nonneg_left (log_direction_arith hR)
              (mul_nonneg (by positivity) (unitBallVolume_pos d).le)
        _ = 4 * ((d : ℝ) * unitBallVolume d) * Real.log (R + 2) := by ring
    exact ⟨hf_int_B, hfin⟩

end CERW.Generic.Kernel
