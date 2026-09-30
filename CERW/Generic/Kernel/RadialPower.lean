import CERW.Model.Potential
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Radial power integrals

In polar coordinates `∫_{ℝ^d} g(|v|) dv = σ_d ∫_0^∞ t^{d-1} g(t) dt` with `σ_d = d ω_d`. For the
power `|v|^{-s}` this gives `∫_{B(0,ρ)} |v|^{-s} = σ_d ρ^{d-s}/(d-s)` when `s < d`, and
`∫_{|v| ≥ ρ} |v|^{-s} = σ_d ρ^{d-s}/(s-d)` when `s > d`. These are the near and far pieces of
the scaling bound `eq:kernel-modulus` and of the logarithmic bound `eq:direction-error`.
-/

namespace CERW.Generic.Kernel

open MeasureTheory CERW

variable {d : ℕ}

/-- On `(0, ∞)` the weight `t ^ (d - 1)` combines with the indicator of `t < ρ` to give
`t ^ (d - 1 - s)`; for `s < d` its integral is `ρ ^ (d - s) / (d - s)`. -/
theorem setIntegral_Ioi_indicator_Iio_rpow (hd : 1 ≤ d) {s ρ : ℝ} (hs : s < (d : ℝ))
    (hρ : 0 < ρ) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (d - 1) • (Set.Iio ρ).indicator (fun t : ℝ => t ^ (-s)) t
      = ρ ^ ((d : ℝ) - s) / ((d : ℝ) - s) := by
  have ha : -1 < (d : ℝ) - 1 - s := by linarith
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      t ^ (d - 1) • (Set.Iio ρ).indicator (fun t : ℝ => t ^ (-s)) t
        = (Set.Ioo (0 : ℝ) ρ).indicator (fun t : ℝ => t ^ ((d : ℝ) - 1 - s)) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases htρ : t < ρ
    · rw [Set.indicator_of_mem (Set.mem_Iio.mpr htρ),
        Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ht0, htρ⟩), smul_eq_mul,
        ← Real.rpow_natCast, ← Real.rpow_add ht0]
      congr 1
      rw [Nat.cast_sub hd]
      ring_nf
    · simp [Set.indicator, htρ]
  have hsub : Set.Ioo (0 : ℝ) ρ ⊆ Set.Ioi (0 : ℝ) := fun x hx => hx.1
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    setIntegral_indicator measurableSet_Ioo, Set.inter_eq_right.mpr hsub,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le,
    integral_rpow (Or.inl ha)]
  have hne : (d : ℝ) - 1 - s + 1 ≠ 0 := by
    have hpos : 0 < (d : ℝ) - 1 - s + 1 := by linarith
    exact ne_of_gt hpos
  rw [Real.zero_rpow hne, sub_zero,
    show (d : ℝ) - 1 - s + 1 = (d : ℝ) - s by ring_nf]

/-- For `s < d`, `|v|^{-s}` is integrable on `B(0, ρ)` with integral `σ_d ρ^{d-s}/(d-s)`. -/
theorem integrableOn_ball_rpow_neg_and_integral_eq (hd : 1 ≤ d) {s ρ : ℝ} (hs : s < d)
    (hρ : 0 < ρ) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (-s)) (Metric.ball 0 ρ) ∧
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ, ‖v‖ ^ (-s)
        = d * unitBallVolume d * ρ ^ ((d : ℝ) - s) / ((d : ℝ) - s) := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
  have hIntRadial : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - 1 - s)) (Set.Ioo 0 ρ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hρ).mpr (by linarith)
  refine ⟨?_, ?_⟩
  · rw [integrableOn_fun_norm_addHaar (volume) (f := fun t : ℝ => t ^ (-s)), hfin]
    refine hIntRadial.congr_fun ?_ measurableSet_Ioo
    intro y hy
    change y ^ ((d : ℝ) - 1 - s) = y ^ (d - 1) • y ^ (-s)
    rw [smul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_add hy.1, hcast]
    ring_nf
  · have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ).indicator
          (fun v => ‖v‖ ^ (-s))
          = fun v => (Set.Iio ρ).indicator (fun t : ℝ => t ^ (-s)) ‖v‖ := by
      funext v
      by_cases hv : ‖v‖ < ρ <;> simp [Set.indicator, hv]
    rw [← integral_indicator Metric.isOpen_ball.measurableSet, hind,
      integral_fun_norm_addHaar (volume), hfin,
      setIntegral_Ioi_indicator_Iio_rpow hd hs hρ]
    simp only [unitBallVolume, Measure.real, nsmul_eq_mul, smul_eq_mul]
    ring_nf

/-- On `(0, ∞)` the weight `t ^ (d - 1)` combines with the indicator of `t ≥ ρ` to give
`t ^ (d - 1 - s)`; for `s > d` its integral is `ρ ^ (d - s) / (s - d)`. -/
theorem setIntegral_Ioi_indicator_Ici_rpow (hd : 1 ≤ d) {s ρ : ℝ} (hs : (d : ℝ) < s)
    (hρ : 0 < ρ) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (d - 1) • (Set.Ici ρ).indicator (fun t : ℝ => t ^ (-s)) t
      = ρ ^ ((d : ℝ) - s) / (s - (d : ℝ)) := by
  have ha : (d : ℝ) - 1 - s < -1 := by linarith
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      t ^ (d - 1) • (Set.Ici ρ).indicator (fun t : ℝ => t ^ (-s)) t
        = (Set.Ici ρ).indicator (fun t : ℝ => t ^ ((d : ℝ) - 1 - s)) t := by
    intro t ht
    by_cases htρ : ρ ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr htρ),
        Set.indicator_of_mem (Set.mem_Ici.mpr htρ), smul_eq_mul,
        ← Real.rpow_natCast, ← Real.rpow_add (lt_of_lt_of_le hρ htρ)]
      congr 1
      rw [Nat.cast_sub hd]
      ring_nf
    · simp [Set.indicator, htρ]
  have hsub : Set.Ici ρ ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hρ hx
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    setIntegral_indicator measurableSet_Ici, Set.inter_eq_right.mpr hsub,
    integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt ha hρ,
    show (d : ℝ) - 1 - s + 1 = (d : ℝ) - s by ring_nf,
    show s - (d : ℝ) = -((d : ℝ) - s) by ring_nf, div_neg]
  ring_nf

/-- For `s > d`, `|v|^{-s}` is integrable off `B(0, ρ)` with integral `σ_d ρ^{d-s}/(s-d)`. -/
theorem integrableOn_compl_ball_rpow_neg_and_integral_eq (hd : 1 ≤ d) {s ρ : ℝ}
    (hs : (d : ℝ) < s) (hρ : 0 < ρ) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (-s)) (Metric.ball 0 ρ)ᶜ ∧
      ∫ v in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ, ‖v‖ ^ (-s)
        = d * unitBallVolume d * ρ ^ ((d : ℝ) - s) / (s - (d : ℝ)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
  have ha : (d : ℝ) - 1 - s < -1 := by linarith
  have hIntRadial : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - 1 - s)) (Set.Ioi ρ) :=
    integrableOn_Ioi_rpow_of_lt ha hρ
  have hcombine : (fun y : ℝ => y ^ (d - 1) • (Set.Ici ρ).indicator (fun t : ℝ => t ^ (-s)) y)
      = (Set.Ici ρ).indicator (fun y : ℝ => y ^ ((d : ℝ) - 1 - s)) := by
    funext y
    by_cases hy : ρ ≤ y
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy), Set.indicator_of_mem (Set.mem_Ici.mpr hy),
        smul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_add (lt_of_lt_of_le hρ hy), hcast]
      ring_nf
    · simp [Set.indicator, hy]
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun v => ‖v‖ ^ (-s))
        = fun v => (Set.Ici ρ).indicator (fun t : ℝ => t ^ (-s)) ‖v‖ := by
    funext v
    by_cases hv : ‖v‖ < ρ
    · have hle : ¬ ρ ≤ ‖v‖ := not_le_of_gt hv
      simp [Set.indicator, Metric.mem_ball, dist_eq_norm, hv, hle]
    · have hle : ρ ≤ ‖v‖ := le_of_not_gt hv
      simp [Set.indicator, Metric.mem_ball, dist_eq_norm, hv, hle]
  have hsub : Set.Ici ρ ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hρ hx
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff measurableSet_ball.compl, hind,
      integrable_fun_norm_addHaar (volume), hfin, hcombine,
      integrableOn_indicator_iff measurableSet_Ici, Set.inter_eq_left.mpr hsub,
      integrableOn_Ici_iff_integrableOn_Ioi]
    exact hIntRadial
  · rw [← integral_indicator Metric.isOpen_ball.measurableSet.compl, hind,
      integral_fun_norm_addHaar (volume), hfin,
      setIntegral_Ioi_indicator_Ici_rpow hd hs hρ]
    simp only [unitBallVolume, Measure.real, nsmul_eq_mul, smul_eq_mul]
    ring_nf

end CERW.Generic.Kernel
