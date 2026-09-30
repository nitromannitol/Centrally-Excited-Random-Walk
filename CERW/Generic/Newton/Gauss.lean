import CERW.Generic.Newton.Polar
import CERW.Generic.Kernel.NewtonField
import CERW.Generic.Kernel.Integrable
import CERW.Model.Potential

/-!
# Gauss's law for a point source

For `φ ∈ C¹_c(ℝ^d)`, `∫ Dφ(v)[K(v - c)] dv = -σ_d φ(c)`. In polar coordinates about `c`,
`K(rθ) = r^{1-d} θ` cancels the radial weight `r^{d-1}`. The integrand becomes the radial
derivative `∂_r φ(c + rθ)`. Its integral over `r > 0` is `-φ(c)` because `φ` has compact support,
and integrating over the sphere gives `-σ_d φ(c)`. This is the distributional identity
`div K(· - c) = σ_d δ_c` behind `eq:kernel-average`.
-/

namespace CERW.Generic.Newton

open MeasureTheory CERW CERW.Generic.Kernel

variable {d : ℕ}

/-- On the unit sphere, the radial weight `r^(d-1)` cancels the field: `r^(d-1) K(rθ) = θ`. -/
private lemma pow_smul_newtonField_smul (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    r ^ (d - 1) • newtonField (r • θ) = θ := by
  rw [newtonField, norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hr, mul_one, smul_smul,
    smul_smul]
  have h : r ^ (d - 1) * (r ^ d)⁻¹ * r = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have hk : r ^ k ≠ 0 := pow_ne_zero k hr.ne'
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [h, one_smul]

/-- If `tsupport φ` lies in the closed ball of radius `ρ`, then `φ` vanishes outside it. -/
private lemma eq_zero_of_lt_norm {φ : EuclideanSpace ℝ (Fin d) → ℝ} {ρ : ℝ}
    (h : tsupport φ ⊆ Metric.closedBall 0 ρ) {x : EuclideanSpace ℝ (Fin d)} (hx : ρ < ‖x‖) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => by
    have := mem_closedBall_zero_iff.1 (h hmem)
    linarith

/-- If `tsupport φ` lies in the closed ball of radius `ρ`, then `Dφ` vanishes outside it. -/
private lemma fderiv_eq_zero_of_lt_norm {φ : EuclideanSpace ℝ (Fin d) → ℝ} {ρ : ℝ}
    (h : tsupport φ ⊆ Metric.closedBall 0 ρ) {x : EuclideanSpace ℝ (Fin d)} (hx : ρ < ‖x‖) :
    fderiv ℝ φ x = 0 := by
  by_contra hne
  have := mem_closedBall_zero_iff.1 (h (support_fderiv_subset ℝ hne))
  linarith

/-- The Gauss integrand `w ↦ Dφ(c + w)[K(w)]` is integrable: it is bounded by `B |w|^{1-d}` on a
ball and vanishes outside. -/
private lemma integrable_fderiv_newtonField (hd : 2 ≤ d) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ) (c : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun w : EuclideanSpace ℝ (Fin d) => fderiv ℝ φ (c + w) (newtonField w)) := by
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := hD.bounded_above_of_compact_support (hsupp.fderiv (𝕜 := ℝ))
  obtain ⟨ρ, hρ0, hρ⟩ := hsupp.isCompact.isBounded.subset_closedBall_lt 0
    (0 : EuclideanSpace ℝ (Fin d))
  have hR : 0 < ρ + ‖c‖ + 1 := by positivity
  have hbound : Integrable ((Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (ρ + ‖c‖ + 1)).indicator
      (fun w => B * ‖w‖ ^ (1 - (d : ℝ)))) :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2
      ((integrableOn_ball_zero_and_integral_eq (by omega) hR).1.const_mul B)
  have hmeas : AEStronglyMeasurable
      (fun w : EuclideanSpace ℝ (Fin d) => fderiv ℝ φ (c + w) (newtonField w)) := by
    have h1 : AEStronglyMeasurable fun w : EuclideanSpace ℝ (Fin d) => fderiv ℝ φ (c + w) :=
      (hD.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    have h2 : Measurable (newtonField :
        EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
      (measurable_norm.pow_const d).inv.smul measurable_id
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ h1
      h2.aestronglyMeasurable
  refine hbound.mono' hmeas (Filter.Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (ρ + ‖c‖ + 1)
  · rw [Set.indicator_of_mem hw, ← norm_newtonField hd w]
    calc ‖fderiv ℝ φ (c + w) (newtonField w)‖
        ≤ ‖fderiv ℝ φ (c + w)‖ * ‖newtonField w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * ‖newtonField w‖ := mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · rw [Set.indicator_of_notMem hw]
    have hw' : ρ + ‖c‖ + 1 ≤ ‖w‖ := by simpa using hw
    have hlt : ρ < ‖c + w‖ := by
      have := norm_sub_norm_le w (-c)
      have h2 := norm_add_le c w
      rw [sub_neg_eq_add, norm_neg, add_comm w c] at this
      linarith
    rw [fderiv_eq_zero_of_lt_norm hρ hlt]
    simp

/-- For a unit vector `θ`, the integral of the radial derivative `Dφ(c + rθ)[θ]` over `r > 0` is
`-φ(c)`, since `φ(c + rθ)` is an antiderivative that vanishes for large `r`. -/
private lemma integral_Ioi_fderiv_ray {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ) (c : EuclideanSpace ℝ (Fin d))
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    ∫ r in Set.Ioi (0 : ℝ), fderiv ℝ φ (c + r • θ) θ = -φ c := by
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨ρ, -, hρ⟩ := hsupp.isCompact.isBounded.subset_closedBall_lt 0
    (0 : EuclideanSpace ℝ (Fin d))
  have hlt : ∀ r : ℝ, ρ + ‖c‖ < r → ρ < ‖c + r • θ‖ := by
    intro r hr
    have h1 := norm_sub_norm_le (r • θ) (-c)
    rw [sub_neg_eq_add, norm_neg, norm_smul, hθ, Real.norm_eq_abs, mul_one,
      add_comm (r • θ) c] at h1
    have := le_abs_self r
    have := norm_nonneg c
    linarith
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun r : ℝ => φ (c + r • θ)) (fderiv ℝ φ (c + x • θ) θ) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => c + r • θ) θ x := by
      simpa using ((hasDerivAt_id x).smul_const θ).const_add c
    exact ((hφ.differentiable one_ne_zero) (c + x • θ)).hasFDerivAt.comp_hasDerivAt x h1
  have hcont : Continuous fun r : ℝ => fderiv ℝ φ (c + r • θ) θ :=
    (hD.comp (by fun_prop)).clm_apply continuous_const
  have hint : IntegrableOn (fun r : ℝ => fderiv ℝ φ (c + r • θ) θ) (Set.Ioi 0) := by
    have hle : (0 : ℝ) ≤ max (ρ + ‖c‖) 0 := le_max_right _ _
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle]
    refine (hcont.integrableOn_Ioc).union ?_
    refine (integrableOn_zero (μ := volume)).congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr' : ρ + ‖c‖ < r := lt_of_le_of_lt (le_max_left _ _) hr
    rw [fderiv_eq_zero_of_lt_norm hρ (hlt r hr')]
    simp
  have hlim : Filter.Tendsto (fun r : ℝ => φ (c + r • θ)) Filter.atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (ρ + ‖c‖)] with r hr
    exact (eq_zero_of_lt_norm hρ (hlt r hr)).symm
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  simpa using this

/-- Gauss's law for a point source, tested against a `C¹` function with compact support:
`∫ Dφ(v)[K(v - c)] dv = -σ_d φ(c)`. -/
theorem integral_fderiv_newtonField (hd : 2 ≤ d) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ) (c : EuclideanSpace ℝ (Fin d)) :
    ∫ v, fderiv ℝ φ v (newtonField (v - c)) = -(d * unitBallVolume d * φ c) := by
  have hd1 : 1 ≤ d := by omega
  have hint := integrable_fderiv_newtonField hd hφ hsupp c
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := hD.bounded_above_of_compact_support (hsupp.fderiv (𝕜 := ℝ))
  obtain ⟨ρ, -, hρ⟩ := hsupp.isCompact.isBounded.subset_closedBall_lt 0
    (0 : EuclideanSpace ℝ (Fin d))
  have hshift : ∫ v, fderiv ℝ φ v (newtonField (v - c))
      = ∫ w, fderiv ℝ φ (c + w) (newtonField w) := by
    rw [← integral_add_left_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) _ c]
    simp
  have hpoint : ∀ r ∈ Set.Ioi (0 : ℝ),
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        fderiv ℝ φ (c + r • (θ : EuclideanSpace ℝ (Fin d)))
          (newtonField (r • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
      = ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        fderiv ℝ φ (c + r • (θ : EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
    intro r hr
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp
    dsimp only
    rw [← smul_eq_mul, ← map_smul, pow_smul_newtonField_smul hd1 hr hθ]
  have hint2 : Integrable (Function.uncurry fun (r : ℝ)
      (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
        fderiv ℝ φ (c + r • (θ : EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) := by
    have hcont : Continuous (Function.uncurry fun (r : ℝ)
        (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
          fderiv ℝ φ (c + r • (θ : EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d))) := by
      have h1 : Continuous fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          c + p.1 • (p.2 : EuclideanSpace ℝ (Fin d)) := by fun_prop
      exact (hD.comp h1).clm_apply (continuous_subtype_val.comp continuous_snd)
    have h1 : IntegrableOn (fun _ : ℝ => B) (Set.Iic (ρ + ‖c‖)) (volume.restrict (Set.Ioi 0)) := by
      rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iic, Set.inter_comm,
        Set.Ioi_inter_Iic]
      exact integrableOn_const (by simp)
    have h2 : Integrable ((Set.Iic (ρ + ‖c‖)).indicator fun _ : ℝ => B)
        (volume.restrict (Set.Ioi 0)) := (integrable_indicator_iff measurableSet_Iic).2 h1
    have h3 := h2.mul_prod (integrable_const (1 : ℝ)
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere))
    refine h3.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hθ : ‖(p.2 : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp
    by_cases hr : p.1 ≤ ρ + ‖c‖
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hr), mul_one]
      calc ‖fderiv ℝ φ (c + p.1 • (p.2 : EuclideanSpace ℝ (Fin d)))
            (p.2 : EuclideanSpace ℝ (Fin d))‖
          ≤ ‖fderiv ℝ φ (c + p.1 • (p.2 : EuclideanSpace ℝ (Fin d)))‖
            * ‖(p.2 : EuclideanSpace ℝ (Fin d))‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ B := by
          rw [hθ, mul_one]
          exact hB _
    · rw [Set.indicator_of_notMem (by simpa using hr), zero_mul]
      have hlt : ρ < ‖c + p.1 • (p.2 : EuclideanSpace ℝ (Fin d))‖ := by
        have h4 := norm_sub_norm_le (p.1 • (p.2 : EuclideanSpace ℝ (Fin d))) (-c)
        rw [sub_neg_eq_add, norm_neg, norm_smul, hθ, Real.norm_eq_abs, mul_one,
          add_comm (p.1 • (p.2 : EuclideanSpace ℝ (Fin d))) c] at h4
        have := le_abs_self p.1
        have := norm_nonneg c
        linarith [not_le.1 hr]
      simp [Function.uncurry, fderiv_eq_zero_of_lt_norm hρ hlt]
  rw [hshift, integral_eq_integral_Ioi_sphere hd1 hint,
    setIntegral_congr_fun measurableSet_Ioi hpoint,
    integral_integral_swap
      (f := fun (r : ℝ) (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
        fderiv ℝ φ (c + r • (θ : EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d)))
      hint2]
  have hray : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫ r in Set.Ioi (0 : ℝ),
        fderiv ℝ φ (c + r • (θ : EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d))
      = -φ c := fun θ => integral_Ioi_fderiv_ray hφ hsupp c (by simp)
  simp only [hray, integral_const, Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin,
    smul_eq_mul]
  simp only [unitBallVolume, Measure.real]
  ring

end CERW.Generic.Newton
