import CERW.Generic.Kernel.NewtonField
import CERW.Generic.Kernel.Modulus
import CERW.Model.Potential
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The flux of the Newtonian field through a sphere

`flux c r = r^{d-1} ∫_{S^{d-1}} θ · K(rθ - c) dσ(θ)` is the flux of `K(· - c)` through the sphere
of radius `r`. Gauss's law says it is `σ_d` when `|c| < r` and `0` when `|c| > r`. This file
records the two analytic facts used to identify it: continuity away from `r = |c|`, and the limit
`σ_d` as `r → ∞`. It also records the swap identity `u · K(ru - sθ) = θ · K(rθ - su)` for unit
vectors, which turns the kernel average `eq:kernel-average` into a flux without any rotation
invariance.
-/

namespace CERW.Generic.Newton

open MeasureTheory Filter Topology CERW CERW.Generic.Kernel

variable {d : ℕ}


/-- The flux `r^{d-1} ∫_S θ · K(rθ - c) dσ(θ)` of the Newtonian field of a point source at `c`
through the sphere of radius `r`. -/
noncomputable def flux (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) : ℝ :=
  r ^ (d - 1) * ∫ θ, inner ℝ (θ : EuclideanSpace ℝ (Fin d))
    (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere


/-- The Newtonian field is continuous away from the origin. -/
private lemma continuousAt_newtonField_of_ne {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    ContinuousAt newtonField v := by
  unfold newtonField
  exact (ContinuousAt.inv₀ (continuous_norm.continuousAt.pow d)
    (pow_ne_zero d (norm_ne_zero_iff.mpr hv))).smul continuousAt_id

theorem inner_newtonField_swap {u θ : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hθ : ‖θ‖ = 1)
    (r s : ℝ) :
    inner ℝ u (newtonField (r • u - s • θ)) = inner ℝ θ (newtonField (r • θ - s • u)) := by
  have huu : inner ℝ u u = 1 := by simp [hu]
  have hθθ : inner ℝ θ θ = 1 := by simp [hθ]
  have hnum : inner ℝ u (r • u - s • θ) = inner ℝ θ (r • θ - s • u) := by
    rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
      inner_smul_right, inner_smul_right]
    rw [huu, hθθ, real_inner_comm θ u]
  have h2 : ‖r • u - s • θ‖ ^ 2 = ‖r • θ - s • u‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real]
    rw [norm_smul, norm_smul, norm_smul, norm_smul, hu, hθ]
    simp only [mul_one]
    rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      real_inner_comm θ u]
  have hnorm : ‖r • u - s • θ‖ = ‖r • θ - s • u‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  rw [inner_newtonField, inner_newtonField, hnum, hnorm]


/-- The spherical integral `∫ θ · K(rθ - c) dσ` is continuous in `r` for `r > 0`,
`r ≠ |c|`. -/
private lemma continuousAt_flux_integral (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d)) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hrc : r₀ ≠ ‖c‖) :
    ContinuousAt (fun r : ℝ => ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) r₀ := by
  set δ : ℝ := min (|r₀ - ‖c‖| / 2) (r₀ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδle1 : δ ≤ |r₀ - ‖c‖| / 2 := min_le_left _ _
  have hδle2 : δ ≤ r₀ / 2 := min_le_right _ _
  set bound : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ :=
    fun _ => δ ^ (1 - (d : ℝ)) with hbounddef
  have hF_meas : ∀ᶠ r in 𝓝 r₀, AEStronglyMeasurable
      (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        inner ℝ (θ : EuclideanSpace ℝ (Fin d))
          (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c)))
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere :=
    Filter.Eventually.of_forall fun r => by
      have h1 : Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          (θ : EuclideanSpace ℝ (Fin d))) := measurable_subtype_coe
      have h2 : Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          r • (θ : EuclideanSpace ℝ (Fin d)) - c) :=
        ((measurable_const (a := r)).smul h1).sub (measurable_const (a := c))
      have h3 : Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c)) :=
        measurable_newtonField.comp h2
      exact (h1.inner h3).aestronglyMeasurable
  have hbound : ∀ᶠ r in 𝓝 r₀, ∀ᵐ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere,
      ‖inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))‖ ≤ bound θ := by
    filter_upwards [Metric.ball_mem_nhds r₀ hδpos] with r hr
    refine Filter.Eventually.of_forall fun θ => ?_
    have hθn : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      rw [← dist_zero_right]
      exact Metric.mem_sphere.mp θ.2
    have hrdist : |r - r₀| < δ := by
      rw [Metric.mem_ball, Real.dist_eq] at hr
      exact hr
    have hrpos : 0 < r := by
      have h2 : |r - r₀| < r₀ / 2 := lt_of_lt_of_le hrdist hδle2
      have h3 := (abs_lt.mp h2).1
      linarith
    have hnorm : δ ≤ ‖r • (θ : EuclideanSpace ℝ (Fin d)) - c‖ := by
      have h1 : |‖r • (θ : EuclideanSpace ℝ (Fin d))‖ - ‖c‖| ≤
          ‖r • (θ : EuclideanSpace ℝ (Fin d)) - c‖ := abs_norm_sub_norm_le _ _
      have h2 : ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hθn, mul_one]
      rw [h2] at h1
      have h3 : δ ≤ |r - ‖c‖| := by
        have htri : |r₀ - ‖c‖| ≤ |r - r₀| + |r - ‖c‖| := by
          calc |r₀ - ‖c‖| = |(r₀ - r) + (r - ‖c‖)| := by ring_nf
            _ ≤ |r₀ - r| + |r - ‖c‖| := abs_add_le _ _
            _ = |r - r₀| + |r - ‖c‖| := by rw [abs_sub_comm]
        have h4 : 2 * δ ≤ |r₀ - ‖c‖| := by linarith
        linarith
      linarith
    have hnf : ‖newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c)‖ ≤
        δ ^ (1 - (d : ℝ)) := by
      rw [norm_newtonField hd]
      exact Real.rpow_le_rpow_of_nonpos hδpos hnorm (by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    calc ‖inner ℝ (θ : EuclideanSpace ℝ (Fin d))
          (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))‖
        = |inner ℝ (θ : EuclideanSpace ℝ (Fin d))
          (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))| :=
          Real.norm_eq_abs _
      _ ≤ ‖(θ : EuclideanSpace ℝ (Fin d))‖ *
          ‖newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c)‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c)‖ := by
          rw [hθn, one_mul]
      _ ≤ bound θ := hnf
  have hbound_int : Integrable bound (volume :
      Measure (EuclideanSpace ℝ (Fin d))).toSphere := integrable_const _
  have hcont : ∀ᵐ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere,
      ContinuousAt (fun r : ℝ => inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))) r₀ := by
    refine Filter.Eventually.of_forall fun θ => ?_
    have hθn : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      rw [← dist_zero_right]
      exact Metric.mem_sphere.mp θ.2
    have hv : r₀ • (θ : EuclideanSpace ℝ (Fin d)) - c ≠ 0 := by
      intro h
      have hc : r₀ • (θ : EuclideanSpace ℝ (Fin d)) = c := sub_eq_zero.mp h
      have h2 : r₀ = ‖c‖ := by
        have := congrArg norm hc
        rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hr₀, hθn, mul_one] at this
      exact hrc h2
    have harg : ContinuousAt
        (fun r : ℝ => r • (θ : EuclideanSpace ℝ (Fin d)) - c) r₀ :=
      (continuousAt_id.smul continuousAt_const).sub continuousAt_const
    exact continuousAt_const.inner ((continuousAt_newtonField_of_ne hv).tendsto.comp harg.tendsto)
  exact continuousAt_of_dominated hF_meas hbound hbound_int hcont


theorem continuousOn_flux (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d)) :
    ContinuousOn (flux c) {r | 0 < r ∧ r ≠ ‖c‖} := by
  have hs : IsOpen {r : ℝ | 0 < r ∧ r ≠ ‖c‖} := by
    have h1 : IsOpen {r : ℝ | 0 < r} := isOpen_lt continuous_const continuous_id
    have h2 : IsOpen {r : ℝ | r ≠ ‖c‖} := isOpen_ne
    exact h1.inter h2
  rw [IsOpen.continuousOn_iff hs]
  intro r₀ hr₀
  have hint := continuousAt_flux_integral hd c hr₀.1 hr₀.2
  unfold flux
  exact (continuousAt_id.pow (d - 1)).mul hint


/-- For `r > 0` and `d ≥ 1`, `r^{d-1} · 2r / (r/2)^d = 2^{d+1}`. -/
private lemma pow_sub_mul_div_eq (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    r ^ (d - 1) * (2 * r) / (r / 2) ^ d = 2 ^ (d + 1) := by
  have hpow : r ^ d = r ^ (d - 1) * r := by
    conv_lhs => rw [← Nat.sub_add_cancel hd]
    rw [pow_succ]
  rw [div_pow, hpow]
  field_simp
  ring


/-- For `d ≥ 2`, the rescaled flux integrand tends to `1` along each sphere direction. -/
private lemma tendsto_flux_integrand (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Tendsto (fun r : ℝ => r ^ (d - 1) *
      inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))) atTop (𝓝 1) := by
  have hθn : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
    rw [← dist_zero_right]
    exact Metric.mem_sphere.mp θ.2
  have heq : (fun r : ℝ => r ^ (d - 1) *
      inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))) =ᶠ[atTop]
      (fun r : ℝ => (1 - inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c / r) /
        ‖(θ : EuclideanSpace ℝ (Fin d)) - r⁻¹ • c‖ ^ d) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [inner_newtonField]
    have hθθ : inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (θ : EuclideanSpace ℝ (Fin d)) = 1 := by
      simp [hθn]
    have hinner : inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (r • (θ : EuclideanSpace ℝ (Fin d)) - c) =
        r - inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c := by
      rw [inner_sub_right, inner_smul_right, hθθ, mul_one]
    have hnorm : ‖r • (θ : EuclideanSpace ℝ (Fin d)) - c‖ =
        r * ‖(θ : EuclideanSpace ℝ (Fin d)) - r⁻¹ • c‖ := by
      have hsmul : r • (θ : EuclideanSpace ℝ (Fin d)) - c =
          r • ((θ : EuclideanSpace ℝ (Fin d)) - r⁻¹ • c) := by
        rw [smul_sub, smul_inv_smul₀ hr.ne']
      rw [hsmul, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [hinner, hnorm, mul_pow]
    have hd1 : 1 ≤ d := by omega
    have hpow : r ^ d = r ^ (d - 1) * r := by
      conv_lhs => rw [← Nat.sub_add_cancel hd1]
      rw [pow_succ]
    rw [hpow]
    field_simp
  have h1 : Tendsto (fun r : ℝ => 1 - inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c / r)
      atTop (𝓝 1) := by
    have hA : Tendsto (fun r : ℝ => inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c / r)
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c)).mul
          (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa using tendsto_const_nhds.sub hA
  have h2 : Tendsto (fun r : ℝ =>
      ‖(θ : EuclideanSpace ℝ (Fin d)) - r⁻¹ • c‖ ^ d) atTop (𝓝 1) := by
    have h0 : Tendsto (fun r : ℝ => r⁻¹ • c) atTop
        (𝓝 (0 : EuclideanSpace ℝ (Fin d))) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul (tendsto_const_nhds (x := c))
    have hsub : Tendsto (fun r : ℝ => (θ : EuclideanSpace ℝ (Fin d)) - r⁻¹ • c)
        atTop (𝓝 ((θ : EuclideanSpace ℝ (Fin d)) - 0)) :=
      tendsto_const_nhds.sub h0
    have hnorm := (continuous_norm.tendsto _).comp hsub
    have hpow := hnorm.pow d
    rw [sub_zero, hθn] at hpow
    simpa using hpow
  have hnice : Tendsto (fun r : ℝ =>
      (1 - inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c / r) /
        ‖(θ : EuclideanSpace ℝ (Fin d)) - r⁻¹ • c‖ ^ d) atTop (𝓝 1) := by
    have hdiv := h1.div h2 (by norm_num : (1 : ℝ) ≠ 0)
    have hfun : (fun r : ℝ => 1 - inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c / r) /
        (fun r : ℝ => ‖(θ : EuclideanSpace ℝ (Fin d)) - r⁻¹ • c‖ ^ d) =
        (fun r : ℝ => (1 - inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c / r) /
          ‖(θ : EuclideanSpace ℝ (Fin d)) - r⁻¹ • c‖ ^ d) := by
      ext r
      rfl
    rw [hfun] at hdiv
    simpa using hdiv
  exact Tendsto.congr' heq.symm hnice



/-- The rescaled flux integrand is bounded by `2^{d+1}` for `r ≥ 2|c| + 1`. -/
private lemma norm_flux_integrand_le (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hr : 2 * ‖c‖ + 1 ≤ r) (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ‖r ^ (d - 1) * inner ℝ (θ : EuclideanSpace ℝ (Fin d))
      (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))‖ ≤ 2 ^ (d + 1) := by
  have hθn : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
    rw [← dist_zero_right]
    exact Metric.mem_sphere.mp θ.2
  have hrpos : 0 < r := by linarith [norm_nonneg c]
  have hθθ : inner ℝ (θ : EuclideanSpace ℝ (Fin d))
      (θ : EuclideanSpace ℝ (Fin d)) = 1 := by
    simp [hθn]
  set A : ℝ := inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c with hAdef
  set N : ℝ := ‖r • (θ : EuclideanSpace ℝ (Fin d)) - c‖ with hNdef
  have hinner : inner ℝ (θ : EuclideanSpace ℝ (Fin d))
      (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c)) = (r - A) / N ^ d := by
    rw [inner_newtonField, hNdef]
    have h1 : inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (r • (θ : EuclideanSpace ℝ (Fin d)) - c) = r - A := by
      rw [inner_sub_right, inner_smul_right, hθθ, mul_one, hAdef]
    rw [h1]
  have hN_lower : r / 2 ≤ N := by
    have h1 : |‖r • (θ : EuclideanSpace ℝ (Fin d))‖ - ‖c‖| ≤ N := by
      rw [hNdef]
      exact abs_norm_sub_norm_le _ _
    have h2 : ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hθn, mul_one]
    rw [h2] at h1
    have h3 : 0 ≤ r - ‖c‖ := by linarith [norm_nonneg c]
    rw [abs_of_nonneg h3] at h1
    linarith [norm_nonneg c]
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN_lower
  have hnum : |r - A| ≤ 2 * r := by
    have hAc : |A| ≤ ‖c‖ := by
      rw [hAdef]
      calc |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) c| ≤
            ‖(θ : EuclideanSpace ℝ (Fin d))‖ * ‖c‖ := abs_real_inner_le_norm _ _
        _ = ‖c‖ := by rw [hθn, one_mul]
    have h1 : |r - A| ≤ |r| + |A| := by
      calc |r - A| = |r + (-A)| := by ring_nf
        _ ≤ |r| + |-A| := abs_add_le _ _
        _ = |r| + |A| := by rw [abs_neg]
    rw [abs_of_pos hrpos] at h1
    linarith [norm_nonneg c]
  calc ‖r ^ (d - 1) * inner ℝ (θ : EuclideanSpace ℝ (Fin d))
        (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))‖
      = |r ^ (d - 1) * ((r - A) / N ^ d)| := by rw [Real.norm_eq_abs, hinner]
    _ = r ^ (d - 1) * |r - A| / N ^ d := by
        rw [abs_mul, abs_div, abs_of_nonneg (pow_nonneg hrpos.le _), abs_of_pos (pow_pos hNpos d)]
        ring
    _ ≤ r ^ (d - 1) * (2 * r) / (r / 2) ^ d := by
        gcongr
    _ = 2 ^ (d + 1) := pow_sub_mul_div_eq (by omega) hrpos


theorem tendsto_flux_atTop (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d)) :
    Tendsto (flux c) atTop (𝓝 (d * unitBallVolume d)) := by
  let F : ℝ → Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ := fun r θ =>
    r ^ (d - 1) * inner ℝ (θ : EuclideanSpace ℝ (Fin d))
      (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))
  let bound : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ :=
    fun _ => (2 : ℝ) ^ (d + 1)
  let μ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have hF_meas : ∀ᶠ r in atTop, AEStronglyMeasurable (F r) μ :=
    Eventually.of_forall fun r => by
      have h1 : Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          (θ : EuclideanSpace ℝ (Fin d))) := measurable_subtype_coe
      have h2 : Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          r • (θ : EuclideanSpace ℝ (Fin d)) - c) :=
        ((measurable_const (a := r)).smul h1).sub (measurable_const (a := c))
      have h3 : Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
          newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c)) :=
        measurable_newtonField.comp h2
      exact ((measurable_const (a := r ^ (d - 1))).mul (h1.inner h3)).aestronglyMeasurable
  have hbound : ∀ᶠ r in atTop, ∀ᵐ θ ∂μ, ‖F r θ‖ ≤ bound θ := by
    filter_upwards [eventually_ge_atTop (2 * ‖c‖ + 1)] with r hr
    refine Eventually.of_forall fun θ => ?_
    exact norm_flux_integrand_le hd c hr θ
  have hbound_int : Integrable bound μ := integrable_const _
  have hlim : ∀ᵐ θ ∂μ, Tendsto (fun r : ℝ => F r θ) atTop (𝓝 1) :=
    Eventually.of_forall fun θ => tendsto_flux_integrand hd c θ
  have hDCT := tendsto_integral_filter_of_dominated_convergence bound hF_meas hbound
    hbound_int hlim
  have htarget : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, (1 : ℝ) ∂μ) =
      d * unitBallVolume d := by
    rw [integral_const, smul_eq_mul, mul_one]
    change ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).real Set.univ =
      d * unitBallVolume d
    rw [MeasureTheory.Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
    rfl
  rw [htarget] at hDCT
  have hflux_eq : ∀ r, flux c r = ∫ θ, F r θ ∂μ := by
    intro r
    simp only [flux, F, μ]
    rw [integral_const_mul]
  exact Tendsto.congr' (Eventually.of_forall fun r => (hflux_eq r).symm) hDCT


end CERW.Generic.Newton
