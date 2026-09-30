import CERW.Generic.Newton.Gauss
import CERW.Generic.Newton.Flux
import CERW.Generic.Kernel.Integrable

/-!
# Gauss's flux theorem

The flux of the Newtonian field of a point source `c` through the sphere of radius `r` is `σ_d`
when `|c| < r`, and `0` when `r < |c|`. Testing Gauss's law against the radial function
`φ(v) = ψ(|v|)` gives `∫_0^∞ ψ'(r) flux_c(r) dr = -σ_d ψ(|c|)` for `ψ ∈ C¹` supported in a
compact subinterval of `(0, ∞)`. Choosing `ψ'` to approximate `δ_{r₁} - δ_{r₂}` identifies the jump
of the flux across `|c|`. Continuity away from `|c|` and the limit `σ_d` at infinity then give
the flux itself.
-/

namespace CERW.Generic.Newton

open MeasureTheory Filter Topology CERW CERW.Generic.Kernel

variable {d : ℕ}

/-- Away from the origin, the norm has Fréchet derivative `w ↦ ⟨v, w⟩ / |v|`. -/
private lemma hasFDerivAt_norm_of_ne {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) (‖v‖⁻¹ • innerSL ℝ v) v := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h := ((hasStrictFDerivAt_norm_sq v).hasFDerivAt).sqrt (by positivity)
  have hfun : (fun y : EuclideanSpace ℝ (Fin d) => √(‖y‖ ^ 2)) = fun x => ‖x‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  rw [hfun, Real.sqrt_sq hpos.le] at h
  have h2 : (1 / (2 * ‖v‖)) • (2 • innerSL ℝ v) = ‖v‖⁻¹ • innerSL ℝ v := by
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    field_simp
    ring
  rwa [h2] at h

/-- The radial profile `v ↦ ψ(|v|)` of a `C¹` function supported in `[a, b] ⊂ (0, ∞)` is `C¹`. -/
private lemma contDiff_radial {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ψ ⊆ Set.Icc a b) :
    ContDiff ℝ 1 (fun v : EuclideanSpace ℝ (Fin d) => ψ ‖v‖) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst hv
    have hev : (fun x : EuclideanSpace ℝ (Fin d) => ψ ‖x‖) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) ha] with x hx
      by_contra hne
      have h1 := (hsupp hne).1
      rw [mem_ball_zero_iff] at hx
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact hψ.contDiffAt.comp v (contDiffAt_norm ℝ hv)

/-- The radial profile of a function supported in `[a, b]` has compact support. -/
private lemma hasCompactSupport_radial {ψ : ℝ → ℝ} {a b : ℝ}
    (hsupp : Function.support ψ ⊆ Set.Icc a b) :
    HasCompactSupport (fun v : EuclideanSpace ℝ (Fin d) => ψ ‖v‖) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) b)
    fun x hx => ?_
  by_contra hne
  exact hx (mem_closedBall_zero_iff.2 (hsupp hne).2)

/-- The derivative of the radial profile is the radial derivative times the unit direction. -/
private lemma fderiv_radial_apply {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ψ ⊆ Set.Icc a b) (v w : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => ψ ‖x‖) v w
      = deriv ψ ‖v‖ * inner ℝ (unitDir v) w := by
  by_cases hv : v = 0
  · subst hv
    have hev : (fun x : EuclideanSpace ℝ (Fin d) => ψ ‖x‖) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) ha] with x hx
      by_contra hne
      have h1 := (hsupp hne).1
      rw [mem_ball_zero_iff] at hx
      linarith
    rw [hev.fderiv_eq]
    simp
  · have h1 := ((hψ.differentiable one_ne_zero) ‖v‖).hasDerivAt.comp_hasFDerivAt v
      (hasFDerivAt_norm_of_ne hv)
    have h2 : fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => ψ ‖x‖) v
        = deriv ψ ‖v‖ • ‖v‖⁻¹ • innerSL ℝ v := h1.fderiv
    rw [h2]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, unitDir,
      real_inner_smul_left]

/-- The derivative of a `C¹` function supported in `[a, b]` is bounded and vanishes to the right
of `b`. -/
private lemma exists_bound_deriv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {a b : ℝ}
    (hsupp : Function.support ψ ⊆ Set.Icc a b) :
    ∃ M : ℝ, (∀ r, |deriv ψ r| ≤ M) ∧ ∀ r, b < r → deriv ψ r = 0 := by
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hsub : Function.support (deriv ψ) ⊆ Set.Icc a b :=
    (support_deriv_subset (f := ψ)).trans (closure_minimal hsupp isClosed_Icc)
  have hcpt : HasCompactSupport (deriv ψ) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) fun x hx => ?_
    by_contra hne
    exact hx (hsub hne)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcpt
  refine ⟨M, fun r => ?_, fun r hr => ?_⟩
  · simpa [Real.norm_eq_abs] using hM r
  · by_contra hne
    exact absurd (hsub hne).2 (not_le.2 hr)

/-- The Gauss integrand `v ↦ ψ'(|v|) ⟨u_v, K(v - c)⟩` of a radial test function is integrable. -/
private lemma integrable_radial_integrand (hd : 2 ≤ d) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {a b : ℝ} (hsupp : Function.support ψ ⊆ Set.Icc a b) (c : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      deriv ψ ‖v‖ * inner ℝ (unitDir v) (newtonField (v - c))) := by
  obtain ⟨M, hM, hzero⟩ := exists_bound_deriv hψ hsupp
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hR : 0 < |b| + ‖c‖ + 1 := by positivity
  have hbound : Integrable ((Metric.ball c (|b| + ‖c‖ + 1)).indicator
      (fun v : EuclideanSpace ℝ (Fin d) => M * ‖v - c‖ ^ (1 - (d : ℝ)))) :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2
      ((integrableOn_ball_and_integral_eq (by omega) c hR).1.const_mul M)
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      deriv ψ ‖v‖ * inner ℝ (unitDir v) (newtonField (v - c))) := by
    have h1 : Measurable fun v : EuclideanSpace ℝ (Fin d) => deriv ψ ‖v‖ :=
      ((hψ.continuous_deriv le_rfl).comp continuous_norm).measurable
    have h2 : Measurable (unitDir : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
      measurable_norm.inv.smul measurable_id
    exact h1.mul (h2.inner (measurable_newtonField.comp (measurable_id.sub_const c)))
  refine hbound.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  by_cases hv : v ∈ Metric.ball c (|b| + ‖c‖ + 1)
  · rw [Set.indicator_of_mem hv, ← norm_newtonField hd]
    calc ‖deriv ψ ‖v‖ * inner ℝ (unitDir v) (newtonField (v - c))‖
        = ‖deriv ψ ‖v‖‖ * ‖inner ℝ (unitDir v) (newtonField (v - c))‖ := norm_mul _ _
      _ ≤ M * (‖unitDir v‖ * ‖newtonField (v - c)‖) :=
          mul_le_mul (by simpa [Real.norm_eq_abs] using hM _) (norm_inner_le_norm _ _)
            (norm_nonneg _) hM0
      _ ≤ M * (1 * ‖newtonField (v - c)‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (norm_unitDir_le v) (norm_nonneg _)) hM0
      _ = M * ‖newtonField (v - c)‖ := by rw [one_mul]
  · rw [Set.indicator_of_notMem hv]
    have hv' : |b| + ‖c‖ + 1 ≤ ‖v - c‖ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    have h1 : ‖v - c‖ ≤ ‖v‖ + ‖c‖ := norm_sub_le v c
    have hb : b < ‖v‖ := by linarith [le_abs_self b]
    rw [hzero _ hb, zero_mul, norm_zero]

/-- On a sphere of radius `r > 0`, the unit direction of `rθ` is `θ`. -/
private lemma unitDir_smul {r : ℝ} (hr : 0 < r) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    unitDir (r • θ) = θ := by
  rw [unitDir, norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hr, mul_one, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul]

/-- A `C¹` monotone step rising from `0` on `(-∞, p - h]` to `1` on `[p + h, ∞)`. -/
private lemma exists_step {p h : ℝ} (hh : 0 < h) :
    ∃ S : ℝ → ℝ, ContDiff ℝ 1 S ∧ Monotone S ∧ (∀ r, r ≤ p - h → S r = 0) ∧
      ∀ r, p + h ≤ r → S r = 1 := by
  have hinv : 0 < (2 * h)⁻¹ := by positivity
  refine ⟨fun r => Real.smoothTransition ((2 * h)⁻¹ * (r - (p - h))), ?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ 1 Real.smoothTransition :=
      (Real.smoothTransition.contDiff (n := ⊤)).of_le (by exact_mod_cast le_top)
    exact h1.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  · intro x y hxy
    refine Real.smoothTransition.monotone ?_
    have : (2 * h)⁻¹ * (x - (p - h)) ≤ (2 * h)⁻¹ * (y - (p - h)) := by gcongr
    exact this
  · intro r hr
    refine Real.smoothTransition.zero_of_nonpos ?_
    exact mul_nonpos_of_nonneg_of_nonpos hinv.le (by linarith)
  · intro r hr
    refine Real.smoothTransition.one_of_one_le ?_
    have h2 : 2 * h ≤ r - (p - h) := by linarith
    calc (1 : ℝ) = (2 * h)⁻¹ * (2 * h) := by field_simp
      _ ≤ (2 * h)⁻¹ * (r - (p - h)) := by gcongr

/-- The derivative of a step vanishes off the transition interval. -/
private lemma deriv_step_eq_zero {S : ℝ → ℝ} {p h : ℝ} (h0 : ∀ r, r ≤ p - h → S r = 0)
    (h1 : ∀ r, p + h ≤ r → S r = 1) {r : ℝ} (hr : r ∉ Set.Icc (p - h) (p + h)) :
    deriv S r = 0 := by
  rcases lt_or_ge r (p - h) with hlt | hge
  · have hev : S =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hlt] with x hx using h0 x (le_of_lt hx)
    rw [hev.deriv_eq, deriv_const]
  · have hgt : p + h < r := by
      by_contra hle
      exact hr ⟨hge, not_lt.1 hle⟩
    have hev : S =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hgt] with x hx using h1 x (le_of_lt hx)
    rw [hev.deriv_eq, deriv_const]

/-- The derivative of a step integrates to `1` over its transition interval. -/
private lemma integral_deriv_step {S : ℝ → ℝ} {p h : ℝ} (hh : 0 < h) (hS : ContDiff ℝ 1 S)
    (h0 : ∀ r, r ≤ p - h → S r = 0) (h1 : ∀ r, p + h ≤ r → S r = 1) :
    ∫ r in Set.Icc (p - h) (p + h), deriv S r = 1 := by
  have hle : p - h ≤ p + h := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_deriv_eq_sub' S rfl (fun x _ => hS.differentiable one_ne_zero x)
      (hS.continuous_deriv le_rfl).continuousOn, h1 _ le_rfl, h0 _ le_rfl]
  norm_num

/-- Averaging `Φ` against the derivative of a step of width `2h` about `p` recovers `Φ p` up to the
oscillation `ε` of `Φ` on `[p - h, p + h]`. -/
private lemma step_deriv_integral_approx {S Φ : ℝ → ℝ} {p h ε : ℝ} (hh : 0 < h) (hph : h < p)
    (hS : ContDiff ℝ 1 S) (hmono : Monotone S) (h0 : ∀ r, r ≤ p - h → S r = 0)
    (h1 : ∀ r, p + h ≤ r → S r = 1) (hΦ : ContinuousOn Φ (Set.Icc (p - h) (p + h)))
    (hε : ∀ t ∈ Set.Icc (p - h) (p + h), |Φ t - Φ p| ≤ ε) :
    IntegrableOn (fun r => deriv S r * Φ r) (Set.Ioi 0) ∧
      |(∫ r in Set.Ioi (0 : ℝ), deriv S r * Φ r) - Φ p| ≤ ε := by
  have hcontD : Continuous (deriv S) := hS.continuous_deriv le_rfl
  have hzero : ∀ r, r ∉ Set.Icc (p - h) (p + h) → deriv S r = 0 :=
    fun r hr => deriv_step_eq_zero h0 h1 hr
  have hsub : Set.Icc (p - h) (p + h) ⊆ Set.Ioi (0 : ℝ) := fun x hx =>
    lt_of_lt_of_le (by linarith) hx.1
  have hint_Icc : IntegrableOn (fun r => deriv S r * Φ r) (Set.Icc (p - h) (p + h)) :=
    (hcontD.continuousOn.mul hΦ).integrableOn_Icc
  have hdiff0 : ∀ x ∈ Set.Ioi (0 : ℝ) \ Set.Icc (p - h) (p + h),
      deriv S x * Φ x = 0 := fun x hx => by rw [hzero x hx.2, zero_mul]
  have hint : IntegrableOn (fun r => deriv S r * Φ r) (Set.Ioi 0) :=
    hint_Icc.of_forall_sdiff_eq_zero measurableSet_Ioi hdiff0
  refine ⟨hint, ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hdiff0]
  have hD_int : IntegrableOn (deriv S) (Set.Icc (p - h) (p + h)) :=
    hcontD.continuousOn.integrableOn_Icc
  have hone := integral_deriv_step hh hS h0 h1
  have hΦp : Φ p = ∫ r in Set.Icc (p - h) (p + h), deriv S r * Φ p := by
    rw [integral_mul_const, hone, one_mul]
  have hint2 : IntegrableOn (fun r => deriv S r * Φ p) (Set.Icc (p - h) (p + h)) :=
    hD_int.mul_const _
  rw [hΦp, ← integral_sub hint_Icc hint2]
  have hnn : ∀ r, 0 ≤ deriv S r := fun r => hmono.deriv_nonneg
  have hbound : ‖∫ r in Set.Icc (p - h) (p + h), (deriv S r * Φ r - deriv S r * Φ p)‖
      ≤ ∫ r in Set.Icc (p - h) (p + h), ε * deriv S r := by
    refine norm_integral_le_of_norm_le (hD_int.const_mul ε) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn r), mul_comm]
    exact mul_le_mul_of_nonneg_right (hε r hr) (hnn r)
  rw [integral_const_mul, hone, mul_one] at hbound
  simpa [Real.norm_eq_abs] using hbound

/-- Near a radius `r > 0` different from `|c|`, the flux stays within `ε` of its value at `r` on a
closed interval avoiding `0` and `|c|`. -/
private lemma exists_flux_nbhd (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    (hrc : r ≠ ‖c‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - r| ≤ δ →
      (0 < t ∧ t ≠ ‖c‖) ∧ |flux c t - flux c r| ≤ ε := by
  have hU : IsOpen {r : ℝ | 0 < r ∧ r ≠ ‖c‖} :=
    (isOpen_lt continuous_const continuous_id).inter isOpen_ne
  have hmem : {r : ℝ | 0 < r ∧ r ≠ ‖c‖} ∈ 𝓝 r := hU.mem_nhds ⟨hr, hrc⟩
  have hmem' : ∀ᶠ t in 𝓝 r, 0 < t ∧ t ≠ ‖c‖ := hmem
  have hcont : ContinuousAt (flux c) r := (continuousOn_flux hd c).continuousAt hmem
  have hev : ∀ᶠ t in 𝓝 r, (0 < t ∧ t ≠ ‖c‖) ∧ |flux c t - flux c r| < ε := by
    refine hmem'.and ?_
    filter_upwards [hcont.eventually (Metric.ball_mem_nhds (flux c r) hε)] with t ht
    rwa [Real.dist_eq] at ht
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ / 2, by positivity, fun t ht => ?_⟩
  have htb : t ∈ Metric.ball r δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    linarith
  exact ⟨(hball t htb).1, (hball t htb).2.le⟩

/-- A step of width `2h` about `p` takes the value `1` or `0` at a point `x` at distance more than
`h` from `p`, according to the side of `p` on which `x` lies. -/
private lemma step_apply_of_gap {S : ℝ → ℝ} {p h x : ℝ} (h0 : ∀ r, r ≤ p - h → S r = 0)
    (h1 : ∀ r, p + h ≤ r → S r = 1) (hgap : h < |x - p|) :
    S x = if p < x then 1 else 0 := by
  by_cases hpx : p < x
  · rw [if_pos hpx]
    rw [abs_of_pos (sub_pos.2 hpx)] at hgap
    exact h1 x (by linarith)
  · rw [if_neg hpx]
    have hxp : x ≤ p := not_lt.1 hpx
    rw [abs_of_nonpos (sub_nonpos.2 hxp)] at hgap
    exact h0 x (by linarith)

/-- Gauss's law against radial test functions identifies the jump of the flux: for radii
`0 < r₁ < r₂` different from `|c|`, `Φ(r₁) - Φ(r₂) = -σ_d (1[r₁ < |c|] - 1[r₂ < |c|])`. The
Gauss identity is taken as the hypothesis `hG`. -/
private lemma flux_sub_eq_of_gauss (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d))
    (hG : ∀ {ψ : ℝ → ℝ}, ContDiff ℝ 1 ψ → ∀ {a b : ℝ}, 0 < a →
      Function.support ψ ⊆ Set.Icc a b →
      ∫ r in Set.Ioi (0 : ℝ), deriv ψ r * flux c r = -(d * unitBallVolume d * ψ ‖c‖))
    {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) (hc1 : r₁ ≠ ‖c‖) (hc2 : r₂ ≠ ‖c‖) :
    flux c r₁ - flux c r₂ = -(d * unitBallVolume d *
      ((if r₁ < ‖c‖ then (1 : ℝ) else 0) - (if r₂ < ‖c‖ then (1 : ℝ) else 0))) := by
  have h2 : 0 < r₂ := h1.trans h12
  have key : ∀ ε : ℝ, 0 < ε → |flux c r₁ - flux c r₂ + d * unitBallVolume d *
      ((if r₁ < ‖c‖ then (1 : ℝ) else 0) - (if r₂ < ‖c‖ then (1 : ℝ) else 0))| ≤ 2 * ε := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, hnb₁⟩ := exists_flux_nbhd hd c h1 hc1 hε
    obtain ⟨δ₂, hδ₂, hnb₂⟩ := exists_flux_nbhd hd c h2 hc2 hε
    set h : ℝ := min δ₁ δ₂ with hhdef
    have hh : 0 < h := lt_min hδ₁ hδ₂
    have hh1 : h ≤ δ₁ := min_le_left _ _
    have hh2 : h ≤ δ₂ := min_le_right _ _
    have hr1 : h < r₁ := by
      have := (hnb₁ (r₁ - δ₁) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ₁])).1.1
      linarith
    have hgap1 : h < |‖c‖ - r₁| := by
      by_contra hle
      have := (hnb₁ ‖c‖ ((not_lt.1 hle).trans hh1)).1.2
      exact this rfl
    have hgap2 : h < |‖c‖ - r₂| := by
      by_contra hle
      have := (hnb₂ ‖c‖ ((not_lt.1 hle).trans hh2)).1.2
      exact this rfl
    obtain ⟨S₁, hS₁, hm₁, h01, h11⟩ := exists_step (p := r₁) hh
    obtain ⟨S₂, hS₂, hm₂, h02, h12'⟩ := exists_step (p := r₂) hh
    have hcont : ContinuousOn (flux c) {r | 0 < r ∧ r ≠ ‖c‖} := continuousOn_flux hd c
    obtain ⟨hI₁, hA₁⟩ := step_deriv_integral_approx (Φ := flux c) (ε := ε) hh hr1 hS₁ hm₁ h01 h11
      (hcont.mono fun t ht => (hnb₁ t (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)).1)
      fun t ht => (hnb₁ t (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2
    have hr2 : h < r₂ := by linarith
    obtain ⟨hI₂, hA₂⟩ := step_deriv_integral_approx (Φ := flux c) (ε := ε) hh hr2 hS₂ hm₂ h02 h12'
      (hcont.mono fun t ht => (hnb₂ t (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)).1)
      fun t ht => (hnb₂ t (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2
    have hψ : ContDiff ℝ 1 (fun r => S₁ r - S₂ r) := hS₁.sub hS₂
    have hsupp : Function.support (fun r => S₁ r - S₂ r) ⊆ Set.Icc (r₁ - h) (r₂ + h) := by
      intro r hr
      by_contra hnot
      apply hr
      simp only
      rcases lt_or_ge r (r₁ - h) with hlt | hge
      · rw [h01 r hlt.le, h02 r (by linarith), sub_zero]
      · have hgt : r₂ + h < r := by
          by_contra hle
          exact hnot ⟨hge, not_lt.1 hle⟩
        rw [h11 r (by linarith), h12' r hgt.le, sub_self]
    have hG' := hG hψ (a := r₁ - h) (b := r₂ + h) (by linarith) hsupp
    have hderiv : ∀ r, deriv (fun r => S₁ r - S₂ r) r = deriv S₁ r - deriv S₂ r := fun r =>
      deriv_sub ((hS₁.differentiable one_ne_zero) r) ((hS₂.differentiable one_ne_zero) r)
    simp only [hderiv, sub_mul] at hG'
    rw [integral_sub hI₁ hI₂] at hG'
    have hν₁ := step_apply_of_gap h01 h11 hgap1
    have hν₂ := step_apply_of_gap h02 h12' hgap2
    simp only [hν₁, hν₂] at hG'
    have hA₁' := abs_le.1 hA₁
    have hA₂' := abs_le.1 hA₂
    rw [abs_le]
    constructor <;> linarith [hA₁'.1, hA₁'.2, hA₂'.1, hA₂'.2]
  have hzero : |flux c r₁ - flux c r₂ + d * unitBallVolume d *
      ((if r₁ < ‖c‖ then (1 : ℝ) else 0) - (if r₂ < ‖c‖ then (1 : ℝ) else 0))| ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by
      have := key (ε / 2) (by positivity)
      linarith
  have := abs_nonpos_iff.1 hzero
  linarith

/-- Gauss's law against a radial test function: for `ψ ∈ C¹` supported in `[a, b] ⊂ (0, ∞)`,
`∫_{r > 0} ψ'(r) flux_c(r) dr = -σ_d ψ(|c|)`. -/
theorem integral_deriv_mul_flux (hd : 2 ≤ d) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support ψ ⊆ Set.Icc a b) (c : EuclideanSpace ℝ (Fin d)) :
    ∫ r in Set.Ioi (0 : ℝ), deriv ψ r * flux c r = -(d * unitBallVolume d * ψ ‖c‖) := by
  have hd1 : 1 ≤ d := by omega
  have hint := integrable_radial_integrand hd hψ hsupp c
  have hgauss := integral_fderiv_newtonField hd (contDiff_radial hψ ha hsupp)
    (hasCompactSupport_radial hsupp) c
  have hpt : ∀ v : EuclideanSpace ℝ (Fin d),
      fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => ψ ‖x‖) v (newtonField (v - c))
        = deriv ψ ‖v‖ * inner ℝ (unitDir v) (newtonField (v - c)) :=
    fun v => fderiv_radial_apply hψ ha hsupp v _
  have hpolar := integral_eq_integral_Ioi_sphere hd1 hint
  calc ∫ r in Set.Ioi (0 : ℝ), deriv ψ r * flux c r
      = ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * ∫ θ : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin d)) 1,
          deriv ψ ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ * inner ℝ
            (unitDir (r • (θ : EuclideanSpace ℝ (Fin d))))
            (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
        refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
        have hr' : 0 < r := hr
        have hθ : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
            ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := fun θ => by simp
        have hcongr : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
            deriv ψ ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ * inner ℝ
              (unitDir (r • (θ : EuclideanSpace ℝ (Fin d))))
              (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c))
            = deriv ψ r * inner ℝ (θ : EuclideanSpace ℝ (Fin d))
              (newtonField (r • (θ : EuclideanSpace ℝ (Fin d)) - c)) := by
          intro θ
          rw [unitDir_smul hr' (hθ θ), norm_smul, hθ θ, Real.norm_eq_abs, abs_of_pos hr',
            mul_one]
        simp only [hcongr]
        rw [integral_const_mul, flux]
        ring
    _ = ∫ v : EuclideanSpace ℝ (Fin d),
          deriv ψ ‖v‖ * inner ℝ (unitDir v) (newtonField (v - c)) := hpolar.symm
    _ = ∫ v : EuclideanSpace ℝ (Fin d),
          fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => ψ ‖x‖) v (newtonField (v - c)) := by
        simp only [hpt]
    _ = -(d * unitBallVolume d * ψ ‖c‖) := hgauss


/-- Gauss's flux theorem: `flux_c(r) = σ_d` if `|c| < r` and `0` if `r < |c|`. -/
theorem flux_eq (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    (hrc : r ≠ ‖c‖) :
    flux c r = if ‖c‖ < r then d * unitBallVolume d else 0 := by
  have hG : ∀ {ψ : ℝ → ℝ}, ContDiff ℝ 1 ψ → ∀ {a b : ℝ}, 0 < a →
      Function.support ψ ⊆ Set.Icc a b →
      ∫ r in Set.Ioi (0 : ℝ), deriv ψ r * flux c r = -(d * unitBallVolume d * ψ ‖c‖) :=
    fun {_} hψ {_ _} ha hsupp => integral_deriv_mul_flux hd hψ ha hsupp c
  have hev : ∀ᶠ R in atTop, flux c R - d * unitBallVolume d *
      (if r < ‖c‖ then (1 : ℝ) else 0) = flux c r := by
    filter_upwards [eventually_gt_atTop (max r ‖c‖)] with R hR
    have hR1 : r < R := lt_of_le_of_lt (le_max_left _ _) hR
    have hR2 : ‖c‖ < R := lt_of_le_of_lt (le_max_right _ _) hR
    have h := flux_sub_eq_of_gauss hd c hG hr hR1 hrc hR2.ne'
    rw [if_neg (not_lt.2 hR2.le)] at h
    linarith
  have hlim : Tendsto (fun R : ℝ => flux c R - d * unitBallVolume d *
      (if r < ‖c‖ then (1 : ℝ) else 0)) atTop
      (𝓝 (d * unitBallVolume d - d * unitBallVolume d * (if r < ‖c‖ then (1 : ℝ) else 0))) :=
    (tendsto_flux_atTop hd c).sub_const _
  have hconst : Tendsto (fun R : ℝ => flux c R - d * unitBallVolume d *
      (if r < ‖c‖ then (1 : ℝ) else 0)) atTop (𝓝 (flux c r)) :=
    tendsto_const_nhds.congr' (hev.mono fun R hR => hR.symm)
  have hval := tendsto_nhds_unique hconst hlim
  by_cases hlt : ‖c‖ < r
  · rw [if_pos hlt, hval, if_neg (not_lt.2 hlt.le)]
    ring
  · have hrlt : r < ‖c‖ := lt_of_le_of_ne (not_lt.1 hlt) hrc
    rw [if_neg hlt, hval, if_pos hrlt]
    ring

end CERW.Generic.Newton
