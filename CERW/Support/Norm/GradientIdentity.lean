import CERW.Support.Norm.BallLayer
import CERW.Generic.Kernel.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The gradient identity for Lipschitz functions of compact support

For every Lipschitz function `f : ℝ^d → ℝ` of compact support, `d ≥ 2`, and every `y ∈ ℝ^d`,
`eq:gradient-identity` reads
`∫_{ℝ^d} ∇f(v) · (v - y) |v - y|^{-d} dv = - d ω_d f(y)`,
with `∇f` the gradient (Mathlib's `gradient`, equal to the gradient wherever `f` is differentiable
and `0` elsewhere; by Rademacher's theorem the exceptional set is null).

The proof is the one of the paper. Writing `v = y + tθ` with `t > 0` and `|θ| = 1`,
`(v - y) |v - y|^{-d} dv = θ dt dσ(θ)` (`integral_eq_integral_sphere_Ioi`, polar coordinates of
`BallLayer`). By Rademacher's theorem (`LipschitzWith.ae_differentiableAt`) and Fubini
(`ae_sphere_ae_Ioi_smul`), for almost every `θ` the Lipschitz function `t ↦ f(y + tθ)` has
derivative `∇f(y + tθ) · θ` for almost every `t > 0`; it vanishes for large `t` and is absolutely
continuous, so its derivative integrates over `(0, ∞)` to `-f(y)` (`integral_deriv_ray`, the
fundamental theorem of calculus for absolutely continuous functions). The unit sphere has area
`d ω_d`.

* `integrable_kernel`: the integrand is integrable, so the Bochner integral is the genuine integral
  and the identity does not rest on a junk value. The proof bounds it by `K |v - y|^{1-d}` on the
  compact support and shows that it vanishes off the support.
* `gradient_identity`: the identity, for every Lipschitz function of compact support, with no
  convexity, norm, `C^1` or differentiability premise.
* `normPotential_univ_of_lipschitz`: `U_{ℝ^d}(y) = -2dε f(y)` for the literal potential
  `CERW.normPotential` with the gradient of `f`.

Nothing here assumes the gradient identity or a property of `f` beyond the Lipschitz condition and
compact support.
-/

open MeasureTheory Filter Topology
open scoped NNReal
open CERW CERW.Support.Norm

namespace CERW.Support.Norm.GradientIdentity

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The gradient `v ↦ ∇f(v)` is measurable. -/
theorem measurable_gradient_fun (f : EuclideanSpace ℝ (Fin d) → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

/-- The gradient of a `K`-Lipschitz function has norm at most `K`. -/
theorem norm_gradient_le_of_lipschitz {K : ℝ≥0} (hf : LipschitzWith K f)
    (v : EuclideanSpace ℝ (Fin d)) : ‖gradient f v‖ ≤ K := by
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := v) hf
  have h' : ‖gradient f v‖ = ‖fderiv ℝ f v‖ := by
    unfold gradient
    exact LinearIsometryEquiv.norm_map _ _
  rwa [h']

/-- Off the topological support of `f`, `f` vanishes near the point, so its gradient is `0`. -/
theorem gradient_eq_zero_of_notMem_tsupport {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∉ tsupport f) : gradient f v = 0 := by
  have h : f =ᶠ[𝓝 v] (fun _ => (0 : ℝ)) := by
    simpa only [Pi.zero_def] using notMem_tsupport_iff_eventuallyEq.1 hv
  unfold gradient
  rw [h.fderiv_eq]
  simp

/-- For `t > 0`, the quotient `t / t ^ d` is the real power `t ^ (1 - d)`. -/
theorem div_pow_eq_rpow_one_sub {t : ℝ} (ht : 0 < t) (d : ℕ) :
    t / t ^ d = t ^ (1 - (d : ℝ)) := by
  have h₁ : t / t ^ d = t ^ (1 : ℝ) / t ^ (d : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_one]
  rw [h₁, ← Real.rpow_sub ht (1 : ℝ) (d : ℝ)]

/-- A point of the Euclidean unit sphere has norm one. -/
theorem norm_eq_one_of_mem_sphere (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
  rw [← dist_zero_right]
  exact Metric.mem_sphere.mp θ.2

/-- The sphere measure of the whole unit sphere is `d ω_d`. -/
theorem toSphere_real_univ :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).real Set.univ =
      d * CERW.unitBallVolume d := by
  rw [MeasureTheory.Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  rfl

/-- **The integrand of the gradient identity is integrable.** For a Lipschitz function `f` of
compact support and every `y`, `v ↦ ∇f(v) · (v - y) |v - y|^{-d}` is Lebesgue integrable on `ℝ^d`
(`d ≥ 1`): it is bounded by `K |v - y|^{1-d}`, which is integrable on the compact support of `f`,
and it vanishes outside the support. -/
theorem integrable_kernel (hd : 1 ≤ d) {K : ℝ≥0} (hf : LipschitzWith K f)
    (hs : HasCompactSupport f) (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun v => inner ℝ (gradient f v) (v - y) / ‖v - y‖ ^ d) := by
  have hSc : IsCompact (tsupport f) := hs
  have hSm : MeasurableSet (tsupport f) := hSc.isClosed.measurableSet
  obtain ⟨hint, -⟩ := CERW.Generic.Kernel.integrableOn_and_setIntegral_le hd hSm
    hSc.measure_lt_top.ne y
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (gradient f v) (v - y) / ‖v - y‖ ^ d) :=
    ((measurable_gradient_fun f).inner hsub).div (hsub.norm.pow_const d)
  have hFS : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (gradient f v) (v - y) / ‖v - y‖ ^ d) (tsupport f) := by
    refine (hint.const_mul (K : ℝ)).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with v
    rcases eq_or_ne v y with rfl | hne
    · simp only [sub_self, inner_zero_right, zero_div, norm_zero]
      exact mul_nonneg NNReal.zero_le_coe (Real.rpow_nonneg le_rfl _)
    · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
      have h1 : ‖inner ℝ (gradient f v) (v - y)‖ ≤ (K : ℝ) * ‖v - y‖ :=
        (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_gradient_le_of_lipschitz hf v) (norm_nonneg _))
      rw [norm_div, norm_pow, norm_norm, div_le_iff₀ hden, ← div_pow_eq_rpow_one_sub hw d,
        mul_assoc, div_mul_cancel₀ _ hden.ne']
      exact h1
  have hind : (tsupport f).indicator (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (gradient f v) (v - y) / ‖v - y‖ ^ d) = fun v =>
        inner ℝ (gradient f v) (v - y) / ‖v - y‖ ^ d := by
    funext v
    by_cases hv : v ∈ tsupport f
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, gradient_eq_zero_of_notMem_tsupport hv]
      simp
  rw [← hind]
  exact (integrable_indicator_iff hSm).2 hFS

/-- Where `f` is differentiable at `y + tθ`, the function `s ↦ f(y + sθ)` has derivative
`∇f(y + tθ) · θ` at `t`. -/
theorem hasDerivAt_ray (y θ : EuclideanSpace ℝ (Fin d)) {t : ℝ}
    (h : DifferentiableAt ℝ f (y + t • θ)) :
    HasDerivAt (fun s : ℝ => f (y + s • θ)) (inner ℝ (gradient f (y + t • θ)) θ) t := by
  have hpath : HasDerivAt (fun s : ℝ => y + s • θ) θ t := by
    simpa using ((hasDerivAt_id' t).smul_const θ).const_add y
  exact HasFDerivAt.comp_hasDerivAt_of_eq t h.hasGradientAt.hasFDerivAt hpath rfl

/-- For `t > 0` and a unit vector `θ`, the integrand of the gradient identity at `y + tθ`, times
the polar weight `t^{d-1}`, is the directional derivative `∇f(y + tθ) · θ`. -/
theorem radial_weight (hd : 1 ≤ d) (y : EuclideanSpace ℝ (Fin d))
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) {t : ℝ} (ht : 0 < t) :
    t ^ (d - 1) * (inner ℝ (gradient f (y + t • θ)) (y + t • θ - y) / ‖y + t • θ - y‖ ^ d) =
      inner ℝ (gradient f (y + t • θ)) θ := by
  have hn : ‖t • θ‖ = t := by
    rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos ht]
  rw [add_sub_cancel_left, hn, real_inner_smul_right]
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- **The integral of the derivative along a ray.** For a Lipschitz function `f` of compact support
and a unit vector `θ`, the Lipschitz function `t ↦ f(y + tθ)` vanishes for large `t` and is
absolutely continuous, so its derivative integrates over `(0, ∞)` to `-f(y)`. -/
theorem integral_deriv_ray {K : ℝ≥0} (hf : LipschitzWith K f) (hs : HasCompactSupport f)
    (y : EuclideanSpace ℝ (Fin d)) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    ∫ t in Set.Ioi (0 : ℝ), deriv (fun s : ℝ => f (y + s • θ)) t = -f y := by
  set φ : ℝ → ℝ := fun s => f (y + s • θ) with hφdef
  have hφ : LipschitzWith K φ := by
    refine LipschitzWith.of_dist_le_mul fun s u => ?_
    have h := hf.dist_le_mul (y + s • θ) (y + u • θ)
    have hn : dist (y + s • θ) (y + u • θ) = dist s u := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hθ, mul_one,
        Real.norm_eq_abs, Real.dist_eq]
    rwa [hn] at h
  obtain ⟨R₀, hR₀⟩ := hs.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  set R : ℝ := ‖y‖ + max R₀ 0 + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hout : ∀ s : ℝ, R ≤ s → y + s • θ ∉ tsupport f := by
    intro s hsR hmem
    have h1 := hR₀ hmem
    rw [mem_closedBall_zero_iff] at h1
    have h2 : ‖s • θ‖ ≤ ‖y + s • θ‖ + ‖y‖ := by
      calc ‖s • θ‖ = ‖(y + s • θ) - y‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖y + s • θ‖ + ‖y‖ := norm_sub_le _ _
    rw [norm_smul, hθ, mul_one, Real.norm_eq_abs] at h2
    have h3 := le_max_left R₀ 0
    have h4 : s ≤ |s| := le_abs_self s
    linarith
  have hzero : ∀ s : ℝ, R < s → deriv φ s = 0 := by
    intro s hsR
    have h : φ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hsR] with u hu
      exact image_eq_zero_of_notMem_tsupport (f := f) (hout u (le_of_lt hu))
    rw [h.deriv_eq]
    simp
  have hcut : ∫ t in Set.Ioi (0 : ℝ), deriv φ t = ∫ t in Set.Ioc (0 : ℝ) R, deriv φ t := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self fun t ht => ?_
    refine hzero t ?_
    by_contra hle
    exact ht.2 ⟨ht.1, not_lt.1 hle⟩
  have hFTC := hφ.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    (a := 0) (b := R)
  rw [intervalIntegral.integral_of_le hR0] at hFTC
  have hφR : φ R = 0 := image_eq_zero_of_notMem_tsupport (f := f) (hout R le_rfl)
  have hφ0 : φ 0 = f y := by simp [hφdef]
  rw [hcut, hFTC, hφR, hφ0]
  ring

/-- **The gradient identity** (`eq:gradient-identity`). For every Lipschitz function `f` of compact
support on `ℝ^d`, `d ≥ 2`, and every `y`, the integrand `∇f(v) · (v - y) |v - y|^{-d}` is
integrable and `∫ ∇f(v) · (v - y) |v - y|^{-d} dv = - d ω_d f(y)`, with `ω_d` the volume of the
unit ball. No premise on `f` beyond the Lipschitz condition and compact support. -/
theorem gradient_identity (hd : 2 ≤ d) {K : ℝ≥0} (hf : LipschitzWith K f)
    (hs : HasCompactSupport f) (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun v => inner ℝ (gradient f v) (v - y) / ‖v - y‖ ^ d) ∧
      ∫ v, inner ℝ (gradient f v) (v - y) / ‖v - y‖ ^ d = -(d * CERW.unitBallVolume d * f y) := by
  have hd1 : 1 ≤ d := by omega
  have hint := integrable_kernel hd1 hf hs y
  refine ⟨hint, ?_⟩
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun v => inner ℝ (gradient f v) (v - y) / ‖v - y‖ ^ d
    with hF
  set f₀ : EuclideanSpace ℝ (Fin d) → ℝ := fun w => F (y + w) with hf₀
  have hf0 : Integrable f₀ := hint.comp_add_left y
  have h1 : ∫ v, F v = ∫ w, f₀ w :=
    (integral_add_left_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) F y).symm
  rw [h1, integral_eq_integral_sphere_Ioi hd1 hf0]
  have hdiff : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DifferentiableAt ℝ f (y + w) :=
    (quasiMeasurePreserving_add_left volume y).ae hf.ae_differentiableAt
  have hray : ∀ᵐ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere,
      ∫ t in Set.Ioi (0 : ℝ), t ^ (d - 1) * f₀ (t • (θ : EuclideanSpace ℝ (Fin d))) = -f y := by
    filter_upwards [ae_sphere_ae_Ioi_smul hd1 hdiff] with θ hθ
    have hθn := norm_eq_one_of_mem_sphere θ
    calc ∫ t in Set.Ioi (0 : ℝ), t ^ (d - 1) * f₀ (t • (θ : EuclideanSpace ℝ (Fin d)))
        = ∫ t in Set.Ioi (0 : ℝ), inner ℝ (gradient f (y + t • (θ : EuclideanSpace ℝ (Fin d))))
            (θ : EuclideanSpace ℝ (Fin d)) :=
          setIntegral_congr_fun measurableSet_Ioi fun t ht =>
            radial_weight hd1 y hθn (Set.mem_Ioi.1 ht)
      _ = ∫ t in Set.Ioi (0 : ℝ),
            deriv (fun s : ℝ => f (y + s • (θ : EuclideanSpace ℝ (Fin d)))) t := by
          refine setIntegral_congr_ae measurableSet_Ioi ?_
          filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hθ] with t ht htS
          exact (hasDerivAt_ray y θ (ht htS)).deriv.symm
      _ = -f y := integral_deriv_ray hf hs y hθn
  rw [integral_congr_ae hray, integral_const, toSphere_real_univ, smul_eq_mul]
  ring

/-- **The potential of `ℝ^d` generated by a Lipschitz function of compact support.** For the literal
potential `U_D(y) = (2ε/ω_d) ∫_D ∇f(v) · (v - y) |v - y|^{-d} dv` with the gradient of `f`, taking
`D = ℝ^d`, `U_{ℝ^d}(y) = - 2 d ε f(y)`. -/
theorem normPotential_univ_of_lipschitz (hd : 2 ≤ d) {K : ℝ≥0} (hf : LipschitzWith K f)
    (hs : HasCompactSupport f) (ε : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε f Set.univ y = -(2 * d * ε * f y) := by
  have hω := CERW.unitBallVolume_pos d
  unfold CERW.normPotential
  rw [Measure.restrict_univ, (gradient_identity hd hf hs y).2]
  field_simp

end CERW.Support.Norm.GradientIdentity
