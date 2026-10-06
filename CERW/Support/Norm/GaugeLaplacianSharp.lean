import CERW.Support.Norm.GaugeCellGradient
import CERW.Support.Norm.GaugePointwise
import CERW.Support.Norm.GaugePotential

/-!
# The exact growth of the distributional Laplacian of the gauge

For a compact convex set `K ⊆ ℝ^d` with the origin in its interior, the Minkowski functional
`ψ = gauge K` is `Λ_ψ`-Lipschitz, where `Λ_ψ = max_{|u| = 1} ψ(u)`, and its distributional
Laplacian `μ` (the locally finite measure with `∫ φ dμ = ∫ ψ Δφ` for every smooth compactly
supported `φ`) satisfies, for every centre `y ∈ ℝ^d` and every radius `R > 0`,

`μ(B(y, R)) ≤ 2^(d+1) ω_d Λ_ψ R^(d-1)`,

where `ω_d` is the volume of the Euclidean unit ball. This is the displayed growth estimate of
the source, with its exact coefficient. The proof follows the source:

* a smooth cutoff `φ`, equal to `1` on `B(y, R)` and supported in the closed ball `closedBall y (2R)`, with
  `|∇φ| ≤ 2/R`, is built as the convolution of a radial piecewise linear plateau with a normalized
  smooth bump;
* the Lipschitz function `ψ` is integrated by parts against `φ` (the integration by parts formula
  for line derivatives of Lipschitz functions), which gives `∫ ψ Δφ = -∫ ∇ψ · ∇φ`, where `∇ψ`
  exists almost everywhere by Rademacher's theorem;
* `|∇ψ| ≤ Λ_ψ`, so `μ(B(y, R)) ≤ ∫ φ dμ ≤ Λ_ψ ∫ |∇φ| ≤ Λ_ψ (2/R) |B(y, 2R)|`.

The bound is proved for every locally finite measure with the full distributional
characterization; the packaged statement applies the existence theorem of `GaugeLaplacian` and the
uniqueness theorem of `GaugePointwise`, so it is a statement about the one measure determined by
the body. No evenness and no `IsNorm` hypothesis occurs. The earlier growth bound of
`GaugeLaplacian`, with a dimension-dependent constant, is left unchanged. The statements are
consumed at the non-even planar body `cutDisc` and at the triangle with corners `cornerTriangle`.
-/

open Set Metric Topology MeasureTheory Filter
open scoped ContDiff Convolution NNReal

namespace CERW.Support.Norm.GaugeLaplacianSharp

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel

variable {d : ℕ}

/-! ### Derivatives of test functions -/

/-- The second directional derivative `D²φ(v)(e, e)`. -/
private noncomputable def hess (φ : EuclideanSpace ℝ (Fin d) → ℝ) (v e : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  fderiv ℝ (fderiv ℝ φ) v e e

/-- `w ↦ D²φ(w)(e, e)` is continuous for smooth `φ`. -/
private lemma continuous_hess {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : EuclideanSpace ℝ (Fin d)) : Continuous (fun w => hess φ w e) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ φ)) := h1.continuous_fderiv one_ne_zero
  exact (h2.clm_apply continuous_const).clm_apply continuous_const

/-- `w ↦ D²φ(w)(e, e)` has compact support for `φ` of compact support. -/
private lemma hasCompactSupport_hess {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : HasCompactSupport φ) (e : EuclideanSpace ℝ (Fin d)) :
    HasCompactSupport (fun w => hess φ w e) := by
  have h1 := (hc.fderiv (𝕜 := ℝ)).fderiv_apply (𝕜 := ℝ) e
  exact h1.comp_left (g := fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L e) (by simp)

/-- The Laplacian is the sum of the second derivatives along the standard basis. -/
private lemma laplacian_eq_sum_hess {φ : EuclideanSpace ℝ (Fin d) → ℝ} :
    Laplacian.laplacian φ =
      fun v => ∑ i : Fin d, hess φ v (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  have := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin d) ℝ)
  convert this using 2 with v
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [hess]

/-- The derivative of the first derivative `x ↦ Dφ(x) e` in the direction `e` is `D²φ(x)(e, e)`. -/
private lemma hasFDerivAt_fderiv_apply {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun x => fderiv ℝ φ x e)
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ φ) x)) x := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero) x
  exact (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp x hdd.hasFDerivAt

/-- The line derivative of `x ↦ Dφ(x) e` in the direction `-e` is `-D²φ(x)(e, e)`. -/
private lemma lineDeriv_fderiv_apply_neg {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (e x : EuclideanSpace ℝ (Fin d)) :
    lineDeriv ℝ (fun x => fderiv ℝ φ x e) x (-e) = -hess φ x e := by
  have h := ((hasFDerivAt_fderiv_apply hφ e x).hasLineDerivAt (-e)).lineDeriv
  rw [h]
  simp [hess]

/-- `x ↦ Dφ(x) e` is Lipschitz for `φ` smooth with compact support. -/
private lemma lipschitzWith_fderiv_apply {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : EuclideanSpace ℝ (Fin d)) :
    ∃ D : ℝ≥0, LipschitzWith D (fun x => fderiv ℝ φ x e) := by
  have h1 : ContDiff ℝ 1 (fun x => fderiv ℝ φ x e) :=
    (hφ.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const
  exact h1.lipschitzWith_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) e) one_ne_zero

/-! ### Integration by parts for a Lipschitz function -/

/-- **Integration by parts against the Laplacian.** For a Lipschitz function `ψ` and a smooth
compactly supported `φ`, `∫ ψ Δφ = -Σ_i ∫ ∂_i ψ ∂_i φ`, where `∂_i ψ` is the line derivative of `ψ`
along the `i`-th basis vector. -/
private lemma integral_mul_laplacian_eq {ψ φ : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hψ : LipschitzWith C ψ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ v, ψ v * Laplacian.laplacian φ v =
      -∑ i : Fin d, ∫ v, lineDeriv ℝ ψ v (EuclideanSpace.basisFun (Fin d) ℝ i) *
        fderiv ℝ φ v (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [laplacian_eq_sum_hess]
  simp_rw [Finset.mul_sum]
  have hint : ∀ i : Fin d, Integrable (fun v => ψ v *
      hess φ v (EuclideanSpace.basisFun (Fin d) ℝ i)) volume := fun i =>
    (hψ.continuous.mul (continuous_hess hφ _)).integrable_of_hasCompactSupport
      (hasCompactSupport_hess hc _).mul_left
  rw [integral_finsetSum _ fun i _ => hint i, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨D, hD⟩ := lipschitzWith_fderiv_apply hφ hc (EuclideanSpace.basisFun (Fin d) ℝ i)
  have h := hψ.integral_lineDeriv_mul_eq (μ := volume) hD (hc.fderiv_apply (𝕜 := ℝ) _)
    (EuclideanSpace.basisFun (Fin d) ℝ i)
  simp_rw [lineDeriv_fderiv_apply_neg hφ] at h
  rw [h, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [neg_mul]
  ring

/-- The sum over the standard basis of the products of the line derivative of `ψ` and the
derivative of `φ` is the inner product of the gradients, at every point where `ψ` is
differentiable. -/
private lemma sum_lineDeriv_mul_fderiv_eq_inner {ψ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : DifferentiableAt ℝ ψ v) :
    ∑ i : Fin d, lineDeriv ℝ ψ v (EuclideanSpace.basisFun (Fin d) ℝ i) *
        fderiv ℝ φ v (EuclideanSpace.basisFun (Fin d) ℝ i) =
      inner ℝ (gradient ψ v) (gradient φ v) := by
  rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner (gradient ψ v) (gradient φ v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv.lineDeriv_eq_fderiv, real_inner_comm (gradient φ v)]
  congr 1
  · exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
  · exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm

/-- **The integration by parts estimate.** If `ψ` is Lipschitz and its gradient has norm at most
`Λ` everywhere, then `|∫ ψ Δφ| ≤ Λ ∫ |Dφ|` for every smooth compactly supported `φ`. -/
private lemma abs_integral_mul_laplacian_le {ψ φ : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hψ : LipschitzWith C ψ) {Λ : ℝ} (hΛ : ∀ v, ‖gradient ψ v‖ ≤ Λ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    |∫ v, ψ v * Laplacian.laplacian φ v| ≤ Λ * ∫ v, ‖fderiv ℝ φ v‖ := by
  rw [integral_mul_laplacian_eq hψ hφ hc]
  have hint : ∀ i : Fin d, Integrable (fun v => lineDeriv ℝ ψ v
      (EuclideanSpace.basisFun (Fin d) ℝ i) *
        fderiv ℝ φ v (EuclideanSpace.basisFun (Fin d) ℝ i)) volume := by
    intro i
    have hcont : Continuous fun v => fderiv ℝ φ v (EuclideanSpace.basisFun (Fin d) ℝ i) :=
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    have := (hψ.locallyIntegrable_lineDeriv (μ := volume)
      (EuclideanSpace.basisFun (Fin d) ℝ i)).integrable_smul_left_of_hasCompactSupport hcont
      (hc.fderiv_apply (𝕜 := ℝ) _)
    simpa [mul_comm] using this
  rw [← integral_finsetSum _ fun i _ => hint i, abs_neg]
  have hae : (fun v => ∑ i : Fin d, lineDeriv ℝ ψ v (EuclideanSpace.basisFun (Fin d) ℝ i) *
      fderiv ℝ φ v (EuclideanSpace.basisFun (Fin d) ℝ i)) =ᵐ[volume]
        fun v => inner ℝ (gradient ψ v) (gradient φ v) := by
    filter_upwards [hψ.ae_differentiableAt] with v hv
    exact sum_lineDeriv_mul_fderiv_eq_inner hv
  rw [integral_congr_ae hae]
  have hdφ : Continuous fun v => ‖fderiv ℝ φ v‖ := (hφ.continuous_fderiv (by simp)).norm
  have hcφ : HasCompactSupport fun v => ‖fderiv ℝ φ v‖ := (hc.fderiv (𝕜 := ℝ)).norm
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hdφ.integrable_of_hasCompactSupport hcφ).const_mul Λ)
    (Eventually.of_forall fun v => ?_)
  calc ‖inner ℝ (gradient ψ v) (gradient φ v)‖
      ≤ ‖gradient ψ v‖ * ‖gradient φ v‖ := norm_inner_le_norm _ _
    _ ≤ Λ * ‖fderiv ℝ φ v‖ := by
        refine mul_le_mul (hΛ v) (le_of_eq ?_) (norm_nonneg _) ((norm_nonneg _).trans (hΛ v))
        exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _

/-! ### A smooth cutoff with a gradient bound -/

section Cutoff

variable (y : EuclideanSpace ℝ (Fin d)) {R : ℝ}

/-- The radial plateau: `1` on the closed ball of radius `5R/4` about `y`, `0` outside the open
ball of radius `7R/4`, and linear in the distance to `y` in between. -/
private noncomputable def plateau (y : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun t => max (min ((7 * R / 4 - ‖t - y‖) * (2 / R)) 1) 0

private lemma plateau_eq_one (hR : 0 < R) {t : EuclideanSpace ℝ (Fin d)}
    (ht : ‖t - y‖ ≤ 5 * R / 4) : plateau y R t = 1 := by
  have h1 : 1 ≤ (7 * R / 4 - ‖t - y‖) * (2 / R) := by
    have h2 : R / 2 ≤ 7 * R / 4 - ‖t - y‖ := by linarith
    calc (1 : ℝ) = R / 2 * (2 / R) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)
  simp [plateau, min_eq_right h1]

private lemma plateau_eq_zero (hR : 0 < R) {t : EuclideanSpace ℝ (Fin d)}
    (ht : 7 * R / 4 ≤ ‖t - y‖) : plateau y R t = 0 := by
  have h1 : (7 * R / 4 - ‖t - y‖) * (2 / R) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h2 : min ((7 * R / 4 - ‖t - y‖) * (2 / R)) 1 ≤ 0 := (min_le_left _ _).trans h1
  simp [plateau, max_eq_right h2]

private lemma plateau_nonneg (t : EuclideanSpace ℝ (Fin d)) : 0 ≤ plateau y R t :=
  le_max_right _ _

private lemma plateau_le_one (t : EuclideanSpace ℝ (Fin d)) : plateau y R t ≤ 1 :=
  max_le (min_le_right _ _) zero_le_one

/-- The plateau is Lipschitz with the constant `2/R`. -/
private lemma lipschitzWith_plateau (hR : 0 < R) :
    LipschitzWith (Real.toNNReal (2 / R)) (plateau y R) := by
  have hs : LipschitzWith (Real.toNNReal (2 / R))
      (fun t : EuclideanSpace ℝ (Fin d) => (7 * R / 4 - ‖t - y‖) * (2 / R)) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have h : (7 * R / 4 - ‖a - y‖) * (2 / R) - (7 * R / 4 - ‖b - y‖) * (2 / R) =
        (‖b - y‖ - ‖a - y‖) * (2 / R) := by ring
    rw [h, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / R), mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |‖b - y‖ - ‖a - y‖| ≤ ‖(b - y) - (a - y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖a - b‖ := by rw [← norm_neg]; congr 1; abel
  exact (hs.min_const 1).max_const 0

/-- The normalized bump of outer radius `R/4`. -/
private noncomputable def kernel (d : ℕ) {R : ℝ} (hR : 0 < R) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨R / 8, R / 4, by positivity, by linarith⟩

/-- The smooth cutoff: the convolution of the normalized bump with the plateau. -/
private noncomputable def cutoff (y : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => ((kernel d hR).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] plateau y R) x

private lemma cutoff_eq_integral (hR : 0 < R) (x : EuclideanSpace ℝ (Fin d)) :
    cutoff y hR x = ∫ t, (kernel d hR).normed volume t * plateau y R (x - t) := by
  simp [cutoff, convolution_def]

private lemma contDiff_cutoff (hR : 0 < R) : ContDiff ℝ ∞ (cutoff y hR) := by
  have hpl : Continuous (plateau y R) := (lipschitzWith_plateau y hR).continuous
  exact (kernel d hR).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (kernel d hR).contDiff_normed hpl.locallyIntegrable

private lemma cutoff_nonneg (hR : 0 < R) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ cutoff y hR x := by
  rw [cutoff_eq_integral]
  exact integral_nonneg fun t => mul_nonneg ((kernel d hR).nonneg_normed t) (plateau_nonneg y _)

private lemma cutoff_eq_plateau (hR : 0 < R) {x : EuclideanSpace ℝ (Fin d)}
    (h : ∀ z ∈ ball x ((kernel d hR).rOut), plateau y R z = plateau y R x) :
    cutoff y hR x = plateau y R x :=
  (kernel d hR).normed_convolution_eq_right h

private lemma cutoff_eq_one (hR : 0 < R) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball y R) :
    cutoff y hR x = 1 := by
  have hx' : ‖x - y‖ < R := by simpa [dist_eq_norm] using hx
  have h1 : plateau y R x = 1 := plateau_eq_one y hR (by linarith)
  have hcon : ∀ z ∈ ball x ((kernel d hR).rOut), plateau y R z = plateau y R x := by
    intro z hz
    have hz' : dist z x < R / 4 := hz
    rw [dist_eq_norm] at hz'
    rw [h1]
    refine plateau_eq_one y hR ?_
    calc ‖z - y‖ = ‖(z - x) + (x - y)‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖x - y‖ := norm_add_le _ _
      _ ≤ 5 * R / 4 := by linarith
  rw [cutoff_eq_plateau y hR hcon, h1]

private lemma cutoff_eq_zero (hR : 0 < R) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ closedBall y (2 * R)) : cutoff y hR x = 0 := by
  have hx' : 2 * R < ‖x - y‖ := by simpa [dist_eq_norm] using hx
  have h1 : plateau y R x = 0 := plateau_eq_zero y hR (by linarith)
  have hcon : ∀ z ∈ ball x ((kernel d hR).rOut), plateau y R z = plateau y R x := by
    intro z hz
    have hz' : dist z x < R / 4 := hz
    rw [dist_eq_norm] at hz'
    rw [h1]
    refine plateau_eq_zero y hR ?_
    have h2 : ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ := by
      calc ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr 1; abel
        _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
    rw [norm_sub_rev x z] at h2
    linarith
  rw [cutoff_eq_plateau y hR hcon, h1]

/-- The cutoff is Lipschitz with the constant `2/R`. -/
private lemma abs_cutoff_sub_le (hR : 0 < R) (a b : EuclideanSpace ℝ (Fin d)) :
    |cutoff y hR a - cutoff y hR b| ≤ 2 / R * ‖a - b‖ := by
  have hρ := (kernel d hR).integrable_normed (μ := volume)
  have hpl := (lipschitzWith_plateau y hR)
  have hint : ∀ x : EuclideanSpace ℝ (Fin d),
      Integrable (fun t => (kernel d hR).normed volume t * plateau y R (x - t)) volume := by
    intro x
    refine hρ.mono' ((kernel d hR).continuous_normed.mul
      (hpl.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((kernel d hR).nonneg_normed t),
      abs_of_nonneg (plateau_nonneg y _)]
    exact mul_le_of_le_one_right ((kernel d hR).nonneg_normed t) (plateau_le_one y _)
  rw [cutoff_eq_integral, cutoff_eq_integral, ← integral_sub (hint a) (hint b), ← Real.norm_eq_abs]
  have hb : ∀ t, ‖(kernel d hR).normed volume t * plateau y R (a - t) -
      (kernel d hR).normed volume t * plateau y R (b - t)‖ ≤
        (kernel d hR).normed volume t * (2 / R * ‖a - b‖) := by
    intro t
    rw [← mul_sub, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg ((kernel d hR).nonneg_normed t)]
    refine mul_le_mul_of_nonneg_left ?_ ((kernel d hR).nonneg_normed t)
    have h := hpl.dist_le_mul (a - t) (b - t)
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)] at h
    rw [Real.norm_eq_abs]
    calc |plateau y R (a - t) - plateau y R (b - t)| ≤ 2 / R * ‖(a - t) - (b - t)‖ := h
      _ = 2 / R * ‖a - b‖ := by congr 2; abel
  refine (norm_integral_le_of_norm_le (hρ.mul_const _) (Eventually.of_forall hb)).trans ?_
  rw [integral_mul_const, (kernel d hR).integral_normed, one_mul]

/-- **A smooth cutoff of the ball.** For `R > 0` there is a smooth function `φ` on `ℝ^d`, `φ ≥ 0`,
with `φ = 1` on `B(y, R)`, `φ = 0` outside the closed ball of radius `2R`, and
`|Dφ| ≤ 2/R` everywhere. -/
private lemma exists_cutoff (hR : 0 < R) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x, 0 ≤ φ x) ∧ (∀ x ∈ ball y R, φ x = 1) ∧ (∀ x, ‖fderiv ℝ φ x‖ ≤ 2 / R) ∧
      (∀ x ∉ closedBall y (2 * R), fderiv ℝ φ x = 0) := by
  have hzero : ∀ x ∉ closedBall y (2 * R), cutoff y hR x = 0 := fun x hx => cutoff_eq_zero y hR hx
  have hcs : HasCompactSupport (cutoff y hR) :=
    HasCompactSupport.intro (isCompact_closedBall y (2 * R)) hzero
  have hlip : LipschitzWith (Real.toNNReal (2 / R)) (cutoff y hR) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact abs_cutoff_sub_le y hR a b
  refine ⟨cutoff y hR, contDiff_cutoff y hR, hcs, cutoff_nonneg y hR,
    fun x hx => cutoff_eq_one y hR hx, fun x => ?_, fun x hx => ?_⟩
  · have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hlip
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  · have hsub : tsupport (cutoff y hR) ⊆ closedBall y (2 * R) :=
      closure_minimal (Function.support_subset_iff'.mpr hzero) isClosed_closedBall
    exact fderiv_of_notMem_tsupport ℝ fun h => hx (hsub h)

end Cutoff

/-! ### The exact growth -/

section Gauge

variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- The arithmetic of the coefficient: `Λ (2/R) ((2R)^d w) = 2^(d+1) w Λ R^(d-1)` for `d ≥ 1`. -/
private lemma coefficient_eq {R w Λ : ℝ} (hR : 0 < R) (hd : 1 ≤ d) :
    Λ * (2 / R * ((2 * R) ^ d * w)) = 2 ^ (d + 1) * w * Λ * R ^ (d - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

/-- The integral of the norm of the derivative of a function whose derivative is bounded by `c`
and vanishes outside the closed ball of radius `ρ` is at most `c |B(y, ρ)|`. -/
private lemma integral_norm_fderiv_le {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) {c ρ : ℝ} (y : EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ x, ‖fderiv ℝ φ x‖ ≤ c) (hzero : ∀ x ∉ closedBall y ρ, fderiv ℝ φ x = 0)
    (hρ : 0 ≤ ρ) :
    ∫ v, ‖fderiv ℝ φ v‖ ≤ c * (ρ ^ d * unitBallVolume d) := by
  have hdφ : Continuous fun v => ‖fderiv ℝ φ v‖ := (hφ.continuous_fderiv (by simp)).norm
  have hcφ : HasCompactSupport fun v => ‖fderiv ℝ φ v‖ := (hc.fderiv (𝕜 := ℝ)).norm
  calc ∫ v, ‖fderiv ℝ φ v‖ ≤ ∫ v, (closedBall y ρ).indicator (fun _ => c) v := by
        refine integral_mono (hdφ.integrable_of_hasCompactSupport hcφ) ?_ fun v => ?_
        · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
            measurableSet_closedBall
        · by_cases hv : v ∈ closedBall y ρ
          · simp [hv, hgrad v]
          · simp [hv, hzero v hv]
    _ = c * (ρ ^ d * unitBallVolume d) := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, measureReal_def,
          Measure.addHaar_closedBall volume y hρ, finrank_euclideanSpace_fin,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hρ _)]
        simp only [unitBallVolume]
        ring

/-- **Exact radial growth of the distributional Laplacian of the gauge** (`eq:hessian-growth`).
Let `K` be a compact convex set with the origin in its interior, `d ≥ 1`, and `m` a locally finite
measure with `∫ φ dm = ∫ ψ_K Δφ` for every smooth compactly supported `φ`. Then for every centre
`y` and every radius `R > 0`,
`m(B(y, R)) ≤ 2^(d+1) ω_d Λ_ψ R^(d-1)`, where `ω_d` is the volume of the Euclidean unit ball and
`Λ_ψ = max_{|u| = 1} ψ_K(u)`. -/
theorem measure_ball_le_gauge_sharp (hd : 1 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {m : Measure (EuclideanSpace ℝ (Fin d))} (hm : IsLocallyFiniteMeasure m)
    (hlap : CERW.IsDistribLaplacian (gauge K) m) (y : EuclideanSpace ℝ (Fin d)) {R : ℝ}
    (hR : 0 < R) :
    m (ball y R) ≤
      ENNReal.ofReal (2 ^ (d + 1) * unitBallVolume d * normMax (gauge K) * R ^ (d - 1)) := by
  haveI := hm
  obtain ⟨φ, hφ, hcs, hnn, h1, hgrad, hzero⟩ := exists_cutoff y hR
  have hint : Integrable φ m := hφ.continuous.integrable_of_hasCompactSupport hcs
  have hle : m.real (ball y R) ≤ ∫ v, φ v ∂m := by
    calc m.real (ball y R)
        = ∫ v, (ball y R).indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ) v ∂m :=
          (integral_indicator_one measurableSet_ball).symm
      _ ≤ ∫ v, φ v ∂m := by
          refine integral_mono ?_ hint fun v => ?_
          · exact (integrableOn_const measure_ball_lt_top.ne).integrable_indicator
              measurableSet_ball
          · by_cases hv : v ∈ ball y R
            · simp [hv, h1 v hv]
            · simp [hv, hnn v]
  have hbound := abs_integral_mul_laplacian_le (lipschitzWith_gauge hK hc h0)
    (norm_gradient_gauge_le hK hc h0) hφ hcs
  have hvol := integral_norm_fderiv_le hφ hcs y hgrad hzero (by positivity : (0 : ℝ) ≤ 2 * R)
  have hb : m.real (ball y R) ≤
      2 ^ (d + 1) * unitBallVolume d * normMax (gauge K) * R ^ (d - 1) :=
    calc m.real (ball y R) ≤ ∫ v, φ v ∂m := hle
      _ = ∫ v, gauge K v * Laplacian.laplacian φ v := hlap φ hφ hcs
      _ ≤ |∫ v, gauge K v * Laplacian.laplacian φ v| := le_abs_self _
      _ ≤ normMax (gauge K) * ∫ v, ‖fderiv ℝ φ v‖ := hbound
      _ ≤ normMax (gauge K) * (2 / R * ((2 * R) ^ d * unitBallVolume d)) :=
          mul_le_mul_of_nonneg_left hvol (normMax_gauge_nonneg K)
      _ = 2 ^ (d + 1) * unitBallVolume d * normMax (gauge K) * R ^ (d - 1) :=
          coefficient_eq hR hd
  calc m (ball y R) = ENNReal.ofReal (m.real (ball y R)) :=
        (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb

/-- **The distributional Laplacian of the gauge, with its exact growth.** For a compact convex `K`
with the origin in its interior and `d ≥ 1`, there is exactly one locally finite measure `m` with
`∫ φ dm = ∫ ψ_K Δφ` for every smooth compactly supported `φ`. It charges every ball about the
origin and satisfies `m(B(y, R)) ≤ 2^(d+1) ω_d Λ_ψ R^(d-1)` for every centre `y` and radius
`R > 0`. -/
theorem exists_unique_isDistribLaplacian_gauge_sharp (hd : 1 ≤ d) (hK : IsCompact K)
    (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)),
      (IsLocallyFiniteMeasure m ∧ CERW.IsDistribLaplacian (gauge K) m) ∧
      (∀ m' : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m' →
        CERW.IsDistribLaplacian (gauge K) m' → m' = m) ∧
      (∀ {ρ : ℝ}, 0 < ρ → 0 < m (ball 0 ρ)) ∧
      ∀ (y : EuclideanSpace ℝ (Fin d)) {R : ℝ}, 0 < R →
        m (ball y R) ≤
          ENNReal.ofReal (2 ^ (d + 1) * unitBallVolume d * normMax (gauge K) * R ^ (d - 1)) := by
  obtain ⟨m, ⟨hm, hlap⟩, huniq⟩ :=
    CERW.Support.Norm.GaugePointwise.gauge_laplacian_existsUnique hK hc h0
  refine ⟨m, ⟨hm, hlap⟩, fun m' hm' hl' => huniq m' ⟨hm', hl'⟩, fun {ρ} hρ => ?_,
    fun y _ hR => measure_ball_le_gauge_sharp hd hK hc h0 hm hlap y hR⟩
  have hlow := CERW.Support.Norm.GaugeCellGradient.measure_ball_ge_gauge hd hK hc h0 hm hlap hρ
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr ?_) hlow
  obtain ⟨hcpos, -⟩ := normMin_gauge_pos_mul_le hK h0 hd
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- **The exact growth at the lattice sites.** The hypothesis of the weighted summation of the cell
estimate holds with the exact constant `Kg = 2^(d+1) ω_d Λ_ψ`: there is a locally finite measure
`m` with distributional Laplacian `Δ ψ_K` and `m(B(y, R)) ≤ Kg R^(d-1)` for every site `y` of `ℤ^d`
and every `R > 0`. -/
theorem exists_isDistribLaplacian_gauge_growth_sharp (hd : 1 ≤ d) (hK : IsCompact K)
    (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian (gauge K) m ∧ ∀ (y : LatticeProb.Site d) {R : ℝ}, 0 < R →
        m (ball (toSpace y) R) ≤
          ENNReal.ofReal ((2 ^ (d + 1) * unitBallVolume d * normMax (gauge K)) * R ^ (d - 1)) := by
  obtain ⟨m, ⟨hm, hlap⟩, -, -, hgrowth⟩ := exists_unique_isDistribLaplacian_gauge_sharp hd hK hc h0
  exact ⟨m, hm, hlap, fun y _ hR => hgrowth (toSpace y) hR⟩

end Gauge

/-! ### Consumption at bodies that are not symmetric -/

/-- **Exact growth at the non-even planar body.** The gauge of `cutDisc` (the disc of radius `2`
cut by `y₀ ≥ -1`) is not a norm and not even; its distributional Laplacian is the unique locally
finite measure `m` with `∫ φ dm = ∫ ψ Δφ`, it charges every ball about the origin, and
`m(B(y, R)) ≤ 2^3 ω_2 Λ_ψ R` for every centre and radius. -/
theorem cutDisc_gaugeLaplacian_sharp :
    ¬ IsNorm (gauge cutDisc) ∧ gauge cutDisc (-coordVec 0) ≠ gauge cutDisc (coordVec 0) ∧
    ∃ m : Measure (EuclideanSpace ℝ (Fin 2)),
      (IsLocallyFiniteMeasure m ∧ CERW.IsDistribLaplacian (gauge cutDisc) m) ∧
      (∀ m' : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m' →
        CERW.IsDistribLaplacian (gauge cutDisc) m' → m' = m) ∧
      (∀ {ρ : ℝ}, 0 < ρ → 0 < m (ball 0 ρ)) ∧
      ∀ (y : EuclideanSpace ℝ (Fin 2)) {R : ℝ}, 0 < R →
        m (ball y R) ≤
          ENNReal.ofReal (2 ^ (2 + 1) * unitBallVolume 2 * normMax (gauge cutDisc) *
            R ^ (2 - 1)) :=
  ⟨not_isNorm_gauge_cutDisc, gauge_cutDisc_neg_ne,
    exists_unique_isDistribLaplacian_gauge_sharp (by norm_num) isCompact_cutDisc convex_cutDisc
      zero_mem_interior_cutDisc⟩

/-- **Exact growth at the triangle with corners.** The gauge of the triangle `cornerTriangle` with
vertices `(-1,-1)`, `(2,-1)`, `(-1,2)` is not even (its value at `a = (1/4)(e₀ + e₁)` is `1/2`, at
`-a` it is `1/4`) and is not differentiable at `(-1,-1)`; its distributional Laplacian is the
unique locally finite measure `m` with `∫ φ dm = ∫ ψ Δφ`, it charges every ball about the origin,
and `m(B(y, R)) ≤ 2^3 ω_2 Λ_ψ R` for every centre and radius. -/
theorem cornerTriangle_gaugeLaplacian_sharp :
    gauge Support.Norm.GaugePotential.cornerTriangle
        (-((1 / 4 : ℝ) • (coordVec 0 + coordVec 1))) ≠
      gauge Support.Norm.GaugePotential.cornerTriangle ((1 / 4 : ℝ) • (coordVec 0 + coordVec 1)) ∧
    ¬ DifferentiableAt ℝ (gauge Support.Norm.GaugePotential.cornerTriangle)
        (-coordVec 0 - coordVec 1) ∧
    ∃ m : Measure (EuclideanSpace ℝ (Fin 2)),
      (IsLocallyFiniteMeasure m ∧
        CERW.IsDistribLaplacian (gauge Support.Norm.GaugePotential.cornerTriangle) m) ∧
      (∀ m' : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m' →
        CERW.IsDistribLaplacian (gauge Support.Norm.GaugePotential.cornerTriangle) m' →
          m' = m) ∧
      (∀ {ρ : ℝ}, 0 < ρ → 0 < m (ball 0 ρ)) ∧
      ∀ (y : EuclideanSpace ℝ (Fin 2)) {R : ℝ}, 0 < R →
        m (ball y R) ≤
          ENNReal.ofReal (2 ^ (2 + 1) * unitBallVolume 2 *
            normMax (gauge Support.Norm.GaugePotential.cornerTriangle) * R ^ (2 - 1)) := by
  obtain ⟨h1, h2⟩ := Support.Norm.GaugePotential.gauge_cornerTriangle_not_even
  refine ⟨by rw [h1, h2]; norm_num,
    Support.Norm.GaugePotential.not_differentiableAt_gauge_cornerTriangle, ?_⟩
  exact exists_unique_isDistribLaplacian_gauge_sharp (by norm_num)
    Support.Norm.GaugePotential.isCompact_cornerTriangle
    Support.Norm.GaugePotential.convex_cornerTriangle
    Support.Norm.GaugePotential.zero_mem_interior_cornerTriangle

end CERW.Support.Norm.GaugeLaplacianSharp
