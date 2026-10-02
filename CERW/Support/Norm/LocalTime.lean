import CERW.Support.Statements
import CERW.Support.Drift
import CERW.Support.LocalTime
import CERW.Support.Geometry
import CERW.Support.Norm.Freedman
import CERW.Support.Norm.MoreauCap
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.Crossing
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.Radial
import CERW.Support.Norm.OuterCrossing
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.Coarse
import CERW.Generic.Lattice.Packing
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Convex.Cone.Extension
import CERW.Support.Norm.DriftSite

/-!
# The local times and the norm potential

`lem:local` of the paper (`CERW-Sep26.tex:384-400`) for the centrally excited random walk with
drift field `ξ`, a choice of subgradients of a norm `Ψ`, given the estimate of `lem:cell`
(`cell_gradient`). The proof is the one of the Euclidean case (`CERW.Support.LocalTime`):

* Dynkin's formula for the kernel `b(· - y)` and the walk with drift field (`driftDynkin`), and
  `eq:cellmodulus` for the norm potential, both from `CERW.Support.Norm.DriftSite`;
* the interval martingale bound from Freedman's inequality at dyadic brackets;
* the Young absorption for the interval maxima, and the approximation of the local times by
  the source sum.

The step specific to norms is the replacement of the lattice drift `ξ(x)` by the gradient `∇Ψ(v)`
on the cells (lines 479-483 of the paper). It uses `lem:cell` and the hessian growth
`μ(B(y, R)) ≤ C Λ_Ψ R^{d-1}` (`eq:hessian-growth`) of the distributional Laplacian `μ` of `Ψ`.
A locally finite measure `μ` with `IsDistribLaplacian Ψ μ` exists: the functional
`φ ↦ ∫ Ψ Δφ` is positive on the smooth compactly supported functions, because second difference
quotients of a convex function are nonnegative. It therefore extends to a positive functional on
all compactly supported continuous functions (M. Riesz), which is an integral against a Radon
measure (Riesz-Markov-Kakutani).
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

section NormFacts

open CERW CERW.Support.Occupation

variable {d : ℕ}

/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient_field (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- `Λ_Ψ ≥ 0`. -/
private lemma normMax_nonneg_of_isNorm {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) :
    0 ≤ normMax Ψ := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨u, -, rfl⟩
  exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 u

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere. -/
private lemma norm_gradient_le_normMax {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (v : EuclideanSpace ℝ (Fin d)) : ‖gradient Ψ v‖ ≤ normMax Ψ := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · exact norm_le_normMax_of_isSubgradient hΨ (CERW.Generic.Norm.gradient_isSubgradient hΨ hv)
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, norm_zero]
    exact normMax_nonneg_of_isNorm hΨ

/-- A drift field of subgradients of a norm has norm at most `Λ_Ψ`. -/
private lemma norm_drift_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    (x : Site d) : ‖ξ x‖ ≤ normMax Ψ := by
  by_cases hx : x = 0
  · subst hx
    rw [hξ0, norm_zero]
    exact normMax_nonneg_of_isNorm hΨ
  · exact norm_le_normMax_of_isSubgradient hΨ (hξ x hx)

/-- At every site there is a subgradient: `ξ x` for `x ≠ 0`, and `0` at the origin. -/
private lemma isSubgradient_drift {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    (x : Site d) : IsSubgradient Ψ (toSpace x) (ξ x) := by
  by_cases hx : x = 0
  · subst hx
    rw [hξ0, toSpace_zero]
    exact CERW.Generic.Norm.subgradient_zero hΨ
  · exact hξ x hx

end NormFacts

section Hessian

open scoped ContDiff

variable {d : ℕ}

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

/-- A finite sum of compactly supported functions has compact support. -/
private lemma hasCompactSupport_sum {ι : Type*} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin d) → ℝ} (h : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The Laplacian of a smooth compactly supported function is continuous. -/
private lemma continuous_laplacian {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (Laplacian.laplacian φ) := by
  rw [laplacian_eq_sum_hess]
  exact continuous_finsetSum _ fun i _ => continuous_hess hφ _

/-- The Laplacian of a compactly supported function has compact support. -/
private lemma hasCompactSupport_laplacian {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : HasCompactSupport φ) : HasCompactSupport (Laplacian.laplacian φ) := by
  rw [laplacian_eq_sum_hess]
  exact hasCompactSupport_sum _ fun i _ => hasCompactSupport_hess hc _

/-- The integral of a directional derivative of a `C¹` compactly supported function vanishes. -/
private lemma integral_fderiv_apply_eq_zero {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (e : EuclideanSpace ℝ (Fin d)) :
    ∫ x, fderiv ℝ ψ x e = 0 := by
  have hcont : Continuous fun x => fderiv ℝ ψ x e :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) (g := ψ) (v := e) (by simp)
    (by simpa using Continuous.integrable_of_hasCompactSupport hcont (hc.fderiv_apply (𝕜 := ℝ) e))
    (by simpa using Continuous.integrable_of_hasCompactSupport hψ.continuous hc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hψ.differentiable one_ne_zero) x)
  simpa using this

/-- The derivative of the first derivative `x ↦ Dφ(x) e` in the direction `e` is `D²φ(x)(e, e)`. -/
private lemma hasFDerivAt_fderiv_apply {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun x => fderiv ℝ φ x e)
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ φ) x)) x := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero) x
  exact (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp x hdd.hasFDerivAt

/-- An affine function integrates to zero against a second derivative of a compactly supported
function: `∫ (a + ⟨ξ, x⟩) D²φ(x)(e, e) dx = 0`. -/
private lemma integral_affine_mul_hess {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (a : ℝ) (ξ e : EuclideanSpace ℝ (Fin d)) :
    ∫ x, (a + inner ℝ ξ x) * hess φ x e = 0 := by
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => fderiv ℝ φ x e with hg
  have hgc : Continuous g :=
    ((hφ.fderiv_right (m := 1) (by norm_cast)).continuous).clm_apply continuous_const
  have hgs : HasCompactSupport g := hc.fderiv_apply (𝕜 := ℝ) e
  have hgd : ∀ x, HasFDerivAt g
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ φ) x)) x :=
    fun x => hasFDerivAt_fderiv_apply hφ e x
  have hf : ∀ x, HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ x)
      (innerSL ℝ ξ) x :=
    fun x => (innerSL ℝ ξ).hasFDerivAt.const_add a
  have hfc : Continuous fun x : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ x := by fun_prop
  have hgd' : ∀ x, fderiv ℝ g x e = hess φ x e := by
    intro x
    rw [(hgd x).fderiv]
    simp [hess]
  have hfd' : ∀ x, fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ x) x e =
      inner ℝ ξ e := by
    intro x
    rw [(hf x).fderiv]
    simp
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun x : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ x) (g := g) (v := e)
    (by
      simp_rw [hfd']
      exact (continuous_const.mul hgc).integrable_of_hasCompactSupport hgs.mul_left)
    (by
      simp_rw [hgd']
      exact (hfc.mul (continuous_hess hφ e)).integrable_of_hasCompactSupport
        (hasCompactSupport_hess hc e).mul_left)
    ((hfc.mul hgc).integrable_of_hasCompactSupport hgs.mul_left)
    (fun x _ => (hf x).differentiableAt) (fun x _ => (hgd x).differentiableAt)
  simp_rw [hgd', hfd'] at hibp
  rw [hibp, integral_const_mul]
  have h0 : ∫ x, g x = 0 := integral_fderiv_apply_eq_zero (hφ.of_le (by norm_cast)) hc e
  rw [h0]
  simp

/-- The derivative of a dilated and translated function. -/
private lemma hasFDerivAt_comp_smul_sub {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : Differentiable ℝ χ) (c : ℝ) (z v : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun v => χ (c • (v - z))) (c • fderiv ℝ χ (c • (v - z))) v := by
  have hA : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin d) => c • (v - z))
      (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) v :=
    ((hasFDerivAt_id v).sub_const z).const_smul c
  have h := (hχ (c • (v - z))).hasFDerivAt.comp v hA
  exact h.congr_fderiv (by ext w; simp)

/-- The second derivative of a dilated and translated function scales by `c²`. -/
private lemma hess_comp_smul_sub {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ContDiff ℝ 2 χ)
    (c : ℝ) (z v e : EuclideanSpace ℝ (Fin d)) :
    hess (fun v => χ (c • (v - z))) v e = c ^ 2 * hess χ (c • (v - z)) e := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ χ) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : fderiv ℝ (fun v => χ (c • (v - z))) =
      fun v => c • fderiv ℝ χ (c • (v - z)) :=
    funext fun v => (hasFDerivAt_comp_smul_sub hχd c z v).fderiv
  have hA : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin d) => c • (v - z))
      (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) v :=
    ((hasFDerivAt_id v).sub_const z).const_smul c
  have h2 := ((hdd (c • (v - z))).hasFDerivAt.comp v hA).const_smul c
  have h3 : HasFDerivAt (fun v => c • fderiv ℝ χ (c • (v - z)))
      (c • ((fderiv ℝ (fderiv ℝ χ) (c • (v - z))).comp
        (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))))) v := h2
  unfold hess
  rw [h1, h3.fderiv]
  simp [pow_two, mul_assoc]

/-- The second derivative vanishes where the function vanishes identically nearby. -/
private lemma hess_eq_zero_of_eventuallyEq {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {w : EuclideanSpace ℝ (Fin d)} (h : φ =ᶠ[𝓝 w] fun _ => 0) (e : EuclideanSpace ℝ (Fin d)) :
    hess φ w e = 0 := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 w] fun _ => (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq]
    simp
  have h2 := h1.fderiv_eq (𝕜 := ℝ)
  simp [hess, h2]

/-- The Laplacian of a dilated and translated function. -/
private lemma laplacian_comp_smul_sub {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ContDiff ℝ 2 χ)
    (c : ℝ) (z v : EuclideanSpace ℝ (Fin d)) :
    Laplacian.laplacian (fun v => χ (c • (v - z))) v =
      c ^ 2 * Laplacian.laplacian χ (c • (v - z)) := by
  rw [laplacian_eq_sum_hess, laplacian_eq_sum_hess, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hess_comp_smul_sub hχ c z v _

/-- The fixed smooth bump, equal to `1` on the unit ball and supported in the ball of radius `2`. -/
private noncomputable def bump (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨1, 2, one_pos, by norm_num⟩

/-- The Laplacian of the fixed bump is bounded. -/
private lemma exists_bound_laplacian_bump (d : ℕ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ w, |Laplacian.laplacian (⇑(bump d)) w| ≤ K₀ := by
  obtain ⟨K₀, hK₀⟩ := (continuous_laplacian (bump d).contDiff).bounded_above_of_compact_support
    (hasCompactSupport_laplacian (bump d).hasCompactSupport)
  refine ⟨K₀, (norm_nonneg _).trans (hK₀ 0), fun w => ?_⟩
  simpa [Real.norm_eq_abs] using hK₀ w

/-- `R ^ d * R * R⁻¹ ^ 2 = R ^ (d - 1)` for `d ≥ 1`. -/
private lemma pow_mul_mul_inv_sq {R : ℝ} (hR : 0 < R) {d : ℕ} (hd : 1 ≤ d) :
    R ^ d * R * R⁻¹ ^ 2 = R ^ (d - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

/-- The test function `φ(v) = χ((v - y)/R)`: smooth, compactly supported, nonnegative, equal to
`1` on `B(y, R)` and zero outside `B(y, 2R)`. -/
private lemma exists_testFunction (d : ℕ) {K₀ : ℝ}
    (hK₀ : ∀ w, |Laplacian.laplacian (⇑(bump d)) w| ≤ K₀) {R : ℝ} (hR : 0 < R)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ v, 0 ≤ φ v) ∧ (∀ v ∈ Metric.closedBall y R, φ v = 1) ∧
      (∀ v, 2 * R < ‖v - y‖ → Laplacian.laplacian φ v = 0) ∧
      ∀ v, |Laplacian.laplacian φ v| ≤ R⁻¹ ^ 2 * K₀ := by
  have hRinv : R⁻¹ ≠ 0 := inv_ne_zero hR.ne'
  refine ⟨fun v => bump d (R⁻¹ • (v - y)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (bump d).contDiff.comp
      (by fun_prop : ContDiff ℝ ∞ fun v : EuclideanSpace ℝ (Fin d) => R⁻¹ • (v - y))
  · exact (bump d).hasCompactSupport.comp_homeomorph
      ((Homeomorph.subRight y).trans (Homeomorph.smulOfNeZero R⁻¹ hRinv))
  · intro v
    exact (bump d).nonneg
  · intro v hv
    refine (bump d).one_of_mem_closedBall ?_
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have h1 : ‖v - y‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hv
      exact hv
    calc R⁻¹ * ‖v - y‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hR).le
      _ = (bump d).rIn := by simp [bump, hR.ne']
  · intro v hv
    rw [laplacian_eq_sum_hess]
    refine Finset.sum_eq_zero fun i _ => hess_eq_zero_of_eventuallyEq ?_ _
    have hopen : IsOpen {w : EuclideanSpace ℝ (Fin d) | 2 * R < ‖w - y‖} :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    filter_upwards [hopen.mem_nhds hv] with w hw
    have hw' : 2 * R < ‖w - y‖ := hw
    have : R⁻¹ • (w - y) ∉ Function.support (bump d) := by
      rw [(bump d).support_eq, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hR)]
      change ¬ R⁻¹ * ‖w - y‖ < 2
      rw [not_lt]
      calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
        _ ≤ R⁻¹ * ‖w - y‖ := mul_le_mul_of_nonneg_left hw'.le (inv_pos.mpr hR).le
    simpa using this
  · intro v
    rw [laplacian_comp_smul_sub (χ := ⇑(bump d)) ((bump d).contDiff) R⁻¹ y v, abs_mul,
      abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hK₀ _) (by positivity)

/-- The defect of a norm from a tangent plane at `y` is at most `2 Λ |v - y|`. -/
private lemma sub_tangent_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {y ξ : EuclideanSpace ℝ (Fin d)} (hξ : CERW.IsSubgradient Ψ y ξ)
    (v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ Ψ v - (Ψ y + inner ℝ ξ (v - y)) ∧
      Ψ v - (Ψ y + inner ℝ ξ (v - y)) ≤ 2 * CERW.normMax Ψ * ‖v - y‖ := by
  refine ⟨by linarith [hξ v], ?_⟩
  have h1 : Ψ v - Ψ y ≤ CERW.normMax Ψ * ‖v - y‖ :=
    (le_abs_self _).trans ((CERW.Generic.Norm.abs_sub_le hΨ v y).trans
      (CERW.Generic.Norm.le_normMax_mul hΨ (v - y)))
  have h2 : -inner ℝ ξ (v - y) ≤ CERW.normMax Ψ * ‖v - y‖ := by
    calc -inner ℝ ξ (v - y) ≤ ‖ξ‖ * ‖v - y‖ := by
          have := neg_le_abs (inner ℝ ξ (v - y))
          exact this.trans (abs_real_inner_le_norm _ _)
      _ ≤ CERW.normMax Ψ * ‖v - y‖ :=
          mul_le_mul_of_nonneg_right (norm_le_normMax_of_isSubgradient hΨ hξ) (norm_nonneg _)
  linarith

/-- The hessian growth `eq:hessian-growth`: `m(B(y, R)) ≤ C Λ_Ψ R^{d-1}`, for every locally finite
measure `m` with distributional Laplacian `Δ Ψ` and every point `y` at which `Ψ` has a
subgradient. -/
private theorem exists_measure_ball_le (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}, CERW.IsNorm Ψ →
      ∀ {m : Measure (EuclideanSpace ℝ (Fin d))}, IsLocallyFiniteMeasure m →
      CERW.IsDistribLaplacian Ψ m → ∀ {y ξ : EuclideanSpace ℝ (Fin d)},
      CERW.IsSubgradient Ψ y ξ → ∀ {R : ℝ}, 0 < R →
        m (Metric.ball y R) ≤ ENNReal.ofReal (K * CERW.normMax Ψ * R ^ (d - 1)) := by
  obtain ⟨K₀, hK₀nn, hK₀⟩ := exists_bound_laplacian_bump d
  refine ⟨2 ^ (d + 2) * CERW.unitBallVolume d * K₀, by
    have := CERW.unitBallVolume_pos d
    positivity, ?_⟩
  intro Ψ hΨ m hm hlap y ξ hξ R hR
  obtain ⟨φ, hφs, hφc, hφ0, hφ1, hφz, hφb⟩ := exists_testFunction d hK₀ hR y
  have hΛ : 0 ≤ CERW.normMax Ψ := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨u, -, rfl⟩
    exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 u
  have hΨc : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  -- the ball is dominated by the test function
  have hint : Integrable φ m := hφs.continuous.integrable_of_hasCompactSupport hφc
  have hball_le : m (Metric.ball y R) ≤ ENNReal.ofReal (∫ v, φ v ∂m) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hφ0)]
    calc m (Metric.ball y R) = ∫⁻ v in Metric.ball y R, ENNReal.ofReal (φ v) ∂m := by
          rw [setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
            (g := fun _ => 1) (fun v hv => by
              rw [hφ1 v (Metric.ball_subset_closedBall hv)]
              simp)]
          simp
      _ ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m := setLIntegral_le_lintegral _ _
  -- the defining identity of the distributional Laplacian
  have hlap_eq := hlap φ hφs hφc
  -- subtracting the tangent plane does not change the integral
  set a : ℝ := Ψ y - inner ℝ ξ y with ha
  set ℓ : EuclideanSpace ℝ (Fin d) → ℝ := fun v => a + inner ℝ ξ v with hℓ
  have hℓc : Continuous ℓ := by simp only [hℓ]; fun_prop
  have hΔc : Continuous (Laplacian.laplacian φ) := continuous_laplacian hφs
  have hΔs : HasCompactSupport (Laplacian.laplacian φ) := hasCompactSupport_laplacian hφc
  have hiΨ : Integrable (fun v => Ψ v * Laplacian.laplacian φ v) :=
    (hΨc.mul hΔc).integrable_of_hasCompactSupport hΔs.mul_left
  have hiℓ : Integrable (fun v => ℓ v * Laplacian.laplacian φ v) :=
    (hℓc.mul hΔc).integrable_of_hasCompactSupport hΔs.mul_left
  have hzero : ∫ v, ℓ v * Laplacian.laplacian φ v = 0 := by
    simp only [hℓ]
    rw [laplacian_eq_sum_hess]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · exact Finset.sum_eq_zero fun i _ => integral_affine_mul_hess hφs hφc a ξ _
    · intro i _
      exact ((by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ v).mul
        (continuous_hess hφs _)).integrable_of_hasCompactSupport
        (hasCompactSupport_hess hφc _).mul_left
  have hsplit : ∫ v, Ψ v * Laplacian.laplacian φ v =
      ∫ v, (Ψ v - ℓ v) * Laplacian.laplacian φ v := by
    have : ∀ v, (Ψ v - ℓ v) * Laplacian.laplacian φ v =
        Ψ v * Laplacian.laplacian φ v - ℓ v * Laplacian.laplacian φ v := fun v => sub_mul _ _ _
    simp_rw [this]
    rw [integral_sub hiΨ hiℓ, hzero, sub_zero]
  -- the pointwise bound
  set c : ℝ := 4 * CERW.normMax Ψ * R * (R⁻¹ ^ 2 * K₀) with hc
  have hpt : ∀ v, ‖(Ψ v - ℓ v) * Laplacian.laplacian φ v‖ ≤
      (Metric.closedBall y (2 * R)).indicator (fun _ => c) v := by
    intro v
    by_cases hv : v ∈ Metric.closedBall y (2 * R)
    · rw [Set.indicator_of_mem hv, Real.norm_eq_abs, abs_mul]
      have hvR : ‖v - y‖ ≤ 2 * R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hv
        exact hv
      obtain ⟨h0, h1⟩ := sub_tangent_le hΨ hξ v
      have hℓv : Ψ v - ℓ v = Ψ v - (Ψ y + inner ℝ ξ (v - y)) := by
        simp only [hℓ, ha, inner_sub_right]
        ring
      rw [hℓv, abs_of_nonneg h0]
      have h2 : Ψ v - (Ψ y + inner ℝ ξ (v - y)) ≤ 4 * CERW.normMax Ψ * R := by
        calc _ ≤ 2 * CERW.normMax Ψ * ‖v - y‖ := h1
          _ ≤ 2 * CERW.normMax Ψ * (2 * R) :=
              mul_le_mul_of_nonneg_left hvR (by positivity)
          _ = 4 * CERW.normMax Ψ * R := by ring
      exact mul_le_mul h2 (hφb v) (abs_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hv, Real.norm_eq_abs, abs_mul]
      have hvR : 2 * R < ‖v - y‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hv
        exact hv
      rw [hφz v hvR]
      simp
  have hvolball : (volume (Metric.closedBall y (2 * R))).toReal =
      (2 * R) ^ d * CERW.unitBallVolume d := by
    have := Measure.addHaar_real_closedBall (volume : Measure (EuclideanSpace ℝ (Fin d))) y
      (by positivity : (0 : ℝ) ≤ 2 * R)
    rw [finrank_euclideanSpace_fin] at this
    simpa [Measure.real_def, CERW.unitBallVolume] using this
  have hint_ind : Integrable ((Metric.closedBall y (2 * R)).indicator fun _ => c) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
      (integrableOn_const measure_closedBall_lt_top.ne)
  have hintegral_le : ∫ v, Ψ v * Laplacian.laplacian φ v ≤
      2 ^ (d + 2) * CERW.unitBallVolume d * K₀ * CERW.normMax Ψ * R ^ (d - 1) := by
    rw [hsplit]
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hint_ind (Eventually.of_forall hpt)).trans ?_
    rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, smul_eq_mul,
      Measure.real_def, hvolball, hc]
    have hRd := pow_mul_mul_inv_sq hR hd
    have hω := CERW.unitBallVolume_pos d
    refine le_of_eq ?_
    calc (2 * R) ^ d * CERW.unitBallVolume d * (4 * CERW.normMax Ψ * R * (R⁻¹ ^ 2 * K₀))
        = 2 ^ (d + 2) * CERW.unitBallVolume d * K₀ * CERW.normMax Ψ * (R ^ d * R * R⁻¹ ^ 2) := by
          rw [mul_pow, pow_add]
          ring
      _ = _ := by rw [hRd]
  calc m (Metric.ball y R) ≤ ENNReal.ofReal (∫ v, φ v ∂m) := hball_le
    _ ≤ ENNReal.ofReal (2 ^ (d + 2) * CERW.unitBallVolume d * K₀ * CERW.normMax Ψ *
        R ^ (d - 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hlap_eq]
        exact hintegral_le

end Hessian

section Positivity

open scoped ContDiff

variable {d : ℕ}

/-- One-dimensional second difference: if `a' = g` and `g' = g₂` (derivatives everywhere) and
`|g₂ t - g₂ 0| ≤ η` for `|t| ≤ h`, then `|a h + a (-h) - 2 a 0 - g₂ 0 h²| ≤ 2 η h²`. -/
private lemma abs_secondDiff_sub_le {a g g₂ : ℝ → ℝ} (ha : ∀ t, HasDerivAt a (g t) t)
    (hg : ∀ t, HasDerivAt g (g₂ t) t) {η h : ℝ} (hh : 0 ≤ h)
    (hη : ∀ t, |t| ≤ h → |g₂ t - g₂ 0| ≤ η) :
    |a h + a (-h) - 2 * a 0 - g₂ 0 * h ^ 2| ≤ 2 * η * h ^ 2 := by
  -- m s = g s - g (-s) - 2 g₂ 0 s
  have hm : ∀ s, HasDerivAt (fun s => g s - g (-s) - 2 * g₂ 0 * s)
      (g₂ s + g₂ (-s) - 2 * g₂ 0) s := by
    intro s
    have h1 := hg s
    have h2 := HasDerivAt.comp s (hg (-s)) (hasDerivAt_neg s)
    have h3 := ((h1.sub h2).sub ((hasDerivAt_id s).const_mul (2 * g₂ 0)))
    exact h3.congr_deriv (by ring)
  have hmb : ∀ s, 0 ≤ s → s ≤ h → |g s - g (-s) - 2 * g₂ 0 * s| ≤ 2 * η * s := by
    intro s hs0 hsh
    have hbound : ∀ r ∈ Set.Icc 0 s, ‖g₂ r + g₂ (-r) - 2 * g₂ 0‖ ≤ 2 * η := by
      intro r hr
      have h1 := hη r (by rw [abs_of_nonneg hr.1]; linarith [hr.2])
      have h2 := hη (-r) (by rw [abs_neg, abs_of_nonneg hr.1]; linarith [hr.2])
      rw [Real.norm_eq_abs]
      calc |g₂ r + g₂ (-r) - 2 * g₂ 0| = |(g₂ r - g₂ 0) + (g₂ (-r) - g₂ 0)| := by ring_nf
        _ ≤ |g₂ r - g₂ 0| + |g₂ (-r) - g₂ 0| := abs_add_le _ _
        _ ≤ 2 * η := by linarith
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => g s - g (-s) - 2 * g₂ 0 * s)
      (f' := fun s => g₂ s + g₂ (-s) - 2 * g₂ 0) (C := 2 * η) (s := Set.Icc 0 s)
      (fun r _ => (hm r).hasDerivWithinAt) hbound (convex_Icc 0 s)
      (Set.left_mem_Icc.mpr hs0) (Set.right_mem_Icc.mpr hs0)
    simpa [Real.norm_eq_abs, abs_of_nonneg hs0] using this
  have hk : ∀ s, HasDerivAt (fun s => a s + a (-s) - 2 * a 0 - g₂ 0 * s ^ 2)
      (g s - g (-s) - 2 * g₂ 0 * s) s := by
    intro s
    have h1 := ha s
    have h2 := HasDerivAt.comp s (ha (-s)) (hasDerivAt_neg s)
    have h3 := (h1.add h2).sub_const (2 * a 0)
    have h4 := (((hasDerivAt_id s).pow 2).const_mul (g₂ 0))
    have h5 := h3.sub h4
    exact h5.congr_deriv (by simp only [id, Nat.cast_ofNat]; ring)
  have hkb : ∀ r ∈ Set.Icc 0 h, ‖g r - g (-r) - 2 * g₂ 0 * r‖ ≤ 2 * η * h := by
    intro r hr
    rw [Real.norm_eq_abs]
    refine (hmb r hr.1 hr.2).trans ?_
    have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0 (by simpa using hh))
    exact mul_le_mul_of_nonneg_left hr.2 (by linarith)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => a s + a (-s) - 2 * a 0 - g₂ 0 * s ^ 2)
    (f' := fun s => g s - g (-s) - 2 * g₂ 0 * s) (C := 2 * η * h) (s := Set.Icc 0 h)
    (fun r _ => (hk r).hasDerivWithinAt) hkb (convex_Icc 0 h)
    (Set.left_mem_Icc.mpr hh) (Set.right_mem_Icc.mpr hh)
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hh, neg_zero] at this
  have h0 : a 0 + a 0 - 2 * a 0 - g₂ 0 * 0 ^ 2 = 0 := by ring
  rw [h0] at this
  simpa [sub_zero, abs_of_nonneg hh, mul_assoc, pow_two] using this

/-- The derivative of `t ↦ φ (v + t e)`. -/
private lemma hasDerivAt_line {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (v e : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => φ (v + t • e)) (fderiv ℝ φ (v + t • e) e) t := by
  have hpath : HasDerivAt (fun t : ℝ => v + t • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add v
  have hd : DifferentiableAt ℝ φ (v + t • e) :=
    (hφ.differentiable (by norm_num)) _
  exact hd.hasFDerivAt.comp_hasDerivAt t hpath

/-- The derivative of `t ↦ Dφ(v + t e) e`. -/
private lemma hasDerivAt_line_deriv {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (v e : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ φ (v + t • e) e) (hess φ (v + t • e) e) t := by
  have hpath : HasDerivAt (fun t : ℝ => v + t • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add v
  have hdd : DifferentiableAt ℝ (fderiv ℝ φ) (v + t • e) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) _
  have h1 := hdd.hasFDerivAt.comp_hasDerivAt t hpath
  have h2 := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt t h1
  exact h2.congr_deriv (by simp [hess])

/-- The second difference of a `C²` function along a line, against `D²φ(v)(e,e) h²`. -/
private lemma abs_secondDiff_sub_hess_le {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (v e : EuclideanSpace ℝ (Fin d)) {η h : ℝ} (hh : 0 ≤ h)
    (hη : ∀ t : ℝ, |t| ≤ h → |hess φ (v + t • e) e - hess φ v e| ≤ η) :
    |φ (v + h • e) + φ (v + (-h) • e) - 2 * φ v - hess φ v e * h ^ 2| ≤ 2 * η * h ^ 2 := by
  have := abs_secondDiff_sub_le (a := fun t : ℝ => φ (v + t • e))
    (g := fun t => fderiv ℝ φ (v + t • e) e) (g₂ := fun t => hess φ (v + t • e) e)
    (hasDerivAt_line hφ v e) (hasDerivAt_line_deriv hφ v e) hh (by simpa using hη)
  simpa using this

/-- Convexity of a norm: `2 Ψ(v) ≤ Ψ(v + w) + Ψ(v - w)`. -/
private lemma two_mul_le_add_sub {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    (v w : EuclideanSpace ℝ (Fin d)) : 2 * Ψ v ≤ Ψ (v + w) + Ψ (v - w) := by
  have h := hΨ.add_le (v + w) (v - w)
  have h2 : (v + w) + (v - w) = (2 : ℝ) • v := by module
  rw [h2, hΨ.smul] at h
  simpa using h

/-- A product of a continuous function with a compactly supported continuous function is
integrable. -/
private lemma integrable_mul_of_hasCompactSupport {f φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun v => f v * φ v) :=
  Continuous.integrable_of_hasCompactSupport (hf.mul hφ) hc.mul_left

/-- For every `h > 0` the second difference quotient of the test function integrates against a
norm to a nonnegative number. -/
private lemma integral_mul_secondDiff_nonneg {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : CERW.IsNorm Ψ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ v, 0 ≤ φ v) (e : EuclideanSpace ℝ (Fin d)) {h : ℝ} (hh : 0 < h) :
    0 ≤ ∫ v, Ψ v * ((φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2) := by
  have hΨc : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  have hφ1 : Continuous fun v => φ (v + h • e) := hφ.comp (continuous_id.add continuous_const)
  have hφ2 : Continuous fun v => φ (v - h • e) := hφ.comp (continuous_id.sub continuous_const)
  have hc1 : HasCompactSupport fun v => φ (v + h • e) :=
    hc.comp_homeomorph (Homeomorph.addRight (h • e))
  have hc2 : HasCompactSupport fun v => φ (v - h • e) :=
    hc.comp_homeomorph (Homeomorph.subRight (h • e))
  have i1 := integrable_mul_of_hasCompactSupport hΨc hφ1 hc1
  have i2 := integrable_mul_of_hasCompactSupport hΨc hφ2 hc2
  have i0 := integrable_mul_of_hasCompactSupport hΨc hφ hc
  have j1 : Integrable (fun v => Ψ (v - h • e) * φ v) :=
    integrable_mul_of_hasCompactSupport
      (hΨc.comp (continuous_id.sub continuous_const) : Continuous fun v => Ψ (v - h • e)) hφ hc
  have j2 : Integrable (fun v => Ψ (v + h • e) * φ v) :=
    integrable_mul_of_hasCompactSupport
      (hΨc.comp (continuous_id.add continuous_const) : Continuous fun v => Ψ (v + h • e)) hφ hc
  have k1 : Integrable (fun v => Ψ v * φ (v + h • e) + Ψ v * φ (v - h • e)) := i1.add i2
  have k2 : Integrable (fun v => 2 * (Ψ v * φ v)) := i0.const_mul 2
  have k3 : Integrable (fun v => Ψ (v + h • e) * φ v + Ψ (v - h • e) * φ v) := j2.add j1
  have t1 : ∫ v, Ψ v * φ (v + h • e) = ∫ v, Ψ (v - h • e) * φ v := by
    rw [← integral_add_right_eq_self (fun v => Ψ (v - h • e) * φ v) (h • e)]
    simp
  have t2 : ∫ v, Ψ v * φ (v - h • e) = ∫ v, Ψ (v + h • e) * φ v := by
    rw [← integral_sub_right_eq_self (fun v => Ψ (v + h • e) * φ v) (h • e)]
    simp
  have hsum : ∫ v, Ψ v * ((φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2) =
      (∫ v, φ v * (Ψ (v + h • e) + Ψ (v - h • e) - 2 * Ψ v)) / h ^ 2 := by
    have hpt : ∀ v, Ψ v * ((φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2) =
        ((Ψ v * φ (v + h • e) + Ψ v * φ (v - h • e)) - 2 * (Ψ v * φ v)) / h ^ 2 := by
      intro v
      ring
    simp_rw [hpt]
    rw [integral_div, integral_sub k1 k2, integral_add i1 i2, integral_const_mul, t1, t2]
    have hq : ∀ v, φ v * (Ψ (v + h • e) + Ψ (v - h • e) - 2 * Ψ v) =
        (Ψ (v + h • e) * φ v + Ψ (v - h • e) * φ v) - 2 * (Ψ v * φ v) := by
      intro v
      ring
    simp_rw [hq]
    rw [integral_sub k3 k2, integral_add j2 j1, integral_const_mul]
    ring
  rw [hsum]
  refine div_nonneg (integral_nonneg fun v => ?_) (by positivity)
  have := two_mul_le_add_sub hΨ v (h • e)
  exact mul_nonneg (hφ0 v) (by linarith)

/-- Positivity of the distributional Laplacian of a norm in one direction: for a nonnegative
smooth compactly supported `φ` and `‖e‖ ≤ 1`, `∫ Ψ D²φ(e, e) ≥ 0`. -/
private lemma integral_mul_hess_nonneg {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : CERW.IsNorm Ψ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ v, 0 ≤ φ v) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ ≤ 1) :
    0 ≤ ∫ v, Ψ v * hess φ v e := by
  have hΨc : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  have hφc : Continuous φ := hφ.continuous
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 ≤ R ∧
      tsupport φ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R := by
    obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
    exact ⟨max R₀ 0, le_max_right _ _,
      hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hzero : ∀ w : EuclideanSpace ℝ (Fin d), R < ‖w‖ → φ w = 0 := by
    intro w hw
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have := hR h
    rw [mem_closedBall_zero_iff] at this
    linarith
  obtain ⟨M, hM⟩ := (continuous_hess hφ e).bounded_above_of_compact_support
    (hasCompactSupport_hess hc e)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d))
    (R + 1)).exists_bound_of_continuousOn
    hΨc.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp; linarith))
  set S : ℝ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun h v => (φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2 with hS
  -- the pointwise second-difference estimate
  have hest : ∀ v : EuclideanSpace ℝ (Fin d), ∀ {η h : ℝ}, 0 < h →
      (∀ t : ℝ, |t| ≤ h → |hess φ (v + t • e) e - hess φ v e| ≤ η) →
      |S h v - hess φ v e| ≤ 2 * η := by
    intro v η h hh hη
    have h1 := abs_secondDiff_sub_hess_le hφ2 v e hh.le hη
    have h2 : φ (v + (-h) • e) = φ (v - h • e) := by rw [neg_smul, ← sub_eq_add_neg]
    rw [h2] at h1
    simp only [hS]
    have hh2 : 0 < h ^ 2 := by positivity
    have h3 : |(φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2 - hess φ v e| =
        |φ (v + h • e) + φ (v - h • e) - 2 * φ v - hess φ v e * h ^ 2| / h ^ 2 := by
      rw [← abs_of_pos hh2, ← abs_div, abs_of_pos hh2]
      congr 1
      field_simp
    rw [h3, div_le_iff₀ hh2]
    nlinarith [h1]
  have hlim : Tendsto (fun h => ∫ v, Ψ v * S h v) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, Ψ v * hess φ v e)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + 1)).indicator
        (fun _ => B * (5 * M)) v) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun h => ?_
      have : Continuous fun v => Ψ v * S h v := by
        simp only [hS]
        exact hΨc.mul (((hφc.comp (continuous_id.add continuous_const)).add
          (hφc.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hφc)
          |>.div_const _)
      exact this.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with h hh
      refine Eventually.of_forall fun v => ?_
      by_cases hv : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + 1)
      · rw [Set.indicator_of_mem hv]
        have hη : ∀ t : ℝ, |t| ≤ h → |hess φ (v + t • e) e - hess φ v e| ≤ 2 * M := by
          intro t _
          have h1 := hM (v + t • e)
          have h2 := hM v
          rw [Real.norm_eq_abs] at h1 h2
          calc |hess φ (v + t • e) e - hess φ v e|
              ≤ |hess φ (v + t • e) e| + |hess φ v e| := abs_sub _ _
            _ ≤ 2 * M := by linarith
        have h1 := hest v hh.1 hη
        have h2 := hM v
        rw [Real.norm_eq_abs] at h2
        have h3 : |S h v| ≤ 5 * M := by
          have := abs_sub_abs_le_abs_sub (S h v) (hess φ v e)
          linarith
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by simpa using hB v hv) h3 (abs_nonneg _) hB0
      · rw [Set.indicator_of_notMem hv]
        have hv' : R + 1 < ‖v‖ := by
          simpa [mem_closedBall_zero_iff] using hv
        have hT : ∀ w : EuclideanSpace ℝ (Fin d), ‖w - v‖ ≤ 1 → φ w = 0 := by
          intro w hw
          refine hzero w ?_
          have := norm_sub_norm_le v w
          rw [norm_sub_rev] at this
          linarith
        have hs1 : φ (v + h • e) = 0 := hT _ (by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh.1]
          nlinarith [hh.2, norm_nonneg e])
        have hs2 : φ (v - h • e) = 0 := hT _ (by
          rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh.1]
          nlinarith [hh.2, norm_nonneg e])
        have hs3 : φ v = 0 := hzero v (by linarith)
        simp [hS, hs1, hs2, hs3]
    · exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
        (integrableOn_const measure_closedBall_lt_top.ne)
    · refine Eventually.of_forall fun v => ?_
      have hcont : ContinuousAt (fun t : ℝ => hess φ (v + t • e) e) 0 :=
        ((continuous_hess hφ e).comp
          (continuous_const.add (continuous_id.smul continuous_const))).continuousAt
      refine Tendsto.const_mul (Ψ v) ?_
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont (ε / 4) (by positivity)
      refine ⟨δ, hδ, fun h hh hd => ?_⟩
      have hh0 : 0 < h := hh
      have hd' : h < δ := by
        rwa [Real.dist_eq, sub_zero, abs_of_pos hh0] at hd
      have hη : ∀ t : ℝ, |t| ≤ h → |hess φ (v + t • e) e - hess φ v e| ≤ ε / 4 := by
        intro t ht
        have := hδ' (x := t) (by rw [Real.dist_eq, sub_zero]; exact lt_of_le_of_lt ht hd')
        simp only [zero_smul, add_zero, Real.dist_eq] at this
        exact this.le
      have := hest v hh0 hη
      rw [Real.dist_eq]
      linarith
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun h hh =>
    integral_mul_secondDiff_nonneg hΨ hφc hc hφ0 e hh)

/-- The distributional Laplacian of a norm is nonnegative. -/
private lemma integral_mul_laplacian_nonneg {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : CERW.IsNorm Ψ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ v, 0 ≤ φ v) : 0 ≤ ∫ v, Ψ v * Laplacian.laplacian φ v := by
  have hΨc : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  rw [laplacian_eq_sum_hess]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_nonneg fun i _ => integral_mul_hess_nonneg hΨ hφ hc hφ0 ?_
    simp
  · intro i _
    exact Continuous.integrable_of_hasCompactSupport
      (hΨc.mul (continuous_hess hφ _)) (hasCompactSupport_hess hc _).mul_left

/-- `Ψ Δφ` is integrable for a smooth compactly supported `φ` and continuous `Ψ`. -/
private lemma integrable_mul_laplacian {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨc : Continuous Ψ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun v => Ψ v * Laplacian.laplacian φ v) := by
  rw [laplacian_eq_sum_hess]
  simp_rw [Finset.mul_sum]
  refine integrable_finsetSum _ fun i _ => ?_
  exact Continuous.integrable_of_hasCompactSupport
    (hΨc.mul (continuous_hess hφ _)) (hasCompactSupport_hess hc _).mul_left

end Positivity

section Existence

open scoped ContDiff

open scoped CompactlySupported
open CompactlySupportedContinuousMap

variable {d : ℕ}

/-- The smooth functions among the compactly supported continuous functions. -/
private def smoothSubmodule (d : ℕ) : Submodule ℝ C_c(EuclideanSpace ℝ (Fin d), ℝ) where
  carrier := {f | ContDiff ℝ ∞ (f : EuclideanSpace ℝ (Fin d) → ℝ)}
  zero_mem' := by
    change ContDiff ℝ ∞ (⇑(0 : C_c(EuclideanSpace ℝ (Fin d), ℝ)))
    rw [coe_zero]
    exact contDiff_const
  add_mem' := fun {f g} hf hg => by
    change ContDiff ℝ ∞ (⇑(f + g))
    rw [coe_add]
    exact ContDiff.add hf hg
  smul_mem' := fun c f hf => by
    change ContDiff ℝ ∞ (⇑(c • f))
    rw [coe_smul]
    exact ContDiff.const_smul c hf

/-- The functional `φ ↦ ∫ Ψ Δφ` on the smooth compactly supported functions. -/
private noncomputable def lapFunctional (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hΨc : Continuous Ψ) :
    smoothSubmodule d →ₗ[ℝ] ℝ where
  toFun f := ∫ v, Ψ v * Laplacian.laplacian (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) v
  map_add' := fun f g => by
    have hf : ContDiff ℝ ∞ (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) := f.2
    have hg : ContDiff ℝ ∞ (g.1 : EuclideanSpace ℝ (Fin d) → ℝ) := g.2
    have h1 := integrable_mul_laplacian hΨc hf f.1.hasCompactSupport
    have h2 := integrable_mul_laplacian hΨc hg g.1.hasCompactSupport
    have e : (⇑(f + g : smoothSubmodule d).1 : EuclideanSpace ℝ (Fin d) → ℝ) =
        ⇑f.1 + ⇑g.1 := by
      funext v
      rfl
    show ∫ v, Ψ v * Laplacian.laplacian (⇑(f + g : smoothSubmodule d).1 :
        EuclideanSpace ℝ (Fin d) → ℝ) v = _
    rw [e]
    show _ = (∫ v, Ψ v * Laplacian.laplacian (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) v) +
      ∫ v, Ψ v * Laplacian.laplacian (g.1 : EuclideanSpace ℝ (Fin d) → ℝ) v
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have := ContDiffAt.laplacian_add (x := v) (hf.contDiffAt.of_le (by norm_cast))
      (hg.contDiffAt.of_le (by norm_cast))
    simp only at this ⊢
    rw [this, mul_add]
  map_smul' := fun c f => by
    have hf : ContDiff ℝ ∞ (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) := f.2
    have e : (⇑(c • f : smoothSubmodule d).1 : EuclideanSpace ℝ (Fin d) → ℝ) =
        c • ⇑f.1 := by
      funext v
      rfl
    show ∫ v, Ψ v * Laplacian.laplacian (⇑(c • f : smoothSubmodule d).1 :
        EuclideanSpace ℝ (Fin d) → ℝ) v = c • ∫ v, Ψ v * Laplacian.laplacian
          (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) v
    rw [e, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have := InnerProductSpace.laplacian_smul (x := v) c (hf.contDiffAt.of_le (by norm_cast))
    simp only [smul_eq_mul] at this ⊢
    rw [this]
    ring

/-- A norm has a distributional Laplacian that is a locally finite measure: the functional
`φ ↦ ∫ Ψ Δφ` is positive on the smooth compactly supported functions, so it extends to a positive
functional on all compactly supported continuous functions (M. Riesz), which is an integral by
the Riesz-Markov-Kakutani theorem. -/
theorem exists_isDistribLaplacian {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian Ψ m := by
  have hΨc : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  haveI : PosSMulMono ℝ C_c(EuclideanSpace ℝ (Fin d), ℝ) :=
    ⟨fun a ha f g hfg => by
      rw [CompactlySupportedContinuousMap.le_def] at hfg ⊢
      intro v
      simpa using mul_le_mul_of_nonneg_left (hfg v) ha⟩
  let f : C_c(EuclideanSpace ℝ (Fin d), ℝ) →ₗ.[ℝ] ℝ := ⟨smoothSubmodule d, lapFunctional Ψ hΨc⟩
  have nonneg : ∀ x : f.domain, (x : C_c(EuclideanSpace ℝ (Fin d), ℝ)) ∈
      PointedCone.positive ℝ C_c(EuclideanSpace ℝ (Fin d), ℝ) → 0 ≤ f x := by
    intro x hx
    rw [PointedCone.mem_positive, CompactlySupportedContinuousMap.le_def] at hx
    exact integral_mul_laplacian_nonneg hΨ x.2 x.1.hasCompactSupport fun v => by simpa using hx v
  have dense : ∀ y : C_c(EuclideanSpace ℝ (Fin d), ℝ), ∃ x : f.domain,
      (x : C_c(EuclideanSpace ℝ (Fin d), ℝ)) + y ∈
        PointedCone.positive ℝ C_c(EuclideanSpace ℝ (Fin d), ℝ) := by
    intro y
    obtain ⟨R₀, hR₀⟩ := y.hasCompactSupport.isCompact.isBounded.subset_closedBall
      (0 : EuclideanSpace ℝ (Fin d))
    obtain ⟨N, hN⟩ := y.continuous.bounded_above_of_compact_support y.hasCompactSupport
    have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
    let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
      ⟨max R₀ 0 + 1, max R₀ 0 + 2, by positivity, by linarith⟩
    let bc : C_c(EuclideanSpace ℝ (Fin d), ℝ) := ⟨⟨b, b.continuous⟩, b.hasCompactSupport⟩
    refine ⟨⟨N • bc, ?_⟩, ?_⟩
    · change ContDiff ℝ ∞ (⇑(N • bc))
      rw [coe_smul]
      exact ContDiff.const_smul N b.contDiff
    · rw [PointedCone.mem_positive, CompactlySupportedContinuousMap.le_def]
      intro v
      change 0 ≤ N * b v + y v
      by_cases hv : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (max R₀ 0 + 1)
      · rw [b.one_of_mem_closedBall hv]
        have h1 : |y v| ≤ N := by
          have := hN v
          rwa [Real.norm_eq_abs] at this
        linarith [neg_abs_le (y v)]
      · have hy : y v = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun h => hv ?_
          have := hR₀ h
          exact Metric.closedBall_subset_closedBall (by linarith [le_max_left R₀ 0]) this
        rw [hy, add_zero]
        exact mul_nonneg hN0 b.nonneg
  obtain ⟨g, hg, hgpos⟩ := riesz_extension _ f nonneg dense
  let Λ : C_c(EuclideanSpace ℝ (Fin d), ℝ) →ₚ[ℝ] ℝ :=
    ⟨g, fun a b hab => by
      have := hgpos (b - a) (by rw [PointedCone.mem_positive]; exact sub_nonneg.mpr hab)
      rw [map_sub] at this
      exact sub_nonneg.mp this⟩
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, ?_⟩
  intro φ hφ hc
  let φc : C_c(EuclideanSpace ℝ (Fin d), ℝ) := ⟨⟨φ, hφ.continuous⟩, hc⟩
  have h1 := RealRMK.integral_rieszMeasure Λ φc
  have h2 : Λ φc = f ⟨φc, hφ⟩ := hg ⟨φc, hφ⟩
  exact h1.trans h2

end Existence

section DirectionReplacement

open MeasureTheory Filter Topology LatticeProb CERW CERW.Support.Occupation CERW.Generic.Kernel
open scoped ENNReal Classical

section FarSum

variable {d : ℕ}

/-- The number of lattice sites within `r` of a point is at most `(r + √d)^d ω_d`: their unit cells
are disjoint and lie in the ball of radius `r + √d`. -/
private lemma card_filter_ball_le (hd : 1 ≤ d) (T : Finset (Site d))
    (z : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r) :
    ((T.filter fun x => z ∈ Metric.ball (toSpace x) r).card : ℝ≥0∞) ≤
      ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d) := by
  set T' := T.filter fun x => z ∈ Metric.ball (toSpace x) r with hT'
  have hδ : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsub : (⋃ x ∈ T', cell x) ⊆ Metric.ball z (r + Real.sqrt d) := by
    intro v hv
    obtain ⟨x, hx, hvx⟩ := Set.mem_iUnion₂.mp hv
    have hxz : z ∈ Metric.ball (toSpace x) r := (Finset.mem_filter.mp hx).2
    rw [Metric.mem_ball, dist_eq_norm] at hxz ⊢
    have h1 := norm_sub_toSpace_le_of_mem_cell hvx
    calc ‖v - z‖ = ‖(v - toSpace x) + (toSpace x - z)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖v - toSpace x‖ + ‖toSpace x - z‖ := norm_add_le _ _
      _ = ‖v - toSpace x‖ + ‖z - toSpace x‖ := by rw [norm_sub_rev (toSpace x) z]
      _ < r + Real.sqrt d := by linarith
  calc (T'.card : ℝ≥0∞) = volume (⋃ x ∈ T', cell x) := (volume_biUnion_cell T').symm
    _ ≤ volume (Metric.ball z (r + Real.sqrt d)) := measure_mono hsub
    _ = ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d) := by
        rw [Measure.addHaar_ball_of_pos volume z (by positivity), finrank_euclideanSpace_fin,
          unitBallVolume, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal measure_ball_lt_top.ne]

/-- A multiplicity bound: the balls `B(x, r)` around distinct lattice sites of a finite set `T` have
total measure at most `(r + √d)^d ω_d` times the measure of a set containing all of them. -/
private lemma sum_measure_ball_le (hd : 1 ≤ d) {m : Measure (EuclideanSpace ℝ (Fin d))}
    (T : Finset (Site d)) {r : ℝ} (hr : 0 ≤ r) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUm : MeasurableSet U) (hU : ∀ x ∈ T, Metric.ball (toSpace x) r ⊆ U) :
    ∑ x ∈ T, m (Metric.ball (toSpace x) r) ≤
      ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d) * m U := by
  have hmeas : ∀ x ∈ T, Measurable ((Metric.ball (toSpace x) r).indicator
      (fun _ => (1 : ℝ≥0∞))) := fun x _ =>
    measurable_const.indicator Metric.isOpen_ball.measurableSet
  calc ∑ x ∈ T, m (Metric.ball (toSpace x) r)
      = ∑ x ∈ T, ∫⁻ z, (Metric.ball (toSpace x) r).indicator (fun _ => (1 : ℝ≥0∞)) z ∂m := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet, one_mul]
    _ = ∫⁻ z, ∑ x ∈ T, (Metric.ball (toSpace x) r).indicator (fun _ => (1 : ℝ≥0∞)) z ∂m :=
        (lintegral_finsetSum _ hmeas).symm
    _ ≤ ∫⁻ z, U.indicator
          (fun _ => ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d)) z ∂m := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ U
        · rw [Set.indicator_of_mem hz]
          have := card_filter_ball_le hd T z hr
          calc ∑ x ∈ T, (Metric.ball (toSpace x) r).indicator (fun _ => (1 : ℝ≥0∞)) z
              = ((T.filter fun x => z ∈ Metric.ball (toSpace x) r).card : ℝ≥0∞) := by
                push_cast [Finset.card_filter, Set.indicator_apply]
                rfl
            _ ≤ _ := this
        · rw [Set.indicator_of_notMem hz]
          refine le_of_eq (Finset.sum_eq_zero fun x hx => ?_)
          rw [Set.indicator_of_notMem]
          exact fun h => hz (hU x hx h)
    _ = ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d) * m U := by
        rw [lintegral_indicator_const hUm, mul_comm]

/-- Dyadic shells: a site `x` with `8 √d < |x - y| ≤ R'` lies in the shell `2^k ≤ |x - y| < 2^{k+1}`
with `k = ⌊log₂ ⌊|x - y|⌋⌋ ≤ ⌊log₂ ⌈R'⌉⌋`, and the ball `B(x, 6 √d)` lies in `B(y, 2^{k+2})`. -/
private lemma dyadic_shell {y x : Site d} {R' : ℝ} (hd : 1 ≤ d)
    (hx : 8 * Real.sqrt d < euclidNorm (x - y) ∧ euclidNorm (x - y) ≤ R') :
    Nat.log 2 ⌊euclidNorm (x - y)⌋₊ ≤ Nat.log 2 ⌈R'⌉₊ ∧
      (2 : ℝ) ^ Nat.log 2 ⌊euclidNorm (x - y)⌋₊ ≤ euclidNorm (x - y) ∧
      euclidNorm (x - y) < 2 ^ (Nat.log 2 ⌊euclidNorm (x - y)⌋₊ + 1) := by
  have hδ : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  set ρ := euclidNorm (x - y) with hρ
  have hρ1 : 1 ≤ ρ := by linarith [hx.1]
  have hfl : ⌊ρ⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊ρ⌋₊ := Nat.le_floor (by simpa using hρ1)
    omega
  refine ⟨Nat.log_mono_right ?_, ?_, ?_⟩
  · exact (Nat.floor_le_floor hx.2).trans (Nat.floor_le_ceil R')
  · have h1 : 2 ^ Nat.log 2 ⌊ρ⌋₊ ≤ ⌊ρ⌋₊ := Nat.pow_log_le_self 2 hfl
    calc (2 : ℝ) ^ Nat.log 2 ⌊ρ⌋₊ ≤ ((⌊ρ⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ρ := Nat.floor_le (by linarith)
  · have h1 : ⌊ρ⌋₊ < 2 ^ (Nat.log 2 ⌊ρ⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    calc ρ < (⌊ρ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ρ
      _ ≤ ((2 ^ (Nat.log 2 ⌊ρ⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = 2 ^ (Nat.log 2 ⌊ρ⌋₊ + 1) := by push_cast; ring

/-- The far sum in `ℝ≥0∞`: if `m (B(y, R)) ≤ Kg R^{d-1}` for every `R`, then
`Σ_x |x - y|^{-(d-1)} m(B(x, 6√d))` over sites with `8 √d < |x - y| ≤ R'` is at most
`(⌊log₂ ⌈R'⌉⌋ + 1) (7√d)^d ω_d Kg 4^{d-1}`. -/
private lemma sum_far_le (hd : 2 ≤ d) {m : Measure (EuclideanSpace ℝ (Fin d))} {Kg : ℝ}
    (hKg : 0 ≤ Kg) (y : Site d)
    (hgrowth : ∀ {R : ℝ}, 0 < R → m (Metric.ball (toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (d - 1)))
    (F : Finset (Site d)) {R' : ℝ}
    (hF : ∀ x ∈ F, 8 * Real.sqrt d < euclidNorm (x - y) ∧ euclidNorm (x - y) ≤ R') :
    ∑ x ∈ F, ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
        m (Metric.ball (toSpace x) (6 * Real.sqrt d)) ≤
      ((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          ((6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d * Kg * 4 ^ (d - 1)) := by
  have hd1 : 1 ≤ d := by omega
  have hδ : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  set K := Nat.log 2 ⌈R'⌉₊ with hK
  set k : Site d → ℕ := fun x => Nat.log 2 ⌊euclidNorm (x - y)⌋₊ with hk
  set Nr : ℝ := (6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d with hNr
  have hmaps : ∀ x ∈ F, k x ∈ Finset.range (K + 1) := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (dyadic_shell hd1 (hF x hx)).1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ Finset.range (K + 1),
      ∑ x ∈ F.filter (fun x => k x = j), ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
        m (Metric.ball (toSpace x) (6 * Real.sqrt d)) ≤
      ENNReal.ofReal (Nr * Kg * 4 ^ (d - 1)) := by
    intro j _
    set Fj := F.filter (fun x => k x = j) with hFj
    have hmem : ∀ x ∈ Fj, x ∈ F ∧ k x = j := fun x hx => Finset.mem_filter.mp hx
    have hshell : ∀ x ∈ Fj,
        (2 : ℝ) ^ j ≤ euclidNorm (x - y) ∧ euclidNorm (x - y) < 2 ^ (j + 1) := by
      intro x hx
      obtain ⟨hxF, hxj⟩ := hmem x hx
      have h := dyadic_shell hd1 (hF x hxF)
      have hxj' : Nat.log 2 ⌊euclidNorm (x - y)⌋₊ = j := hxj
      rw [hxj'] at h
      exact ⟨h.2.1, h.2.2⟩
    have hsub : ∀ x ∈ Fj, Metric.ball (toSpace x) (6 * Real.sqrt d) ⊆
        Metric.ball (toSpace y) (2 ^ (j + 2)) := by
      intro x hx z hz
      obtain ⟨hxF, -⟩ := hmem x hx
      obtain ⟨-, h2⟩ := hshell x hx
      have h8 := (hF x hxF).1
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hxy : ‖toSpace x - toSpace y‖ = euclidNorm (x - y) := by rw [← toSpace_sub, norm_toSpace]
      calc ‖z - toSpace y‖ = ‖(z - toSpace x) + (toSpace x - toSpace y)‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖z - toSpace x‖ + ‖toSpace x - toSpace y‖ := norm_add_le _ _
        _ < 6 * Real.sqrt d + euclidNorm (x - y) := by rw [hxy]; linarith
        _ ≤ 2 ^ (j + 2) := by
            have : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
            rw [this]
            linarith
    have hinv : ∀ x ∈ Fj, ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) ≤
        ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) := by
      intro x hx
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := (hshell x hx).1
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 _)
    calc ∑ x ∈ Fj, ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
          m (Metric.ball (toSpace x) (6 * Real.sqrt d))
        ≤ ∑ x ∈ Fj, ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) *
          m (Metric.ball (toSpace x) (6 * Real.sqrt d)) :=
          Finset.sum_le_sum fun x hx => mul_le_mul' (hinv x hx) le_rfl
      _ = ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) *
          ∑ x ∈ Fj, m (Metric.ball (toSpace x) (6 * Real.sqrt d)) := (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) *
          (ENNReal.ofReal Nr * m (Metric.ball (toSpace y) (2 ^ (j + 2)))) :=
          by
            gcongr
            exact sum_measure_ball_le hd1 Fj (r := 6 * Real.sqrt d) (by positivity)
              Metric.isOpen_ball.measurableSet hsub
      _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) *
          (ENNReal.ofReal Nr * ENNReal.ofReal (Kg * ((2 : ℝ) ^ (j + 2)) ^ (d - 1))) :=
          by
            gcongr
            exact hgrowth (by positivity)
      _ = ENNReal.ofReal (Nr * Kg * 4 ^ (d - 1)) := by
          have hNr0 : 0 ≤ Nr := by
            have := unitBallVolume_pos d
            rw [hNr]
            positivity
          have ha0 : 0 ≤ (((2 : ℝ) ^ j) ^ (d - 1))⁻¹ := by positivity
          have hb0 : 0 ≤ Kg * ((2 : ℝ) ^ (j + 2)) ^ (d - 1) := by positivity
          rw [← ENNReal.ofReal_mul hNr0, ← ENNReal.ofReal_mul ha0]
          congr 1
          have h2 : ((2 : ℝ) ^ (j + 2)) ^ (d - 1) = ((2 : ℝ) ^ j) ^ (d - 1) * 4 ^ (d - 1) := by
            rw [← mul_pow, pow_add]
            norm_num
          rw [h2]
          have h3 : (0 : ℝ) < ((2 : ℝ) ^ j) ^ (d - 1) := by positivity
          field_simp
  calc ∑ j ∈ Finset.range (K + 1), ∑ x ∈ F.filter (fun x => k x = j),
        ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
          m (Metric.ball (toSpace x) (6 * Real.sqrt d))
      ≤ ∑ _j ∈ Finset.range (K + 1), ENNReal.ofReal (Nr * Kg * 4 ^ (d - 1)) :=
        Finset.sum_le_sum hfib
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end FarSum

section Direction

variable {d : ℕ}

/-- For `t > 0`, `t^{1-d} = (t^{d-1})⁻¹`. -/
private lemma rpow_one_sub_eq_inv_pow {t : ℝ} (ht : 0 < t) (hd : 1 ≤ d) :
    t ^ (1 - (d : ℝ)) = (t ^ (d - 1))⁻¹ := by
  have : (1 - (d : ℝ)) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd]
    ring
  rw [this, Real.rpow_neg ht.le, Real.rpow_natCast]

/-- A bound for the integral of the kernel against a measurable bounded field on a set of finite
volume: if `‖g v‖ ‖v - z‖^{1-d} ≤ h v` on `D` then `|∫_D ⟨g, K(· - z)⟩| ≤ ∫_D h`. -/
private lemma abs_setIntegral_inner_newtonField_le (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (z : EuclideanSpace ℝ (Fin d)) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : IntegrableOn h D) (hpt : ∀ v ∈ D, ‖g v‖ * ‖v - z‖ ^ (1 - (d : ℝ)) ≤ h v) :
    |∫ v in D, inner ℝ (g v) (newtonField (v - z))| ≤ ∫ v in D, h v := by
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hh ?_
  refine (ae_restrict_iff' hD).mpr (Eventually.of_forall fun v hv => ?_)
  calc ‖inner ℝ (g v) (newtonField (v - z))‖ ≤ ‖g v‖ * ‖newtonField (v - z)‖ :=
        norm_inner_le_norm _ _
    _ = ‖g v‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by rw [norm_newtonField hd]
    _ ≤ h v := hpt v hv

/-- The logarithmic count of dyadic levels: `⌊log₂ ⌈R'⌉⌋ + 1 ≤ (1 + 1/log 2) log (R' + 2)`. -/
private lemma natLog_ceil_add_one_le {R' : ℝ} (hR' : 1 ≤ R') :
    ((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log (R' + 2) := by
  have hL : 1 ≤ Real.log (R' + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : (0 : ℝ) < (⌈R'⌉₊ : ℝ) := by
    have : 0 < ⌈R'⌉₊ := Nat.ceil_pos.mpr (by linarith)
    exact_mod_cast this
  have h1 : (Nat.log 2 ⌈R'⌉₊ : ℝ) ≤ Real.logb 2 (⌈R'⌉₊ : ℝ) := Real.natLog_le_logb _ _
  have h2 : Real.log (⌈R'⌉₊ : ℝ) ≤ Real.log (R' + 2) :=
    Real.log_le_log hceil (by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ R')])
  have h3 : (Nat.log 2 ⌈R'⌉₊ : ℝ) ≤ Real.log (R' + 2) / Real.log 2 := by
    refine h1.trans ?_
    rw [Real.logb]
    exact div_le_div_of_nonneg_right h2 hlog2.le
  push_cast
  calc (Nat.log 2 ⌈R'⌉₊ : ℝ) + 1 ≤ Real.log (R' + 2) / Real.log 2 + 1 := by linarith
    _ ≤ (1 + 1 / Real.log 2) * Real.log (R' + 2) := by
        have : Real.log (R' + 2) / Real.log 2 = 1 / Real.log 2 * Real.log (R' + 2) := by ring
        rw [this]
        nlinarith

/-- The far sum in `ℝ`, for a locally finite measure. -/
private lemma sum_far_real_le (hd : 2 ≤ d) {m : Measure (EuclideanSpace ℝ (Fin d))}
    (hmfin : IsLocallyFiniteMeasure m) {Kg : ℝ}
    (hKg : 0 ≤ Kg) (y : Site d)
    (hgrowth : ∀ {R : ℝ}, 0 < R → m (Metric.ball (toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (d - 1)))
    (F : Finset (Site d)) {R' : ℝ}
    (hF : ∀ x ∈ F, 8 * Real.sqrt d < euclidNorm (x - y) ∧ euclidNorm (x - y) ≤ R') :
    ∑ x ∈ F, (euclidNorm (x - y) ^ (d - 1))⁻¹ *
        (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal ≤
      ((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ) *
        ((6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d * Kg * 4 ^ (d - 1)) := by
  have h := sum_far_le hd hKg y hgrowth F hF
  have hfin : ∀ x ∈ F, ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
      m (Metric.ball (toSpace x) (6 * Real.sqrt d)) ≠ ⊤ := fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hT : ((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal
        ((6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d * Kg * 4 ^ (d - 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono hT h
  rw [ENNReal.toReal_sum hfin] at h2
  have hω := unitBallVolume_pos d
  have hT0 : 0 ≤ (6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d * Kg * 4 ^ (d - 1) := by
    positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hT0] at h2
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) h2
  have hx0 : 0 ≤ (euclidNorm (x - y) ^ (d - 1))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (euclidNorm_nonneg _) _)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx0]

/-- The direction replacement: replacing the lattice drift `ξ(x)` by the gradient `∇Ψ(v)` on the
cells costs `O(log(R' + 2))` in the source sum, given the cell estimate of `lem:cell` and the
hessian growth of `Δ Ψ`. -/
private theorem exists_sum_abs_setIntegral_sub_gradient_le (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {m : Measure (EuclideanSpace ℝ (Fin d))} (hmfin : IsLocallyFiniteMeasure m)
    {Cc Kg : ℝ} (hCc : 0 ≤ Cc) (hKg : 0 ≤ Kg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)), (∀ x, ‖ξ x‖ ≤ normMax Ψ) →
      (∀ x : Site d, ENNReal.ofReal (∫ v in cell x, ‖gradient Ψ v - ξ x‖) ≤
        ENNReal.ofReal Cc * m (Metric.ball (toSpace x) (6 * Real.sqrt d))) →
      ∀ (F : Finset (Site d)) (y : Site d) (R' : ℝ), 1 ≤ R' →
        (∀ x ∈ F, euclidNorm (x - y) ≤ R') →
        (∀ {R : ℝ}, 0 < R →
          m (Metric.ball (toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (d - 1))) →
        ∑ x ∈ F, |∫ v in cell x, inner ℝ (ξ x - gradient Ψ v) (newtonField (v - toSpace y))|
          ≤ C * Real.log (R' + 2) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hdR
  have hω := unitBallVolume_pos d
  have hΛ : 0 ≤ normMax Ψ := normMax_nonneg_of_isNorm hΨ
  set Λ := normMax Ψ with hΛdef
  set ω := unitBallVolume d with hωdef
  set Nr : ℝ := (6 * Real.sqrt d + Real.sqrt d) ^ d * ω with hNr
  have hNr0 : 0 ≤ Nr := by rw [hNr]; positivity
  set Cn : ℝ := 2 * Λ * (d * ω * (9 * Real.sqrt d)) with hCn
  set Cf : ℝ := 2 ^ (d - 1) * Cc * (Nr * Kg * 4 ^ (d - 1)) * (1 + 1 / Real.log 2) with hCf
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCn0 : 0 ≤ Cn := by rw [hCn]; positivity
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  refine ⟨Cn + Cf, add_nonneg hCn0 hCf0, ?_⟩
  intro ξ hξ hcell F y R' hR' hF hgrowth
  have hL : 1 ≤ Real.log (R' + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  set c := toSpace y with hc
  rw [← Finset.sum_filter_add_sum_filter_not F (fun x => euclidNorm (x - y) ≤ 8 * Real.sqrt d)]
  -- the field `ξ x - ∇Ψ` is bounded by `2 Λ`
  have hgb : ∀ x v, ‖ξ x - gradient Ψ v‖ ≤ 2 * Λ := fun x v =>
    (norm_sub_le _ _).trans (by linarith [hξ x, norm_gradient_le_normMax hΨ v])
  have hgmeas : ∀ x, Measurable fun v => ‖gradient Ψ v - ξ x‖ := fun x =>
    continuous_norm.measurable.comp ((measurable_gradient_field Ψ).sub_const _)
  have hcellfin : ∀ x : Site d, volume (cell x) ≠ ⊤ := fun x => by
    rw [volume_cell]
    exact ENNReal.one_ne_top
  have hkernel : ∀ x : Site d, IntegrableOn (fun v => ‖v - c‖ ^ (1 - (d : ℝ))) (cell x) :=
    fun x => (integrableOn_and_setIntegral_le hd1 (measurableSet_cell x) (hcellfin x) c).1
  -- the near terms
  have hnear : ∑ x ∈ F.filter (fun x => euclidNorm (x - y) ≤ 8 * Real.sqrt d),
      |∫ v in cell x, inner ℝ (ξ x - gradient Ψ v) (newtonField (v - c))| ≤ Cn := by
    set Fn := F.filter (fun x => euclidNorm (x - y) ≤ 8 * Real.sqrt d) with hFn
    have hterm : ∀ x ∈ Fn, |∫ v in cell x, inner ℝ (ξ x - gradient Ψ v) (newtonField (v - c))| ≤
        ∫ v in cell x, 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)) := by
      intro x _
      refine abs_setIntegral_inner_newtonField_le hd (measurableSet_cell x) c
        ((hkernel x).const_mul _) fun v _ => ?_
      exact mul_le_mul_of_nonneg_right (hgb x v) (Real.rpow_nonneg (norm_nonneg _) _)
    have hball : IntegrableOn (fun v => 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)))
        (Metric.ball c (9 * Real.sqrt d)) :=
      (integrableOn_ball_and_integral_eq hd1 c
        (by positivity : (0 : ℝ) < 9 * Real.sqrt d)).1.const_mul _
    have hsub : (⋃ x ∈ Fn, cell x) ⊆ Metric.ball c (9 * Real.sqrt d) := by
      intro v hv
      obtain ⟨x, hx, hvx⟩ := Set.mem_iUnion₂.mp hv
      have hxn : euclidNorm (x - y) ≤ 8 * Real.sqrt d := (Finset.mem_filter.mp hx).2
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 := norm_sub_toSpace_le_of_mem_cell hvx
      have hxy : ‖toSpace x - c‖ = euclidNorm (x - y) := by rw [hc, ← toSpace_sub, norm_toSpace]
      calc ‖v - c‖ = ‖(v - toSpace x) + (toSpace x - c)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖v - toSpace x‖ + ‖toSpace x - c‖ := norm_add_le _ _
        _ < 9 * Real.sqrt d := by rw [hxy]; linarith
    calc ∑ x ∈ Fn, |∫ v in cell x, inner ℝ (ξ x - gradient Ψ v) (newtonField (v - c))|
        ≤ ∑ x ∈ Fn, ∫ v in cell x, 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)) := Finset.sum_le_sum hterm
      _ = ∫ v in ⋃ x ∈ Fn, cell x, 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)) :=
          (integral_biUnion_finset Fn (fun x _ => measurableSet_cell x)
            (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => (hkernel x).const_mul _)).symm
      _ ≤ ∫ v in Metric.ball c (9 * Real.sqrt d), 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)) :=
          setIntegral_mono_set hball
            (Eventually.of_forall fun v =>
              mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _))
            hsub.eventuallyLE
      _ = Cn := by
          rw [integral_const_mul,
            (integrableOn_ball_and_integral_eq hd1 c (by positivity : (0 : ℝ) < 9 * Real.sqrt d)).2]
  -- the far terms
  have hfar : ∑ x ∈ F.filter (fun x => ¬ euclidNorm (x - y) ≤ 8 * Real.sqrt d),
      |∫ v in cell x, inner ℝ (ξ x - gradient Ψ v) (newtonField (v - c))| ≤
        Cf * Real.log (R' + 2) := by
    set Ff := F.filter (fun x => ¬ euclidNorm (x - y) ≤ 8 * Real.sqrt d) with hFf
    have hFf' : ∀ x ∈ Ff, 8 * Real.sqrt d < euclidNorm (x - y) ∧ euclidNorm (x - y) ≤ R' := by
      intro x hx
      obtain ⟨hxF, hxn⟩ := Finset.mem_filter.mp hx
      exact ⟨not_le.mp hxn, hF x hxF⟩
    have hterm : ∀ x ∈ Ff,
        |∫ v in cell x, inner ℝ (ξ x - gradient Ψ v) (newtonField (v - c))| ≤
          2 ^ (d - 1) * Cc * ((euclidNorm (x - y) ^ (d - 1))⁻¹ *
            (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal) := by
      intro x hx
      obtain ⟨h8, hR⟩ := hFf' x hx
      have hρ : 0 < euclidNorm (x - y) := by linarith
      set ρ := euclidNorm (x - y) with hρdef
      have hK : (0 : ℝ) ≤ 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ := by positivity
      have hpt : ∀ v ∈ cell x, ‖ξ x - gradient Ψ v‖ * ‖v - c‖ ^ (1 - (d : ℝ)) ≤
          (2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹) * ‖gradient Ψ v - ξ x‖ := by
        intro v hv
        have hvx := norm_sub_toSpace_le_of_mem_cell hv
        have hxy : ‖toSpace x - c‖ = ρ := by rw [hc, ← toSpace_sub, norm_toSpace]
        have hvc : ρ / 2 ≤ ‖v - c‖ := by
          have h1 : ‖toSpace x - c‖ ≤ ‖toSpace x - v‖ + ‖v - c‖ := by
            calc ‖toSpace x - c‖ = ‖(toSpace x - v) + (v - c)‖ := by rw [sub_add_sub_cancel]
              _ ≤ _ := norm_add_le _ _
          rw [norm_sub_rev (toSpace x) v] at h1
          linarith
        have hvcpos : 0 < ‖v - c‖ := by linarith
        rw [rpow_one_sub_eq_inv_pow hvcpos hd1, norm_sub_rev (ξ x)]
        have h2 : (‖v - c‖ ^ (d - 1))⁻¹ ≤ 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ := by
          have h3 : (ρ / 2) ^ (d - 1) ≤ ‖v - c‖ ^ (d - 1) := pow_le_pow_left₀ (by positivity) hvc _
          calc (‖v - c‖ ^ (d - 1))⁻¹ ≤ ((ρ / 2) ^ (d - 1))⁻¹ := inv_anti₀ (by positivity) h3
            _ = 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ := by
                rw [div_pow, inv_div, div_eq_mul_inv]
        calc ‖gradient Ψ v - ξ x‖ * (‖v - c‖ ^ (d - 1))⁻¹
            ≤ ‖gradient Ψ v - ξ x‖ * (2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = _ := by ring
      have hI : IntegrableOn (fun v => (2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹) * ‖gradient Ψ v - ξ x‖)
          (cell x) := by
        refine Integrable.const_mul ?_ _
        refine IntegrableOn.of_bound (hcellfin x).lt_top (hgmeas x).aestronglyMeasurable (2 * Λ) ?_
        refine (ae_restrict_iff' (measurableSet_cell x)).mpr (Eventually.of_forall fun v _ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
        exact hgb x v
      have habs := abs_setIntegral_inner_newtonField_le hd (measurableSet_cell x) c hI hpt
      rw [integral_const_mul] at habs
      have hIx : ∫ v in cell x, ‖gradient Ψ v - ξ x‖ ≤
          Cc * (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal := by
        have h := (ENNReal.ofReal_le_iff_le_toReal
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)).mp (hcell x)
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCc] at h
      refine habs.trans ?_
      calc 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ * ∫ v in cell x, ‖gradient Ψ v - ξ x‖
          ≤ 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ *
            (Cc * (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal) :=
            mul_le_mul_of_nonneg_left hIx hK
        _ = _ := by ring
    have hsum := sum_far_real_le hd hmfin hKg y hgrowth Ff hFf'
    have hlogc := natLog_ceil_add_one_le hR'
    calc ∑ x ∈ Ff, |∫ v in cell x, inner ℝ (ξ x - gradient Ψ v) (newtonField (v - c))|
        ≤ ∑ x ∈ Ff, 2 ^ (d - 1) * Cc * ((euclidNorm (x - y) ^ (d - 1))⁻¹ *
            (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal) := Finset.sum_le_sum hterm
      _ = 2 ^ (d - 1) * Cc * ∑ x ∈ Ff, (euclidNorm (x - y) ^ (d - 1))⁻¹ *
            (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 ^ (d - 1) * Cc * (((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ) * (Nr * Kg * 4 ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 2 ^ (d - 1) * Cc *
          (((1 + 1 / Real.log 2) * Real.log (R' + 2)) * (Nr * Kg * 4 ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlogc (by positivity)) (by positivity)
      _ = Cf * Real.log (R' + 2) := by rw [hCf]; ring
  calc _ ≤ Cn + Cf * Real.log (R' + 2) := add_le_add hnear hfar
    _ ≤ (Cn + Cf) * Real.log (R' + 2) := by nlinarith

end Direction

end DirectionReplacement

section DriftDynkin

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift
open CERW.Support.Occupation CERW.Support.LocalTime

variable {d : ℕ}

/-- The interval Dynkin decomposition of `ℓ_{s,t}(y)` for the walk with a drift field, for a path
from the origin. -/
private theorem intervalLocalTime_eq_driftDynkin {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) (ε : ℝ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ0 : ξ 0 = 0) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) {s t : ℕ} (hst : s ≤ t) (y : Site d) :
    (intervalLocalTime (fun j => X j ω) s t y : ℝ) =
      b (X t ω - y) - b (X s ω - y) +
        ε * (∑ z ∈ departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s,
          inner ℝ (ξ z) (centralDiff b (z - y))) -
        (driftDynkin ε ξ (fun z => b (z - y)) X t ω -
          driftDynkin ε ξ (fun z => b (z - y)) X s ω) := by
  have ht := ContactDynkin.localTime_eq_driftDynkin hb ε ξ hξ0 X ω h0 t y
  have hs := ContactDynkin.localTime_eq_driftDynkin hb ε ξ hξ0 X ω h0 s y
  have hadd : ((localTime (fun j => X j ω) s y : ℕ) : ℝ) +
      (intervalLocalTime (fun j => X j ω) s t y : ℝ) =
      ((localTime (fun j => X j ω) t y : ℕ) : ℝ) := by
    exact_mod_cast localTime_add_intervalLocalTime (fun j => X j ω) hst y
  have hsub : departureRange (fun j => X j ω) s ⊆ departureRange (fun j => X j ω) t :=
    departureRange_mono _ hst
  have hsum := Finset.sum_sdiff_eq_sub hsub
    (f := fun z => inner ℝ (ξ z) (centralDiff b (z - y)))
  rw [hsum, mul_sub]
  linarith [ht, hs, hadd]

end DriftDynkin

section IntervalMartingale

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift
open CERW.Support.Occupation CERW.Support.LocalTime

variable {d : ℕ}

/-- The interval maximum is at least one on a nonempty interval. -/
private lemma one_le_intervalMax (x : ℕ → Site d) {s t : ℕ} (hst : s < t) :
    1 ≤ intervalMax x s t := by
  have hs : s ∈ Ico s t := mem_Ico.mpr ⟨le_rfl, hst⟩
  have h1 : 1 ≤ intervalLocalTime x s t (x s) :=
    Finset.card_pos.mpr ⟨s, mem_filter.mpr ⟨hs, rfl⟩⟩
  exact h1.trans (Finset.le_sup (f := intervalLocalTime x s t) (mem_image_of_mem x hs))

/-- A sum over `s ≤ j < t` of a nonnegative function of the position is at most `M_{s,t}` times
the same function summed over the sites visited in `[s, t)`. -/
private lemma sum_Ico_le_intervalMax_mul (x : ℕ → Site d) (s t : ℕ) {g : Site d → ℝ}
    (hg : ∀ z, 0 ≤ g z) :
    ∑ j ∈ Ico s t, g (x j) ≤ (intervalMax x s t : ℝ) * ∑ z ∈ (Ico s t).image x, g z := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Ico s t) (t := (Ico s t).image x) (g := x)
    (f := fun i => g (x i)) (fun i hi => mem_image_of_mem x hi), Finset.mul_sum]
  refine sum_le_sum fun z _ => ?_
  have hinner : ∑ i ∈ (Ico s t).filter (fun i => x i = z), g (x i) =
      (intervalLocalTime x s t z : ℝ) * g z := by
    rw [sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2], sum_const, nsmul_eq_mul]
    rfl
  rw [hinner]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast intervalLocalTime_le_intervalMax x s t z) (hg z)

/-- The sum of `(1 + |z - y|)^{2-2d}` over any set of sites within `4n` of `y` is `O(log n)`
for `d = 2` and `O(1)` for `d ≥ 3`. -/
private lemma exists_sum_image_le (hd : 2 ≤ d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (x : ℕ → Site d) (n : ℕ), 1 ≤ n → (∀ j, euclidNorm (x j) ≤ j) →
      ∀ y : Site d, euclidNorm y ≤ 3 * n → ∀ s t : ℕ, t ≤ n →
        ∑ z ∈ (Ico s t).image x, (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) ≤
          D * (if d = 2 then Real.log (n + 2) else 1) := by
  by_cases h2 : d = 2
  · obtain ⟨C, hC0, hC⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega)
    refine ⟨2 * C, by positivity, ?_⟩
    intro x n hn hx y hy s t htn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hR : ∀ z ∈ (Ico s t).image x, euclidNorm (z - y) ≤ 4 * n := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hj).2.le.trans htn
      linarith [euclidNorm_sub_le (x j) y, hx j]
    have hexp : (2 - 2 * (d : ℝ)) = -(d : ℝ) := by subst h2; norm_num
    simp only [hexp]
    have h1 := hC ((Ico s t).image x) y (4 * n) (by linarith) hR
    have h3 : Real.log (4 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) := by
      have h4 := Real.log_le_log (by linarith : (0 : ℝ) < 4 * n + 2)
        (by nlinarith : 4 * (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2)
      rw [Real.log_pow] at h4
      simpa using h4
    rw [if_pos h2]
    calc _ ≤ C * Real.log (4 * (n : ℝ) + 2) := h1
      _ ≤ C * (2 * Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_left h3 hC0.le
      _ = 2 * C * Real.log ((n : ℝ) + 2) := by ring
  · obtain ⟨C, hC0, hC⟩ :=
      CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le (d := d) (by omega)
    refine ⟨C, hC0, ?_⟩
    intro x n _ _ y _ s t _
    rw [if_neg h2, mul_one]
    exact hC _ y

/-- The error term `e_n(m) = √m L + L` for `d = 2` and `√(m L) + L` for `d ≥ 3`. -/
private noncomputable def errorBound (d : ℕ) (m L : ℝ) : ℝ :=
  if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L

/-- The error term as `√(m Λ L) + L`, where `Λ = L` for `d = 2` and `Λ = 1` otherwise. -/
private lemma errorBound_eq {m L : ℝ} (hm : 0 ≤ m) (hL : 0 ≤ L) :
    errorBound d m L = Real.sqrt (m * (if d = 2 then L else 1) * L) + L := by
  unfold errorBound
  split_ifs with h
  · rw [show m * L * L = m * (L * L) by ring, Real.sqrt_mul hm, Real.sqrt_mul_self hL]
  · rw [mul_one]

/-- The deterministic step: on a path staying in the ball `|x_j| ≤ j`, the Freedman threshold
`c (√(max(V_t - V_s, 1) L) + B L)` is at most `C e_n(M_{s,t})`. -/
private lemma exists_det_bound (hd : 2 ≤ d) {Cg : ℝ} (hCg : 0 ≤ Cg) {c : ℝ} (hc : 1 ≤ c) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ (x : ℕ → Site d) (n : ℕ), 2 ≤ n → (∀ j, euclidNorm (x j) ≤ j) →
      ∀ y : Site d, euclidNorm y ≤ 3 * n → ∀ s t : ℕ, s < t → t ≤ n →
        c * (Real.sqrt (max (Cg ^ 2 * ∑ j ∈ Ico s t,
              (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 * Real.log (n + 2)) +
            (2 * Cg + 1) * Real.log (n + 2)) ≤
          Cdet * errorBound d (intervalMax x s t) (Real.log (n + 2)) := by
  obtain ⟨D, hD0, hD⟩ := exists_sum_image_le hd
  set A : ℝ := Cg ^ 2 * D with hA
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 < 2 * Cg + 1 := by linarith
  refine ⟨c * (Real.sqrt (A + 1) + (2 * Cg + 1)), by positivity, ?_⟩
  intro x n hn hx y hy s t hst htn
  set L : ℝ := Real.log (n + 2) with hLdef
  have hL1 : 1 ≤ L := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h4 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have h5 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith [this]
    linarith
  have hL0 : 0 ≤ L := by linarith
  set m : ℝ := (intervalMax x s t : ℝ) with hm
  have hm1 : 1 ≤ m := by
    have h := one_le_intervalMax x hst
    rw [hm]
    exact_mod_cast h
  set Λ : ℝ := if d = 2 then L else 1 with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ]
    split_ifs <;> linarith
  have hS : ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ)) ≤ m * (D * Λ) :=
    (sum_Ico_le_intervalMax_mul x s t (g := fun z => (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)))
      (fun z => Real.rpow_nonneg (by linarith [euclidNorm_nonneg (z - y)]) _)).trans
      (mul_le_mul_of_nonneg_left (hD x n (by omega) hx y hy s t htn) (Nat.cast_nonneg _))
  have hmΛ : 1 ≤ m * Λ := by nlinarith
  have hmax : max (Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 ≤
      (A + 1) * (m * Λ) := by
    refine max_le ?_ (by nlinarith)
    calc Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))
        ≤ Cg ^ 2 * (m * (D * Λ)) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
      _ = A * (m * Λ) := by rw [hA]; ring
      _ ≤ (A + 1) * (m * Λ) := by nlinarith
  set u : ℝ := Real.sqrt (m * Λ * L) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hsq : Real.sqrt (max (Cg ^ 2 * ∑ j ∈ Ico s t,
      (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 * L) ≤ Real.sqrt (A + 1) * u := by
    rw [hu, ← Real.sqrt_mul (by linarith)]
    refine Real.sqrt_le_sqrt ?_
    calc _ ≤ (A + 1) * (m * Λ) * L := mul_le_mul_of_nonneg_right hmax hL0
      _ = (A + 1) * (m * Λ * L) := by ring
  rw [errorBound_eq (by linarith) hL0]
  have hsA : 0 ≤ Real.sqrt (A + 1) := Real.sqrt_nonneg _
  calc _ ≤ c * (Real.sqrt (A + 1) * u + (2 * Cg + 1) * L) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith
    _ ≤ c * (Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L) := by
        have : Real.sqrt (A + 1) * u + (2 * Cg + 1) * L ≤
            (Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L) := by
          nlinarith [mul_nonneg hsA hL0, mul_nonneg hB0.le hu0]
        calc _ ≤ c * ((Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L)) :=
              mul_le_mul_of_nonneg_left this (by linarith)
          _ = _ := by ring

/-- One interval–target pair: Freedman's inequality at dyadic brackets, followed by the
deterministic step, bounds the probability that `𝓜^y_t - 𝓜^y_s` exceeds `C e_n(M_{s,t})`. -/
private lemma exists_event_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {ξ : Site d → EuclideanSpace ℝ (Fin d)}
      (_ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) {X : ℕ → Ω → Site d},
      IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ s t : ℕ, ∀ y : Site d, s < t → t ≤ n → euclidNorm y ≤ 3 * n →
          μ {ω | Cdet * errorBound d (intervalMax (fun j => X j ω) s t) (Real.log (n + 2)) <
              |driftDynkin ε ξ (fun z => b (z - y)) X t ω -
                driftDynkin ε ξ (fun z => b (z - y)) X s ω|} ≤
            ENNReal.ofReal (((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) + 1) *
              (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  have hd1 : 1 ≤ d := by omega
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_det_bound hd hCg hc1
  refine ⟨Cdet, hCdet0, ?_⟩
  intro Ω _ μ _ ξ hξ X hX n hn s t y hst htn hy
  obtain ⟨M, hM, hbd, hvar, hae⟩ :=
    ContactDynkin.exists_clamped_translate_drift hd1 hε hξ hX hgrad y
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst.le
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hW : (1 : ℝ) ≤ max (Cg ^ 2 * n) 1 := le_max_right _ _
  have hdy := hc hM (V := bracket Cg y X) (stronglyMeasurable_bracket_succ hX.measurable Cg y)
    (bracket_zero Cg y X) (bracket_mono Cg y X) hvar (b := 2 * Cg + 1) (by linarith) s k
    (fun i _ _ ω => hbd i ω) (W := max (Cg ^ 2 * n) 1) (L := Real.log ((n : ℝ) + 2)) hW hL
    (fun ω => (bracket_sub_le hd1 Cg y X (Nat.le_add_right s k) htn ω).trans (le_max_left _ _))
  refine le_trans (measure_mono_ae ?_) hdy
  filter_upwards [hae, ae_euclidNorm_le_drift hd1 hε hξ hX] with ω hω hx hE
  change _ < _ at hE
  change _ < _
  rw [hω (s + k), hω s]
  refine lt_of_le_of_lt ?_ hE
  rw [bracket_sub Cg y X (Nat.le_add_right s k) ω]
  exact hCdet (fun j => X j ω) n hn hx y hy s (s + k) hst htn

/-- The error term is nonnegative. -/
private lemma errorBound_nonneg (m : ℝ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ errorBound d m L := by
  unfold errorBound
  split_ifs <;> positivity

/-- The arithmetic of the union bound: `(n + 1)² (7 (n + 1))^D · G (n + 1) · 2 e^{-(p + D + 3) L}`
is at most `7^D G 2^{D+4} n^{-p}`. -/
private lemma union_bound_arith {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (D : ℕ) {G : ℝ}
    (hG : 0 ≤ G) :
    (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ D) * ((G * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) ≤
    (7 ^ D * G * 2 ^ (D + 4)) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le
    (K := p + ((D + 3 : ℕ) : ℝ)) (by positivity) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn (D + 3) p
  have h3 : (0 : ℝ) ≤ 7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3) := by positivity
  calc (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ D) * ((G * ((n : ℝ) + 1)) *
        (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))
      = (7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3)) *
          (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        rw [mul_pow]
        ring
    _ ≤ (7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3)) * (2 * (n : ℝ) ^ (-(p + ((D + 3 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * (7 ^ D * G) * (((n : ℝ) + 1) ^ (D + 3) * (n : ℝ) ^ (-(p + ((D + 3 : ℕ) : ℝ)))) := by
        ring
    _ ≤ 2 * (7 ^ D * G) * (2 ^ (D + 3) * (n : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (7 ^ D * G * 2 ^ (D + 4)) * (n : ℝ) ^ (-p) := by ring

/-- `eq:interval-mart`: under the one-step bound `|b(x + e) - b(x)| ≤ C_g (1 + |x|)^{1-d}`, with
probability at least `1 - Cn^{-p}`, `|𝓜^y_t - 𝓜^y_s| ≤ C e_n(M_{s,t})` for all `0 ≤ s < t ≤ n` and
all `|y| ≤ 3n`. -/
private theorem exists_interval_mart_drift (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ξ : Site d → EuclideanSpace ℝ (Fin d)} (_ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
      {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ∃ s t : ℕ, ∃ y : Site d, s < t ∧ t ≤ n ∧ euclidNorm y ≤ 3 * n ∧
          C * (if d = 2 then
              Real.sqrt (intervalMax (fun j => X j ω) s t) * Real.log (n + 2) + Real.log (n + 2)
            else Real.sqrt (intervalMax (fun j => X j ω) s t * Real.log (n + 2)) +
              Real.log (n + 2)) <
            |driftDynkin ε ξ (fun z => b (z - y)) X t ω -
              driftDynkin ε ξ (fun z => b (z - y)) X s ω|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_event_bound hd hε hgrad
    (K := p + ((d + 3 : ℕ) : ℝ)) (by positivity)
  refine ⟨Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4), by positivity, ?_⟩
  intro Ω _ μ _ ξ hξ X hX n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 2) := (Real.log_pos (by linarith)).le
  set P : Finset (ℕ × ℕ) := ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun q => q.1 < q.2)
    with hP
  set Y : Finset (Site d) := ballFinset d (3 * (n : ℝ)) with hY
  set B : ℕ × ℕ → Site d → Set Ω := fun q y =>
    {ω | Cdet * errorBound d (intervalMax (fun j => X j ω) q.1 q.2) (Real.log ((n : ℝ) + 2)) <
      |driftDynkin ε ξ (fun z => b (z - y)) X q.2 ω - driftDynkin ε ξ (fun z => b (z - y)) X q.1 ω|}
    with hB
  have hsub : {ω | ∃ s t : ℕ, ∃ y : Site d, s < t ∧ t ≤ n ∧ euclidNorm y ≤ 3 * n ∧
      (Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) * (if d = 2 then
              Real.sqrt (intervalMax (fun j => X j ω) s t) * Real.log (n + 2) + Real.log (n + 2)
            else Real.sqrt (intervalMax (fun j => X j ω) s t * Real.log (n + 2)) +
              Real.log (n + 2)) <
            |driftDynkin ε ξ (fun z => b (z - y)) X t ω -
              driftDynkin ε ξ (fun z => b (z - y)) X s ω|} ⊆
      ⋃ q ∈ P, ⋃ y ∈ Y, B q y := by
    rintro ω ⟨s, t, y, hst, htn, hy, hlt⟩
    simp only [Set.mem_iUnion]
    refine ⟨(s, t), ?_, y, ?_, ?_⟩
    · simp only [hP, mem_filter, mem_product, mem_range]
      omega
    · rw [hY, mem_ballFinset_iff]
      exact hy
    · change Cdet * errorBound d _ _ < _
      have he := errorBound_nonneg (d := d) ((intervalMax (fun j => X j ω) s t : ℕ) : ℝ) hL0
      have hlt' : (Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) *
          errorBound d (intervalMax (fun j => X j ω) s t) (Real.log ((n : ℝ) + 2)) <
            |driftDynkin ε ξ (fun z => b (z - y)) X t ω -
              driftDynkin ε ξ (fun z => b (z - y)) X s ω| := hlt
      have h7 : 0 ≤ 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4) := by positivity
      nlinarith [mul_nonneg h7 he]
  have hbound : ∀ q ∈ P, ∀ y ∈ Y, μ (B q y) ≤ ENNReal.ofReal (((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((d + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) := by
    intro q hq y hy
    have hq' := mem_filter.mp hq
    have h2 : q.2 ≤ n := by
      have := mem_range.mp (mem_product.mp hq'.1).2
      omega
    have hyn : euclidNorm y ≤ 3 * n := mem_ballFinset_iff.mp hy
    refine (hCdet hξ hX n hn q.1 q.2 y hq'.2 h2 hyn).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (clog_ceil_add_one_le Cg n) (by positivity)
  have hPcard : (P.card : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h1 : P.card ≤ (n + 1) * (n + 1) := by
      refine (card_filter_le _ _).trans ?_
      simp
    exact_mod_cast h1.trans_eq (by ring)
  have hYcard : (Y.card : ℝ) ≤ (7 * ((n : ℝ) + 1)) ^ d :=
    (card_ballFinset_le d (R := 3 * (n : ℝ)) (by positivity)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) d)
  set a : ℝ := ((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
    (2 * Real.exp (-((p + ((d + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono hsub).trans ?_
  calc μ (⋃ q ∈ P, ⋃ y ∈ Y, B q y) ≤ ∑ q ∈ P, μ (⋃ y ∈ Y, B q y) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ P, ∑ y ∈ Y, μ (B q y) := sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ P, ∑ _y ∈ Y, ENNReal.ofReal a :=
        sum_le_sum fun q hq => sum_le_sum fun y hy => hbound q hq y hy
    _ = ENNReal.ofReal ((P.card : ℝ) * ((Y.card : ℝ) * a)) := by
        simp only [sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (p := (P.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_mul (p := (Y.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) * (n : ℝ) ^ (-p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (P.card : ℝ) * ((Y.card : ℝ) * a) ≤
            (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ d) * a := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hPcard hYcard (Nat.cast_nonneg _) (by positivity)) ha0
        have h2 := union_bound_arith hp.le (by omega : 1 ≤ n) d (G := Cg ^ 2 + 3) (by positivity)
        have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        nlinarith [mul_nonneg hCdet0.le h3]

end IntervalMartingale

section SourcePacking

open MeasureTheory LatticeProb CERW CERW.Support.Law CERW.Generic.Kernel CERW.Support.Occupation
open CERW.Support.LocalTime CERW.Generic.Lattice

variable {d : ℕ}

/-- Each coordinate of the central difference is at most `C (1 + |z|)^{1-d}` once every one-step
increment is at most `Cg (1 + |z|)^{1-d}` and `Cg ≤ C`. -/
private lemma abs_centralDiff_coord_le_of_step {b : Site d → ℝ} {Cg C : ℝ} (hCgC : Cg ≤ C)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) (z : Site d) (i : Fin d) :
    ‖(centralDiff b z) i‖ ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
  have hX : 0 ≤ (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
  have h1 : |b (z + unit i) - b z| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    (hgrad z (unit i) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)).trans
      (mul_le_mul_of_nonneg_right hCgC hX)
  have h2 : |b (z - unit i) - b z| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
    have h : |b (z + -unit i) - b z| ≤ Cg * (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
      hgrad z (-unit i) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)
    rw [sub_eq_add_neg z (unit i)]
    exact h.trans (mul_le_mul_of_nonneg_right hCgC hX)
  have h2sym : |b z - b (z - unit i)| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
    rw [abs_sub_comm]
    exact h2
  have htri : |b (z + unit i) - b (z - unit i)| ≤
      2 * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
    have h := abs_sub_le (b (z + unit i)) (b z) (b (z - unit i))
    linarith
  have hcoord : (centralDiff b z) i = (b (z + unit i) - b (z - unit i)) / 2 := by
    simp only [centralDiff, PiLp.toLp_apply]
  rw [hcoord, Real.norm_eq_abs, abs_div]
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  rw [h2abs]
  linarith

/-- The Euclidean norm of the central difference is at most `√d (C (1 + |z|)^{1-d})` once every
coordinate is. -/
private lemma norm_centralDiff_le_of_step {b : Site d → ℝ} {Cg C : ℝ} (hCnonneg : 0 ≤ C)
    (hCgC : Cg ≤ C)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) (z : Site d) :
    ‖centralDiff b z‖ ≤ Real.sqrt d * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
  have hX : 0 ≤ (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
  have hc : 0 ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := mul_nonneg hCnonneg hX
  have hcoord := abs_centralDiff_coord_le_of_step hCgC hgrad z
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i : Fin d, ‖(centralDiff b z) i‖ ^ 2)
      ≤ √(∑ _i : Fin d, (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
    _ = √((d : ℝ) * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Real.sqrt d * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hc]

/-- For a kernel with the one-step bound, `|Σ_{x ∈ F} ξ(x) · Db(x - y)| ≤ C_d |F|^{1/d}` for
every finite `F`, every `y` and every field `ξ` with `|ξ(x)| ≤ Λ`. -/
private theorem exists_abs_sum_inner_drift_centralDiff_le (hd : 2 ≤ d) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (Λ : ℝ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)), (∀ x, ‖ξ x‖ ≤ Λ) →
      ∀ (F : Finset (Site d)) (y : Site d),
        |∑ x ∈ F, inner ℝ (ξ x) (centralDiff b (x - y))| ≤ Cd * (F.card : ℝ) ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, hC₀pos, hC₀⟩ := sum_rpow_one_sub_le_card_rpow (d := d) hd1
  set Cgmax : ℝ := max Cg 0 with hCgmax
  have hCg_le : Cg ≤ Cgmax := by rw [hCgmax]; exact le_max_left _ _
  have hCgmax_nonneg : 0 ≤ Cgmax := by rw [hCgmax]; exact le_max_right _ _
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  refine ⟨Λ' * (Real.sqrt d * Cgmax * C₀), ?_, ?_⟩
  · exact mul_nonneg hΛ'0 (mul_nonneg (mul_nonneg (Real.sqrt_nonneg d) hCgmax_nonneg) hC₀pos.le)
  · intro ξ hξ F y
    have hterm : ∀ x ∈ F,
        |inner ℝ (ξ x) (centralDiff b (x - y))| ≤
          Λ' * (Real.sqrt d * Cgmax) * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by
      intro x _
      have hnorm := norm_centralDiff_le_of_step hCgmax_nonneg hCg_le hgrad (x - y)
      calc |inner ℝ (ξ x) (centralDiff b (x - y))|
          ≤ ‖ξ x‖ * ‖centralDiff b (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ Λ' * (Real.sqrt d * (Cgmax * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)))) :=
            mul_le_mul ((hξ x).trans (le_max_left _ _)) hnorm (norm_nonneg _) hΛ'0
        _ = Λ' * (Real.sqrt d * Cgmax) * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by ring
    calc |∑ x ∈ F, inner ℝ (ξ x) (centralDiff b (x - y))|
        ≤ ∑ x ∈ F, |inner ℝ (ξ x) (centralDiff b (x - y))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ F, Λ' * (Real.sqrt d * Cgmax) * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = Λ' * (Real.sqrt d * Cgmax) * ∑ x ∈ F, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ Λ' * (Real.sqrt d * Cgmax) * (C₀ * (F.card : ℝ) ^ ((1 : ℝ) / d)) :=
          mul_le_mul_of_nonneg_left (hC₀ F y)
            (mul_nonneg hΛ'0 (mul_nonneg (Real.sqrt_nonneg d) hCgmax_nonneg))
      _ = Λ' * (Real.sqrt d * Cgmax * C₀) * (F.card : ℝ) ^ ((1 : ℝ) / d) := by ring

end SourcePacking

section SourceSum

open MeasureTheory LatticeProb CERW CERW.Support.Law CERW.Generic.Kernel CERW.Support.Occupation
open CERW.Support.LocalTime CERW.Generic.Lattice

variable {d : ℕ}

/-- For a measurable field `g` with `‖g‖ ≤ Λ`, `v ↦ ⟪g v, K(v - z)⟫` is integrable on a measurable
set of finite volume. -/
private lemma integrableOn_inner_field_newtonField (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hgb : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (z : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (g v) (newtonField (v - z))) D volume := by
  have hbase : IntegrableOn (fun v => ‖v - z‖ ^ (1 - (d : ℝ))) D volume :=
    (integrableOn_and_setIntegral_le (d := d) (by omega : 1 ≤ d) hD hDfin z).1
  have hmeas : Measurable
      (fun v : EuclideanSpace ℝ (Fin d) => inner ℝ (g v) (newtonField (v - z))) :=
    hg.inner (measurable_newtonField.comp (measurable_id.sub measurable_const))
  refine (hbase.const_mul Λ).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with v
  calc ‖inner ℝ (g v) (newtonField (v - z))‖ ≤ ‖g v‖ * ‖newtonField (v - z)‖ :=
        norm_inner_le_norm _ _
    _ = ‖g v‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by rw [norm_newtonField hd]
    _ ≤ Λ * ‖v - z‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (hgb v) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The source sum of `eq:dynkin` for the walk with drift field `ξ` differs from the norm potential
by `O(ε log(R' + 2))`: the gradient is replaced by the Newtonian field, the kernel value by its cell
integral, and the lattice drift `ξ(x)` by the gradient `∇Ψ(v)` on the cell (`lem:cell`). -/
private theorem exists_abs_source_sum_sub_normPotential_le (hd : 2 ≤ d) {b : Site d → ℝ}
    {Ca R Cg : ℝ}
    (hR : 1 ≤ R)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hcell : CERW.Support.Statements.cell_gradient) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ) (y : Site d) (R' : ℝ), 1 ≤ R' →
      (∀ x ∈ departureRange X n, euclidNorm (x - y) ≤ R') →
        |ε * ∑ x ∈ departureRange X n, inner ℝ (ξ x) (centralDiff b (x - y)) -
            normPotential d ε Ψ (cellSet X n) (toSpace y)| ≤ C * ε * Real.log (R' + 2) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Ca', hCa'_nonneg, hCa⟩ :=
    exists_sum_norm_centralDiff_sub_newtonField_le (d := d) hd hR hgradA hgrad
  obtain ⟨Cb, hCb_nonneg, hCb⟩ := exists_sum_abs_newtonField_sub_setIntegral_le (d := d) hd
  obtain ⟨Cc, hCc0, hcellC⟩ := hcell hd
  obtain ⟨m, hmfin, hlap⟩ := exists_isDistribLaplacian hΨ
  obtain ⟨Kgen, hKgen, hgrowth⟩ := exists_measure_ball_le hd1
  have hΛ : 0 ≤ normMax Ψ := normMax_nonneg_of_isNorm hΨ
  set Λ := normMax Ψ with hΛdef
  obtain ⟨Cdir, hCdir0, hCdir⟩ := exists_sum_abs_setIntegral_sub_gradient_le hd hΨ hmfin
    (Cc := Cc) (Kg := Kgen * Λ) hCc0.le (mul_nonneg hKgen hΛ)
  have hω := unitBallVolume_pos d
  have hcoef : 0 ≤ 2 / unitBallVolume d := le_of_lt (div_pos (by norm_num) hω)
  refine ⟨Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir), ?_, ?_⟩
  · positivity
  · intro ε hε ξ hξ hξ0 X n y R' hR' hcellR
    have hξΛ := norm_drift_le hΨ hξ hξ0
    have hξs := isSubgradient_drift hΨ hξ hξ0
    have hcellξ : ∀ x : Site d, ENNReal.ofReal (∫ v in cell x, ‖gradient Ψ v - ξ x‖) ≤
        ENNReal.ofReal Cc * m (Metric.ball (toSpace x) (6 * Real.sqrt d)) :=
      hcellC Ψ hΨ ξ hξ hξ0 m hmfin hlap
    set S0 : ℝ := ∑ x ∈ departureRange X n, inner ℝ (ξ x) (centralDiff b (x - y)) with hS0
    set S1 : ℝ := ∑ x ∈ departureRange X n,
      inner ℝ (ξ x) (newtonField (toSpace x - toSpace y)) with hS1
    set S2 : ℝ := ∑ x ∈ departureRange X n,
      ∫ v in cell x, inner ℝ (ξ x) (newtonField (v - toSpace y)) with hS2
    set S3 : ℝ := ∑ x ∈ departureRange X n,
      ∫ v in cell x, inner ℝ (gradient Ψ v) (newtonField (v - toSpace y)) with hS3
    have hcellmeas : ∀ x : Site d, MeasurableSet (cell x) := measurableSet_cell
    have hcellfin : ∀ x : Site d, volume (cell x) ≠ ⊤ := fun x => by
      rw [volume_cell]
      exact ENNReal.one_ne_top
    have hint_xi : ∀ x : Site d, IntegrableOn
        (fun v => inner ℝ (ξ x) (newtonField (v - toSpace y))) (cell x) volume := fun x =>
      integrableOn_inner_field_newtonField hd (g := fun _ => ξ x) measurable_const
        (fun _ => hξΛ x) (hcellmeas x) (hcellfin x) (toSpace y)
    have hint_grad : ∀ x : Site d, IntegrableOn
        (fun v => inner ℝ (gradient Ψ v) (newtonField (v - toSpace y))) (cell x) volume :=
      fun x => integrableOn_inner_field_newtonField hd (measurable_gradient_field Ψ)
        (norm_gradient_le_normMax hΨ) (hcellmeas x) (hcellfin x) (toSpace y)
    have h1 : |S0 - (2 / unitBallVolume d) * S1| ≤ Λ * Ca' * Real.log (R' + 2) := by
      have hsum := hCa (departureRange X n) y R' hR' hcellR
      have hrew : S0 - (2 / unitBallVolume d) * S1 =
          ∑ x ∈ departureRange X n, inner ℝ (ξ x)
            (centralDiff b (x - y) -
              (2 / unitBallVolume d) • newtonField (toSpace (x - y))) := by
        rw [hS0, hS1, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [inner_sub_right, inner_smul_right, toSpace_sub]
      rw [hrew]
      calc |∑ x ∈ departureRange X n, inner ℝ (ξ x)
              (centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y)))|
          ≤ ∑ x ∈ departureRange X n, ‖inner ℝ (ξ x)
              (centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y)))‖ :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x ∈ departureRange X n, Λ *
              ‖centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ := by
            apply Finset.sum_le_sum
            intro x _
            calc ‖inner ℝ (ξ x)
                    (centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace (x - y)))‖
                ≤ ‖ξ x‖ * ‖centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ :=
                  norm_inner_le_norm _ _
              _ ≤ Λ * ‖centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ :=
                  mul_le_mul_of_nonneg_right (hξΛ x) (norm_nonneg _)
        _ = Λ * ∑ x ∈ departureRange X n,
              ‖centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ := by
            rw [Finset.mul_sum]
        _ ≤ Λ * (Ca' * Real.log (R' + 2)) := mul_le_mul_of_nonneg_left hsum hΛ
        _ = Λ * Ca' * Real.log (R' + 2) := by ring
    have h2 : |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| ≤
        (2 / unitBallVolume d) * ((Λ + 1) * Cb) * Real.log (R' + 2) := by
      have hΛ1 : 0 < Λ + 1 := by linarith
      have hsum := hCb (departureRange X n) (fun x => (Λ + 1)⁻¹ • ξ x) y R' hR'
        (fun x => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ1)]
          calc (Λ + 1)⁻¹ * ‖ξ x‖ ≤ (Λ + 1)⁻¹ * (Λ + 1) :=
                mul_le_mul_of_nonneg_left ((hξΛ x).trans (by linarith)) (inv_pos.mpr hΛ1).le
            _ = 1 := inv_mul_cancel₀ hΛ1.ne')
        hcellR
      have hterm : ∀ x ∈ departureRange X n,
          |inner ℝ (ξ x) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ (ξ x) (newtonField (v - toSpace y))| =
            (Λ + 1) * |inner ℝ ((Λ + 1)⁻¹ • ξ x) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ ((Λ + 1)⁻¹ • ξ x) (newtonField (v - toSpace y))| := by
        intro x _
        simp_rw [inner_smul_left, RCLike.conj_to_real]
        rw [integral_const_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hΛ1), ← mul_assoc,
          mul_inv_cancel₀ hΛ1.ne', one_mul]
      have hrew : S1 - S2 =
          ∑ x ∈ departureRange X n,
            (inner ℝ (ξ x) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ (ξ x) (newtonField (v - toSpace y))) := by
        rw [hS1, hS2, ← Finset.sum_sub_distrib]
      have htri : |S1 - S2| ≤
          (Λ + 1) * ∑ x ∈ departureRange X n,
            |inner ℝ ((Λ + 1)⁻¹ • ξ x) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ ((Λ + 1)⁻¹ • ξ x) (newtonField (v - toSpace y))| := by
        rw [hrew, Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl hterm
      calc |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2|
          = (2 / unitBallVolume d) * |S1 - S2| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hcoef]
        _ ≤ (2 / unitBallVolume d) * ((Λ + 1) * (Cb * Real.log (R' + 2))) :=
            mul_le_mul_of_nonneg_left (htri.trans (mul_le_mul_of_nonneg_left hsum hΛ1.le)) hcoef
        _ = (2 / unitBallVolume d) * ((Λ + 1) * Cb) * Real.log (R' + 2) := by ring
    have h3 : |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| ≤
        (2 / unitBallVolume d) * Cdir * Real.log (R' + 2) := by
      have hsum := hCdir ξ hξΛ hcellξ (departureRange X n) y R' hR' hcellR
        (fun {R} hR => by
          simpa [hΛdef] using hgrowth hΨ hmfin hlap (hξs y) hR)
      have hrew : S2 - S3 =
          ∑ x ∈ departureRange X n,
            ∫ v in cell x,
              inner ℝ (ξ x - gradient Ψ v) (newtonField (v - toSpace y)) := by
        rw [hS2, hS3, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← integral_sub (hint_xi x) (hint_grad x)]
        exact setIntegral_congr_fun (hcellmeas x) (fun v _ => by rw [inner_sub_left])
      have htri : |S2 - S3| ≤
          ∑ x ∈ departureRange X n,
            |∫ v in cell x,
              inner ℝ (ξ x - gradient Ψ v) (newtonField (v - toSpace y))| := by
        rw [hrew]
        exact Finset.abs_sum_le_sum_abs _ _
      calc |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3|
          = (2 / unitBallVolume d) * |S2 - S3| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hcoef]
        _ ≤ (2 / unitBallVolume d) * (Cdir * Real.log (R' + 2)) :=
            mul_le_mul_of_nonneg_left (htri.trans hsum) hcoef
        _ = (2 / unitBallVolume d) * Cdir * Real.log (R' + 2) := by ring
    have hmain : |S0 - (2 / unitBallVolume d) * S3| ≤
        (Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir)) * Real.log (R' + 2) := by
      have htri : |S0 - (2 / unitBallVolume d) * S3| ≤
          |S0 - (2 / unitBallVolume d) * S1| +
            |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| +
              |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| := by
        have heq : S0 - (2 / unitBallVolume d) * S3 =
            (S0 - (2 / unitBallVolume d) * S1) +
              ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2) +
                ((2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3) := by ring
        rw [heq]
        calc |(S0 - (2 / unitBallVolume d) * S1) +
                ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2) +
                  ((2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3)|
            ≤ |(S0 - (2 / unitBallVolume d) * S1) +
                  ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2)| +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| :=
              abs_add_le _ _
          _ ≤ (|S0 - (2 / unitBallVolume d) * S1| +
                  |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2|) +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| :=
              add_le_add (abs_add_le _ _) le_rfl
          _ = _ := by ring
      calc |S0 - (2 / unitBallVolume d) * S3|
          ≤ |S0 - (2 / unitBallVolume d) * S1| +
              |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| := htri
        _ ≤ Λ * Ca' * Real.log (R' + 2) +
              (2 / unitBallVolume d) * ((Λ + 1) * Cb) * Real.log (R' + 2) +
                (2 / unitBallVolume d) * Cdir * Real.log (R' + 2) :=
            add_le_add (add_le_add h1 h2) h3
        _ = (Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir)) * Real.log (R' + 2) := by
            ring
    have hpot : normPotential d ε Ψ (cellSet X n) (toSpace y) =
        ε * ((2 / unitBallVolume d) * S3) := by
      have hD3 : ∫ v in cellSet X n, inner ℝ (gradient Ψ v) (newtonField (v - toSpace y))
          = S3 := by
        rw [hS3, cellSet]
        exact integral_biUnion_finset (departureRange X n) (fun x _ => hcellmeas x)
          (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => hint_grad x)
      have hcongr : ∫ v in cellSet X n,
            inner ℝ (gradient Ψ v) (v - toSpace y) / ‖v - toSpace y‖ ^ d
          = ∫ v in cellSet X n,
            inner ℝ (gradient Ψ v) (newtonField (v - toSpace y)) := by
        exact setIntegral_congr_fun (measurableSet_cellSet X n)
          (fun v _ => (inner_newtonField (gradient Ψ v) (v - toSpace y)).symm)
      rw [normPotential, hcongr, hD3]
      ring
    calc |ε * S0 - normPotential d ε Ψ (cellSet X n) (toSpace y)|
        = |ε * S0 - ε * ((2 / unitBallVolume d) * S3)| := by rw [hpot]
      _ = ε * |S0 - (2 / unitBallVolume d) * S3| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hε]
      _ ≤ ε * ((Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir)) *
            Real.log (R' + 2)) := mul_le_mul_of_nonneg_left hmain hε
      _ = (Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir)) * ε *
            Real.log (R' + 2) := by ring

end SourceSum

section Assembly

open CERW.Support.Statements

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift
open CERW.Support.Occupation CERW.Support.LocalTime

/-- A logarithm of a positive number at most `4n + 2` is at most `2 log (n + 2)`. -/
private lemma log_le_two_mul_log {a : ℝ} (n : ℕ) (ha : 0 < a) (h : a ≤ 4 * (n : ℝ) + 2) :
    Real.log a ≤ 2 * Real.log ((n : ℝ) + 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hle : a ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
  have := Real.log_le_log ha hle
  rwa [Real.log_pow, Nat.cast_ofNat] at this

/-- The Euclidean norm of a difference of sites is at most the sum of the norms. -/
private lemma euclidNorm_sub_le_add {d : ℕ} (x y : Site d) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by
  have h := CERW.Support.Occupation.euclidNorm_add_le x (-y)
  rwa [← sub_eq_add_neg, CERW.Generic.Lattice.euclidNorm_neg] at h

/-- The error scale `e_n(m) = B √m + L` with `B = L` for `d = 2` and `B = √L` for `d ≥ 3`. -/
private lemma error_scale_eq {m L : ℝ} (d : ℕ) (hm : 0 ≤ m) :
    (if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L) =
      (if d = 2 then L else Real.sqrt L) * Real.sqrt m + L := by
  by_cases hd : d = 2
  · simp only [hd, if_true]
    ring
  · simp only [hd, if_false]
    rw [Real.sqrt_mul hm]
    ring

/-- The scale `B` of the error, and the scale `λ_n = B²` that dominates `L`. -/
private lemma error_scale_facts {L : ℝ} (d : ℕ) (hL : 1 ≤ L) :
    0 ≤ (if d = 2 then L else Real.sqrt L) ∧
      (if d = 2 then L else Real.sqrt L) ^ 2 = (if d = 2 then L ^ 2 else L) ∧
      L ≤ (if d = 2 then L ^ 2 else L) := by
  split_ifs with hd
  · exact ⟨by linarith, rfl, by nlinarith⟩
  · exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (by linarith), le_rfl⟩

/-- Some site visited during `[s, t)` attains the interval maximum. -/
private lemma exists_visited_eq_intervalMax {d : ℕ} (x : ℕ → Site d) {s t : ℕ} (hst : s < t) :
    ∃ j, s ≤ j ∧ j < t ∧ intervalLocalTime x s t (x j) = intervalMax x s t := by
  have hne : ((Finset.Ico s t).image x).Nonempty := (Finset.nonempty_Ico.mpr hst).image x
  obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup _ hne (intervalLocalTime x s t)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨j, (Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2, hsup.symm⟩

/-- The pathwise bound of `eq:interval` on one interval: the interval Dynkin decomposition, the
packing bound on the fresh sites and the martingale bound give `M ≤ a + B' √M`, which
Young's inequality absorbs. -/
private lemma interval_bound_drift {d : ℕ} {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) {CP Cb CI Bn lam ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ0 : ξ 0 = 0)
    (hCP0 : 0 ≤ CP) (hCb0 : 0 ≤ Cb) (hCI0 : 0 ≤ CI) (hε : 0 ≤ ε) (hBn : 0 ≤ Bn)
    (hBsq : Bn ^ 2 = lam)
    (hCP : ∀ (F : Finset (Site d)) (y : Site d),
      |∑ x ∈ F, inner ℝ (ξ x) (centralDiff b (x - y))| ≤
        CP * (F.card : ℝ) ^ ((1 : ℝ) / d))
    (hCb : ∀ x : Site d, |b x| ≤ Cb * Real.log (euclidNorm x + 2))
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0)
    (hnorm : ∀ j : ℕ, euclidNorm (X j ω) ≤ j) {n : ℕ} (hn : 2 ≤ n)
    (hLlam : Real.log ((n : ℝ) + 2) ≤ lam)
    (hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
      |driftDynkin ε ξ (fun z => b (z - y)) X t ω - driftDynkin ε ξ (fun z => b (z - y)) X s ω| ≤
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)))
    (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    (intervalMax (fun j => X j ω) s t : ℝ) ≤
      (2 * CP + 1) * ε * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) +
        (8 * Cb + 2 * CI + CI ^ 2) * lam := by
  obtain ⟨j, -, hjt, hjmax⟩ := exists_visited_eq_intervalMax (fun j => X j ω) hst
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htR : (t : ℝ) ≤ n := by exact_mod_cast htn
  have hsR : (s : ℝ) ≤ n := by exact_mod_cast (hst.le.trans htn)
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast (hjt.le.trans htn)
  have hL1 := one_le_log_add_two hn
  have hyn : euclidNorm (X j ω) ≤ n := (hnorm j).trans hjR
  have hdyn := intervalLocalTime_eq_driftDynkin hb ε hξ0 X ω h0 hst.le (X j ω)
  have hM : (intervalLocalTime (fun j => X j ω) s t (X j ω) : ℝ) =
      (intervalMax (fun j => X j ω) s t : ℝ) := by exact_mod_cast hjmax
  have hb1 : |b (X t ω - X j ω)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X t ω - X j ω)]) ?_
    linarith [euclidNorm_sub_le_add (X t ω) (X j ω), hnorm t]
  have hb2 : |b (X s ω - X j ω)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X s ω - X j ω)]) ?_
    linarith [euclidNorm_sub_le_add (X s ω) (X j ω), hnorm s]
  have hsum := hCP (departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s)
    (X j ω)
  rw [card_departureRange_sdiff _ hst.le] at hsum
  have hk0 : 0 ≤ (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  generalize (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) = k at hsum hk0 ⊢
  have hmt := hmart s t (X j ω) hst htn (by linarith)
  have hεS := mul_le_mul_of_nonneg_left hsum hε
  have hεS' := mul_le_mul_of_nonneg_left (le_abs_self
    (∑ z ∈ departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s,
      inner ℝ (ξ z) (centralDiff b (z - X j ω)))) hε
  rw [hM] at hdyn
  have key : (intervalMax (fun j => X j ω) s t : ℝ) ≤
      Cb * (2 * Real.log ((n : ℝ) + 2)) + Cb * (2 * Real.log ((n : ℝ) + 2)) +
        ε * (CP * k) +
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) +
          Real.log ((n : ℝ) + 2)) := by
    linarith [le_abs_self (b (X t ω - X j ω)), neg_le_abs (b (X s ω - X j ω)),
      neg_le_abs (driftDynkin ε ξ (fun z => b (z - X j ω)) X t ω -
        driftDynkin ε ξ (fun z => b (z - X j ω)) X s ω)]
  have ha0 : 0 ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) + Cb * (2 * Real.log ((n : ℝ) + 2)) +
      ε * (CP * k) +
        CI * Real.log ((n : ℝ) + 2) := by positivity
  have hyoung := CERW.Generic.Young.le_two_mul_add_sq_of_le_add_mul_sqrt (Nat.cast_nonneg _)
    ha0 (mul_nonneg hCI0 hBn) (by linarith [key])
  have hBs : (CI * Bn) ^ 2 = CI ^ 2 * lam := by rw [mul_pow, hBsq]
  nlinarith [mul_le_mul_of_nonneg_left hLlam hCb0, mul_le_mul_of_nonneg_left hLlam hCI0,
    mul_nonneg hε hk0]

/-- Combining the five error terms of the approximate local-time bound: if each term is bounded by
its error scale, then their sum is bounded by the summed scale. -/
private lemma approx_error_combination {Cb CS CM CI Bn ε m logn A B C D E : ℝ}
    (hCb0 : 0 ≤ Cb) (hCS0 : 0 ≤ CS) (hCM0 : 0 ≤ CM)
    (hε : 0 ≤ ε) (hBn : 0 ≤ Bn)
    (hA : |A| ≤ Cb * (2 * logn)) (hB : |B| ≤ Cb * (2 * logn))
    (hC : |C| ≤ CS * ε * (2 * logn)) (hD : |D| ≤ CM * ε * (2 * logn))
    (hE : |E| ≤ CI * (Bn * Real.sqrt m + logn)) :
    |A + B + C + D + E| ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε + CI) * (Bn * Real.sqrt m + logn) := by
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have hC' := abs_le.mp hC
  have hD' := abs_le.mp hD
  have hE' := abs_le.mp hE
  have hK0 : 0 ≤ 4 * Cb + 2 * CS * ε + 2 * CM * ε := by
    have h1 := mul_nonneg hCS0 hε
    have h2 := mul_nonneg hCM0 hε
    linarith
  have hterm : 0 ≤ (4 * Cb + 2 * CS * ε + 2 * CM * ε) * Bn * Real.sqrt m :=
    mul_nonneg (mul_nonneg hK0 hBn) (Real.sqrt_nonneg m)
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> nlinarith [hterm]

/-- The pathwise bound of `eq:approx` at a real point `y`, `|y| ≤ 2n`: at the site `z` of the cell
of `y`, the Dynkin decomposition of `ℓ_n(z)`, the source-sum comparison, the cell modulus and the
martingale bound. -/
private lemma approx_bound_drift {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) {Cb CS CM CI Bn ε : ℝ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ0 : ξ 0 = 0)
    (hCb0 : 0 ≤ Cb) (hCS0 : 0 ≤ CS) (hCM0 : 0 ≤ CM) (hCI0 : 0 ≤ CI) (hε : 0 ≤ ε)
    (hBn : 0 ≤ Bn)
    (hCb : ∀ x : Site d, |b x| ≤ Cb * Real.log (euclidNorm x + 2))
    (hCS : ∀ (u : ℕ → Site d) (m : ℕ) (w : Site d) (R' : ℝ), 1 ≤ R' →
      (∀ x ∈ departureRange u m, euclidNorm (x - w) ≤ R') →
        |ε * ∑ x ∈ departureRange u m, inner ℝ (ξ x) (centralDiff b (x - w)) -
            normPotential d ε Ψ (cellSet u m) (toSpace w)| ≤ CS * ε * Real.log (R' + 2))
    (hCM : ∀ R : ℝ, 1 ≤ R → ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
      D ⊆ Metric.ball 0 R → ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε Ψ D y - normPotential d ε Ψ D z| ≤ CM * ε * Real.log (R + 2))
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0)
    (hnorm : ∀ j : ℕ, euclidNorm (X j ω) ≤ j) {n : ℕ} (hn : 2 ≤ n) (hsq : Real.sqrt d ≤ n)
    (hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
      |driftDynkin ε ξ (fun z => b (z - y)) X t ω - driftDynkin ε ξ (fun z => b (z - y)) X s ω| ≤
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)))
    (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 2 * n) :
    |cellLocalTime (fun j => X j ω) n y - normPotential d ε Ψ (cellSet (fun j => X j ω) n) y| ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε + CI) *
        (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 := one_le_log_add_two hn
  have hyz : ‖y - toSpace (cellCenter y)‖ ≤ Real.sqrt d / 2 :=
    CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  have hznorm : euclidNorm (cellCenter y) ≤ 3 * n := by
    have h := norm_le_norm_add_norm_sub' (toSpace (cellCenter y)) y
    rw [norm_toSpace, norm_sub_rev] at h
    linarith
  have hH : CERW.maxRadius (fun j => X j ω) n ≤ n := by
    apply Finset.sup'_le
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (hnorm j).trans (by exact_mod_cast hjn)
  have hcellSet : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball (by omega) (fun j => X j ω) n).trans
      (Metric.ball_subset_ball (by linarith))
  have hdyn := ContactDynkin.localTime_eq_driftDynkin hb ε ξ hξ0 X ω h0 n (cellCenter y)
  have hb1 : |b (X n ω - cellCenter y)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X n ω - cellCenter y)]) ?_
    linarith [euclidNorm_sub_le_add (X n ω) (cellCenter y), hnorm n]
  have hb2 : |b (-cellCenter y)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    rw [CERW.Generic.Lattice.euclidNorm_neg]
    exact log_le_two_mul_log n (by linarith [euclidNorm_nonneg (cellCenter y)]) (by linarith)
  have hsrc := hCS (fun j => X j ω) n (cellCenter y) (4 * n) (by linarith) (by
    intro w hw
    rw [departureRange] at hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
    linarith [euclidNorm_sub_le_add (X j ω) (cellCenter y), hnorm j])
  have hmod := hCM ((n : ℝ) + Real.sqrt d) (by linarith [Real.sqrt_nonneg (d : ℝ)])
    (cellSet (fun j => X j ω) n) (CERW.Support.Occupation.measurableSet_cellSet _ _) hcellSet
    y (toSpace (cellCenter y)) (by linarith [Real.sqrt_nonneg (d : ℝ)])
    (by linarith [Real.sqrt_nonneg (d : ℝ)])
  have hmt := hmart 0 n (cellCenter y) (by omega) le_rfl hznorm
  rw [driftDynkin_zero, sub_zero] at hmt
  have hmono : Real.sqrt (intervalMax (fun j => X j ω) 0 n) ≤
      Real.sqrt (maxLocalTime (fun j => X j ω) n) :=
    Real.sqrt_le_sqrt (Nat.cast_le.mpr
      (CERW.Support.Occupation.intervalMax_le_maxLocalTime _ le_rfl))
  have hmt' : |driftDynkin ε ξ (fun z => b (z - cellCenter y)) X n ω| ≤
      CI * (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) :=
    hmt.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hmono hBn) le_rfl) hCI0)
  have hlog1 : Real.log (4 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) :=
    log_le_two_mul_log n (by linarith) le_rfl
  have hlog2 : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤ 2 * Real.log ((n : ℝ) + 2) :=
    log_le_two_mul_log n (by linarith [Real.sqrt_nonneg (d : ℝ)]) (by linarith)
  have hsrc' : |ε * ∑ x ∈ departureRange (fun j => X j ω) n,
      inner ℝ (ξ x) (centralDiff b (x - cellCenter y)) -
        normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))| ≤
      CS * ε * (2 * Real.log ((n : ℝ) + 2)) :=
    hsrc.trans (mul_le_mul_of_nonneg_left hlog1 (mul_nonneg hCS0 hε))
  have hmod' : |normPotential d ε Ψ (cellSet (fun j => X j ω) n) y -
      normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))| ≤
      CM * ε * (2 * Real.log ((n : ℝ) + 2)) :=
    hmod.trans (mul_le_mul_of_nonneg_left hlog2 (mul_nonneg hCM0 hε))
  have hE : Real.log ((n : ℝ) + 2) ≤
      Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2) := by
    linarith [mul_nonneg hBn (Real.sqrt_nonneg (maxLocalTime (fun j => X j ω) n : ℝ))]
  have hlead : (4 * Cb + 2 * CS * ε + 2 * CM * ε) * Real.log ((n : ℝ) + 2) ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε) *
        (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have hcell : cellLocalTime (fun j => X j ω) n y =
      (localTime (fun j => X j ω) n (cellCenter y) : ℝ) := rfl
  rw [hcell, hdyn]
  have hdecomp : b (X n ω - cellCenter y) - b (-cellCenter y) +
      ε * (∑ z ∈ departureRange (fun j => X j ω) n,
        inner ℝ (ξ z) (centralDiff b (z - cellCenter y))) -
        driftDynkin ε ξ (fun z => b (z - cellCenter y)) X n ω -
        normPotential d ε Ψ (cellSet (fun j => X j ω) n) y =
      b (X n ω - cellCenter y) + (-b (-cellCenter y)) +
        (ε * (∑ z ∈ departureRange (fun j => X j ω) n,
          inner ℝ (ξ z) (centralDiff b (z - cellCenter y))) -
          normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))) +
        (normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace (cellCenter y)) -
          normPotential d ε Ψ (cellSet (fun j => X j ω) n) y) +
        (-driftDynkin ε ξ (fun z => b (z - cellCenter y)) X n ω) := by ring
  rw [hdecomp]
  exact approx_error_combination hCb0 hCS0 hCM0 hε hBn hb1
    (by rwa [abs_neg]) hsrc' (by rwa [abs_sub_comm]) (by rwa [abs_neg])

/-- For `n ≥ 2`: `0 < log n` and `log (n + 2) ≤ 2 log n`. -/
private lemma log_add_two_le_two_mul_log {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log n ∧ Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.log_pos (by linarith), ?_⟩
  have h1 := Real.log_le_log (by linarith : (0 : ℝ) < n + 2)
    (by nlinarith : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2)
  rwa [Real.log_pow, Nat.cast_ofNat] at h1

/-- The scale `λ_n` of `eq:interval` is at most `4 (log n)²`. -/
private lemma lam_le_four_mul_log_sq {d : ℕ} {L ℓ : ℝ} (hL1 : 1 ≤ L) (hLℓ : L ≤ 2 * ℓ) :
    (if d = 2 then L ^ 2 else L) ≤ 4 * ℓ ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have h1 : L ^ 2 ≤ (2 * ℓ) ^ 2 := pow_le_pow_left₀ hL0 hLℓ 2
  have h2 : L ≤ L ^ 2 := by nlinarith
  have h3 : (2 * ℓ) ^ 2 = 4 * ℓ ^ 2 := by ring
  split_ifs
  · exact h1.trans h3.le
  · exact h2.trans (h1.trans h3.le)

/-- The error scale `e_n(M)` is at most twice the `log n` form of the statement. -/
private lemma error_scale_le_log {d : ℕ} {M L ℓ C₂ C : ℝ} (hM0 : 0 ≤ M) (hℓ0 : 0 < ℓ)
    (hL1 : 1 ≤ L) (hLℓ : L ≤ 2 * ℓ) (hC₂0 : 0 ≤ C₂) (hC : 2 * C₂ ≤ C) :
    C₂ * ((if d = 2 then L else Real.sqrt L) * Real.sqrt M + L) ≤
      C * ℓ + C * (if d = 2 then Real.sqrt M * ℓ else Real.sqrt (M * ℓ)) := by
  have hL0 : 0 ≤ L := by linarith
  have hsM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  by_cases hd2 : d = 2
  · simp only [hd2, if_true]
    have h1 : L * Real.sqrt M ≤ 2 * ℓ * Real.sqrt M := mul_le_mul_of_nonneg_right hLℓ hsM
    have h2 : L * Real.sqrt M + L ≤ 2 * (ℓ + Real.sqrt M * ℓ) := by linarith
    have h3 : 0 ≤ ℓ + Real.sqrt M * ℓ := by positivity
    calc C₂ * (L * Real.sqrt M + L) ≤ C₂ * (2 * (ℓ + Real.sqrt M * ℓ)) :=
          mul_le_mul_of_nonneg_left h2 hC₂0
      _ = (2 * C₂) * (ℓ + Real.sqrt M * ℓ) := by ring
      _ ≤ C * (ℓ + Real.sqrt M * ℓ) := mul_le_mul_of_nonneg_right hC h3
      _ = C * ℓ + C * (Real.sqrt M * ℓ) := by ring
  · simp only [hd2, if_false]
    have hMℓ : 0 ≤ M * ℓ := mul_nonneg hM0 hℓ0.le
    have h4 : Real.sqrt (4 * (M * ℓ)) = 2 * Real.sqrt (M * ℓ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt : Real.sqrt L * Real.sqrt M ≤ 2 * Real.sqrt (M * ℓ) := by
      rw [← Real.sqrt_mul hL0, ← h4]
      refine Real.sqrt_le_sqrt ?_
      have h5 : L * M ≤ 2 * ℓ * M := mul_le_mul_of_nonneg_right hLℓ hM0
      linarith
    have h2 : Real.sqrt L * Real.sqrt M + L ≤ 2 * (ℓ + Real.sqrt (M * ℓ)) := by linarith
    have h3 : 0 ≤ ℓ + Real.sqrt (M * ℓ) := by positivity
    calc C₂ * (Real.sqrt L * Real.sqrt M + L) ≤ C₂ * (2 * (ℓ + Real.sqrt (M * ℓ))) :=
          mul_le_mul_of_nonneg_left h2 hC₂0
      _ = (2 * C₂) * (ℓ + Real.sqrt (M * ℓ)) := by ring
      _ ≤ C * (ℓ + Real.sqrt (M * ℓ)) := mul_le_mul_of_nonneg_right hC h3
      _ = C * ℓ + C * Real.sqrt (M * ℓ) := by ring

/-- Lemma `lem:local` of the paper for the walk with drift field `ξ`, a choice of subgradients of a
norm `Ψ`, given the estimate of `lem:cell`. -/
theorem norm_local_time_potential_of (hcell : cell_gradient) :
    norm_local_time_potential.{u} := by
  intro d hd Ψ hΨ ε hε hell p hp
  have hd1 : 1 ≤ d := by omega
  obtain ⟨b, h, hK⟩ := exists_kernelFacts hd
  obtain ⟨R, Ca, hR, hgradA⟩ := hK.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨Cb, hCb⟩ := hK.growth
  obtain ⟨CP, hCP0, hCP⟩ := exists_abs_sum_inner_drift_centralDiff_le hd hgrad (normMax Ψ)
  obtain ⟨CS, hCS0, hCS⟩ := exists_abs_source_sum_sub_normPotential_le hd hR hgradA hgrad hΨ hcell
  obtain ⟨CM, hCM0, hCM⟩ := ContactModulus.exists_normPotential_cell_modulus hd hΨ
  have hCb' : ∀ x : Site d, |b x| ≤ |Cb| * Real.log (euclidNorm x + 2) := fun x =>
    (hCb x).trans (mul_le_mul_of_nonneg_right (le_abs_self Cb)
      (Real.log_nonneg (by linarith [euclidNorm_nonneg x])))
  obtain ⟨CI, hCI0, hCI⟩ := exists_interval_mart_drift.{u} hd hε.le hgrad hp
  set n₀ : ℕ := ⌈Real.sqrt d⌉₊ + 2 with hn₀
  set C₁ : ℝ := 8 * |Cb| + 2 * CI + CI ^ 2 with hC₁
  set C₂ : ℝ := 4 * |Cb| + 2 * CS * ε + 2 * CM * ε + CI with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hnp : 0 ≤ (n₀ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set Cint : ℝ := (2 * CP + 1) * ε with hCint
  have hCint0 : 0 ≤ Cint := by positivity
  refine ⟨Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hξ' : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) := by
    intro z i
    by_cases hz : z = 0
    · subst hz
      rw [hξ0]
      simp only [PiLp.zero_apply, abs_zero, mul_zero]
      positivity
    · calc ε * |ξ z i| ≤ ε * Ψ (coordVec i) :=
            mul_le_mul_of_nonneg_left (CERW.Generic.Norm.subgradient_abs_coord_le hΨ (hξ z hz) i)
              hε.le
        _ ≤ 1 / (d : ℝ) := (hell i).le
  have hξΛ : ∀ x, ‖ξ x‖ ≤ normMax Ψ := norm_drift_le hΨ hξ hξ0
  by_cases hn₀le : n₀ ≤ n
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hL1 := one_le_log_add_two hn
    obtain ⟨hBn, hBsq, hLlam⟩ := error_scale_facts d hL1
    have hlam0 : 0 ≤ (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) :=
      by linarith
    have hsq : Real.sqrt d ≤ n := by
      have h1 := Nat.le_ceil (Real.sqrt d)
      have h2 : ((⌈Real.sqrt d⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (by omega : ⌈Real.sqrt d⌉₊ ≤ n)
      linarith
    -- the logarithms
    obtain ⟨hℓ0, hLℓ⟩ := log_add_two_le_two_mul_log hn
    have hlamℓ : (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) ≤
        4 * Real.log n ^ 2 := lam_le_four_mul_log_sq hL1 hLℓ
    have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j : ℕ, euclidNorm (X j ω) ≤ j)} = 0 := by
      refine ae_iff.mp ?_
      filter_upwards [ae_iff.mpr hX.start, ae_euclidNorm_le_drift hd1 hε.le hξ' hX] with ω h0 h1
      exact ⟨h0, h1⟩
    refine measure_le_of_subset_union (fun ω hω => ?_) (hCI hξ' hX n hn) hnull
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hA', hN'⟩ := hcon
    simp only [Set.mem_setOf_eq, not_not] at hN'
    obtain ⟨h0, hnorm⟩ := hN'
    simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hA'
    have hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
        |driftDynkin ε ξ (fun z => b (z - y)) X t ω - driftDynkin ε ξ (fun z => b (z - y)) X s ω| ≤
          CI * ((if d = 2 then Real.log ((n : ℝ) + 2) else Real.sqrt (Real.log ((n : ℝ) + 2))) *
            Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)) := by
      intro s t y hst htn hy
      rw [← error_scale_eq d (Nat.cast_nonneg _)]
      exact hA' s t y hst htn hy
    have hint : ∀ s t : ℕ, s < t → t ≤ n → (intervalMax (fun j => X j ω) s t : ℝ) ≤
        Cint * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) +
          C₁ * (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) :=
      fun s t hst htn => interval_bound_drift hK.poisson hξ0 hCP0 (abs_nonneg Cb) hCI0.le hε.le
        hBn hBsq (hCP ξ hξΛ) hCb' X ω h0 hnorm hn hLlam hmart s t hst htn
    have hC₁le : C₁ * (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) ≤
        (Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p) * Real.log n ^ 2 := by
      calc C₁ * (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2))
          ≤ C₁ * (4 * Real.log n ^ 2) := mul_le_mul_of_nonneg_left hlamℓ hC₁0
        _ = (4 * C₁) * Real.log n ^ 2 := by ring
        _ ≤ (Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p) * Real.log n ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hCint_le : Cint ≤ Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p := by linarith
    refine hω ⟨?_, fun s t hst htn => ?_, fun y hy => ?_⟩
    · have h1 : maxLocalTime (fun j => X j ω) n ≤ intervalMax (fun j => X j ω) 0 n :=
        Finset.sup_le fun z _ => by
          rw [← CERW.Support.Occupation.intervalLocalTime_zero]
          exact intervalLocalTime_le_intervalMax _ 0 n z
      have h2 := hint 0 n (by omega) le_rfl
      rw [CERW.Support.Occupation.freshCount_zero] at h2
      refine (Nat.cast_le.mpr h1).trans (h2.trans (add_le_add ?_ hC₁le))
      exact mul_le_mul_of_nonneg_right hCint_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · refine (hint s t hst htn).trans (add_le_add ?_ hC₁le)
      exact mul_le_mul_of_nonneg_right hCint_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hM0 : (0 : ℝ) ≤ maxLocalTime (fun j => X j ω) n := Nat.cast_nonneg _
      have h := approx_bound_drift hd hK.poisson hξ0 (abs_nonneg Cb) hCS0 hCM0 hCI0.le hε.le hBn
        hCb'
        (fun u m w R' hR' hu => hCS ε hε.le ξ hξ hξ0 u m w R' hR' hu)
        (fun R hR D hD hDsub y z hy hyz => hCM ε hε.le R hR D hD hDsub y z hy hyz)
        X ω h0 hnorm hn hsq hmart y hy
      refine h.trans ?_
      have hC₂' : 4 * |Cb| + 2 * CS * ε + 2 * CM * ε + CI = C₂ := rfl
      rw [hC₂']
      have hC₂le : 2 * C₂ ≤ Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p := by linarith
      have := error_scale_le_log (d := d) (M := (maxLocalTime (fun j => X j ω) n : ℝ))
        (L := Real.log ((n : ℝ) + 2)) (ℓ := Real.log n) hM0 hℓ0 hL1 hLℓ hC₂0 hC₂le
      exact this
  · exact (prob_le_one).trans (ENNReal.one_le_ofReal.mpr
      (one_le_mul_rpow_neg hp (by omega) (not_le.mp hn₀le).le (by
        have : (n₀ : ℝ) ^ p ≤ Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p := by linarith
        exact this)))

end Assembly

end CERW.Support.Norm
