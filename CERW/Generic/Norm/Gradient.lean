import CERW.Generic.Norm.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The gradient of a norm

A norm is Lipschitz with constant `Σ_i Ψ(e_i)`, so by Rademacher's theorem it is differentiable
almost everywhere; where it is differentiable its gradient is a subgradient.
-/

namespace CERW.Generic.Norm

open CERW MeasureTheory

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A norm is Lipschitz: `|Ψ x - Ψ y| ≤ (Σ_i Ψ(e_i)) |x - y|`. -/
theorem abs_sub_le_sum_mul (hΨ : IsNorm Ψ) (x y : EuclideanSpace ℝ (Fin d)) :
    |Ψ x - Ψ y| ≤ (∑ i, Ψ (coordVec i)) * ‖x - y‖ := by
  have hcoord : ∀ i, |(x - y) i| ≤ ‖x - y‖ := by
    intro i
    have h := PiLp.norm_apply_le (p := 2) (x - y) i
    rwa [Real.norm_eq_abs] at h
  have hnonneg : ∀ i, 0 ≤ Ψ (coordVec i) := fun i => (map_zero_nonneg_neg hΨ).2.1 _
  calc |Ψ x - Ψ y| ≤ Ψ (x - y) := abs_sub_le hΨ x y
    _ ≤ ∑ i, |(x - y) i| * Ψ (coordVec i) := le_sum_coord hΨ (x - y)
    _ ≤ ∑ i, ‖x - y‖ * Ψ (coordVec i) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (hcoord i) (hnonneg i)
    _ = (∑ i, Ψ (coordVec i)) * ‖x - y‖ := by
          rw [← Finset.mul_sum, mul_comm]

/-- A norm is differentiable at almost every point (Rademacher). -/
theorem ae_differentiableAt (hΨ : IsNorm Ψ) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ Ψ v := by
  have hlip : LipschitzWith (Real.toNNReal (∑ i, Ψ (coordVec i))) Ψ := by
    apply LipschitzWith.of_dist_le'
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    exact abs_sub_le_sum_mul hΨ x y
  exact hlip.ae_differentiableAt

/-- A norm is convex on the whole space: subadditivity and absolute homogeneity give
`Ψ (a • x + b • y) ≤ a * Ψ x + b * Ψ y` for `a, b ≥ 0`. -/
private lemma convexOn_univ_isNorm (hΨ : IsNorm Ψ) : ConvexOn ℝ Set.univ Ψ := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  calc Ψ (a • x + b • y) ≤ Ψ (a • x) + Ψ (b • y) := hΨ.add_le _ _
    _ = a * Ψ x + b * Ψ y := by
          rw [hΨ.smul a x, hΨ.smul b y, abs_of_nonneg ha, abs_of_nonneg hb]

/-- Where a norm is differentiable, its gradient is a subgradient. -/
theorem gradient_isSubgradient (hΨ : IsNorm Ψ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : DifferentiableAt ℝ Ψ v) : IsSubgradient Ψ v (gradient Ψ v) := by
  intro y
  let w : EuclideanSpace ℝ (Fin d) := y - v
  let path : ℝ → EuclideanSpace ℝ (Fin d) := fun t => v + t • w
  have hconv : ConvexOn ℝ Set.univ (Ψ ∘ path) := by
    have h := (convexOn_univ_isNorm hΨ).comp_affineMap (AffineMap.lineMap v (v + w))
    have hfun : (Ψ ∘ ⇑(AffineMap.lineMap v (v + w))) = (Ψ ∘ path) := by
      funext t
      simp only [Function.comp_apply, path]
      rw [AffineMap.lineMap_apply_module']
      congr 1
      module
    rwa [hfun] at h
  have hpath : HasDerivAt path w 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • w) w 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).smul_const w
    simpa [path] using h1.const_add v
  have hderiv : HasDerivAt (Ψ ∘ path) ((fderiv ℝ Ψ v) w) 0 := by
    have hc := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hv.hasGradientAt.hasFDerivAt hpath
      (by simp [path])
    simpa only [Function.comp_apply, InnerProductSpace.toDual_apply_apply, toDual_gradient]
      using hc
  have hslope := hconv.le_slope_of_hasDerivAt (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    (by norm_num) hderiv
  rw [slope_def_field] at hslope
  have hmain : (Ψ ∘ path) 0 + (fderiv ℝ Ψ v) w ≤ (Ψ ∘ path) 1 := by
    simp only [Function.comp_apply]
    norm_num at hslope
    linarith
  have hrewrite : (fderiv ℝ Ψ v) w = inner ℝ (gradient Ψ v) w := by
    rw [← toDual_gradient]
    rfl
  rw [hrewrite] at hmain
  simpa [Function.comp_apply, path, w] using hmain

end CERW.Generic.Norm
