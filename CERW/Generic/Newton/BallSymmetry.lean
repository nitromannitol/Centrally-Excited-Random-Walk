import CERW.Model.Potential
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rotational symmetry of the potential of a centred ball

A linear isometry `A` of `ℝ^d` preserves Lebesgue measure and the ball `B(0, b)`. It commutes
with `v ↦ u_v`, and it preserves inner products and distances. The change of variables `v = Av'`
therefore gives `U_{B(0,b)}(Ay) = U_{B(0,b)}(y)`. Any two points of equal norm are exchanged by a
reflection, so `U_{B(0,b)}(y)` depends on `|y|` only. This is the step "for a ball, `U_D` is
radial" of `eq:ballpotential`.
-/

namespace CERW.Generic.Newton

open MeasureTheory CERW

variable {d : ℕ}

/-- A linear isometry of `ℝ^d` commutes with the direction map `unitDir`. -/
private theorem unitDir_map_isometry
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) : unitDir (A v) = A (unitDir v) := by
  simp only [unitDir, A.norm_map, LinearIsometryEquiv.map_smul]

/-- A linear isometry of `ℝ^d` preserves the integrand of the potential, transported from `y`. -/
private theorem integrand_isometry
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (v y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (unitDir (A v)) (A v - A y) / ‖A v - A y‖ ^ d
      = inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := by
  rw [unitDir_map_isometry A v, ← A.map_sub v y, A.norm_map, A.inner_map_map]

/-- The potential of a centred ball is invariant under linear isometries. -/
theorem potential_ball_apply_isometry
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (ε b : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε (Metric.ball 0 b) (A y) = potential d ε (Metric.ball 0 b) y := by
  unfold potential
  congr 1
  have h := (LinearIsometryEquiv.measurePreserving A).setIntegral_preimage_emb
    A.toMeasurableEquiv.measurableEmbedding
    (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - A y) / ‖v - A y‖ ^ d)
    (Metric.ball 0 b)
  rw [LinearIsometryEquiv.preimage_ball, A.symm.map_zero] at h
  calc ∫ v in Metric.ball 0 b, inner ℝ (unitDir v) (v - A y) / ‖v - A y‖ ^ d
      = ∫ x in Metric.ball 0 b,
          inner ℝ (unitDir (A x)) (A x - A y) / ‖A x - A y‖ ^ d := h.symm
    _ = ∫ v in Metric.ball 0 b, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := by
        apply setIntegral_congr_fun measurableSet_ball
        intro v _
        exact integrand_isometry A v y

/-- The potential of a centred ball takes the same value at points of the same norm. -/
theorem potential_ball_eq_of_norm_eq (ε b : ℝ) {y z : EuclideanSpace ℝ (Fin d)}
    (h : ‖y‖ = ‖z‖) :
    potential d ε (Metric.ball 0 b) y = potential d ε (Metric.ball 0 b) z := by
  rcases eq_or_ne y z with rfl | hyz
  · rfl
  · have hA : Submodule.reflection (ℝ ∙ (y - z))ᗮ y = z := Submodule.reflection_sub h
    rw [← potential_ball_apply_isometry (Submodule.reflection (ℝ ∙ (y - z))ᗮ) ε b y, hA]

end CERW.Generic.Newton
