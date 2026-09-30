import CERW.Model.Norm
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The distributional Laplacian of a norm

The measure `μ` of `lem:cell`: `∫ φ dμ = ∫ Ψ(v) Δφ(v) dv` for every smooth compactly supported
`φ` on `ℝ^d` (the paper writes `Δφ = Σ_i ∂_i²φ`). The paper shows that it is a positive Radon
measure. Here the defining identity is the predicate `IsDistribLaplacian Ψ μ`; `lem:cell` is
stated for every locally finite measure with this property, and such a measure exists (a lemma).
-/

namespace CERW

open MeasureTheory
open scoped ContDiff

variable {d : ℕ}

/-- `μ` is the distributional Laplacian of `Ψ`: `∫ φ dμ = ∫ Ψ Δφ` for every smooth compactly
supported `φ`. -/
def IsDistribLaplacian (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ v, φ v ∂μ = ∫ v, Ψ v * Laplacian.laplacian φ v

end CERW
