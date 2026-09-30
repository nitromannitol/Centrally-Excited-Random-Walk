import CERW.Model.Potential
import CERW.Model.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The potential of a norm, and the positive part of the Euclidean potential

For a norm `Ψ` and a set `D ⊆ ℝ^d`, the potential of `eq:potential-norm` is
`U_D(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v - y) |v - y|^{-d} dv`. Mathlib's `gradient Ψ v` is the gradient
where `Ψ` is differentiable and `0` elsewhere. A norm is Lipschitz, so by Rademacher's theorem the
exceptional set is null and does not affect the integral. For the Euclidean norm the gradient is
`v/|v|` away from the origin and `0` at it, so `normPotential` is `potential`.

`positivePotential` is the Euclidean potential with its negative contributions discarded,
`U_D^+(y) = (2ε/ω_d) ∫_D [u_v · (v - y) |v - y|^{-d}]_+ dv` (`sec:contact`, before
`lem:near-far`). As in `potential`, the integrand reads `0` at the single point `v = y`.
-/

namespace CERW

open MeasureTheory

variable {d : ℕ}

/-- The potential `U_D(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v - y) |v - y|^{-d} dv` of `eq:potential-norm`. -/
noncomputable def normPotential (d : ℕ) (ε : ℝ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d

/-- The positive part `U_D^+(y) = (2ε/ω_d) ∫_D [u_v · (v - y) |v - y|^{-d}]_+ dv` of the Euclidean
potential. -/
noncomputable def positivePotential (d : ℕ) (ε : ℝ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * ε / unitBallVolume d * ∫ v in D, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0

end CERW
