import CERW.Model.Norm

/-!
# The Moreau envelope of a norm

`F_τ(x) = min_z {Ψ(z) + |x - z|²/(2τ)}` (`sec:moreau`). For a norm the function minimized is
nonnegative, so the infimum is a real number; it is attained, which is a lemma. The paper's
`p_x = ∇F_τ(x)` is Mathlib's `gradient (moreauEnvelope Ψ τ) x`; `F_τ` is continuously
differentiable, which is a lemma.
-/

namespace CERW

variable {d : ℕ}

/-- The Moreau envelope `F_τ(x) = inf_z {Ψ(z) + |x - z|²/(2τ)}`. -/
noncomputable def moreauEnvelope (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (τ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨅ z, Ψ z + ‖x - z‖ ^ 2 / (2 * τ)

end CERW
