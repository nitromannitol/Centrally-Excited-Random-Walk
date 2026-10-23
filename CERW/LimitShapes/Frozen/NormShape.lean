import CERW.LimitShapes.Shape
import CERW.Frozen.NormShape

/-!
# thm:norm-shape

The statement at `thm:norm-shape`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `thm:norm-shape`, with the standing assumptions and constant scopes of the
    paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.norm_shape {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hεΨ : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | Ψ (CERW.toSpace x) < (1 - η) * r n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | Ψ (CERW.toSpace x) < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - Ψ (CERW.toSpace x)) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.norm_shape_from_rates hd hΨ hξ hξ0 hε hεΨ μ X hX
