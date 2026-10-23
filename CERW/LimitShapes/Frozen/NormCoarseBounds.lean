import CERW.LimitShapes.Exit.Assembly
import CERW.Frozen.NormCoarseBounds

/-!
# prop:coarse

The statement at `prop:coarse`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `prop:coarse`, with the standing assumptions and constant scopes of the
    paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.norm_coarse_bounds {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (c * r n ^ d ≤ ((CERW.departureRange (X · ω) n).card : ℝ) ∧
                  ((CERW.departureRange (X · ω) n).card : ℝ) ≤ C * r n ^ d ∧
                  c * r n ≤ (CERW.maxLocalTime (X · ω) n : ℝ) ∧
                  (CERW.maxLocalTime (X · ω) n : ℝ) ≤ C * r n ∧
                  c * r n ≤ CERW.maxRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ C * r n)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.Exit.norm_coarse_bounds_via_exit.{u} hd
