module

public import CERW.LimitShapes.NormRates
public import CERW.Frozen.NormShapeRates

@[expose] public section

/-!
# prop:norm-shape

The statement at `prop:norm-shape`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `prop:norm-shape`, with the standing assumptions and constant scopes of the
    paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.norm_shape_rates {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (|CERW.normInnerRadius Ψ (X · ω) n - r n|
                    ≤ C * (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
                      else (r n * Real.log n) ^ ((1 : ℝ) / 2)) ∧
                  CERW.normMaxRadius Ψ (X · ω) n - r n
                    ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
                      else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) ∧
                  ∀ x : Site d,
                    |(CERW.localTime (X · ω) n x : ℝ)
                        - 2 * d * ε * max (r n - Ψ (CERW.toSpace x)) 0|
                      ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.norm_shape_rates_from_common_event hd
