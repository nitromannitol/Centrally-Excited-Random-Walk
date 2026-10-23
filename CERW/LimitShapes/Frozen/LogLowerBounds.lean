import CERW.Frozen.LogLowerBounds
import CERW.LimitShapes.LogLower

/-!
# prop:log-lower

The statement at `prop:log-lower`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `prop:log-lower`, with the standing assumptions and constant scopes of the
    paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.log_lower_bounds {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ c C h₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        (∀ n : ℕ, n₀ ≤ n → ∀ h : ℝ, h₀ ≤ h → h ≤ r n / 8 →
          μ {ω | r n - h ≤ CERW.innerRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ r n + h}
            ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (d - 1) * Real.exp (-(C * h))))) ∧
          μ {ω | CERW.maxRadius (X · ω) n ≤ r n + h}
            ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (d - 1) * Real.exp (-(C * h))))
              + Real.exp (-(c * r n ^ ((d : ℝ) - 3) * h ^ 2)))) ∧
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          c * Real.log n < max (r n - CERW.innerRadius (X · ω) n)
            (CERW.maxRadius (X · ω) n - r n) ∧
          (3 ≤ d → c * Real.log n < CERW.maxRadius (X · ω) n - r n)
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.log_lower_bounds_from_azuma hd
