import CERW.Frozen.FluctuationRates
import CERW.LimitShapes.Curvature.FluctuationTheorem

/-!
# thm:fluctuations

The statement at `thm:fluctuations`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `thm:fluctuations`, with the standing assumptions and constant scopes of the
    paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.fluctuation_rates {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      (if d = 2 then
          |CERW.innerRadius Y n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
            CERW.maxRadius Y n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else
          |CERW.innerRadius Y n - r n| ≤ C * Real.log n ∧
            CERW.maxRadius Y n - r n ≤ C * Real.log n ^ ((d : ℝ) + 1)) ∧
      volume (((r n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          ≤ ENNReal.ofReal
            (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (r n * Real.log n)
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good C (X · ω) n)
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.Curvature.fluctuation_rates_via_curvature.{u} hd
