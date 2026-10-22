import CERW.Frozen.OuterRadius

/-!
# prop:stronger-outer

The statement at `prop:stronger-outer`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `prop:stronger-outer`, with the standing assumptions and constant scopes of
    the paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.outer_radius {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ CERW.maxRadius (X · ω) n ≤ r n + C *
            (if d = 2 then Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
              else Real.log n ^ ((d : ℝ) + 1))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Frozen.outer_radius hd
