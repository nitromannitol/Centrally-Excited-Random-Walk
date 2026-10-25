module

public import CERW.LimitShapes.InnerProbability
public import CERW.Frozen.InnerRadius

@[expose] public section

/-!
# prop:inner

The statement at `prop:inner`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `prop:inner`, with the standing assumptions and constant scopes of the
    paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.inner_radius {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let q : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (|CERW.innerRadius (X · ω) n - r n| ≤ C * r n * q n ∧
                  volume (((r n)⁻¹ • CERW.cellSet (X · ω) n) ∆
                      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
                    ≤ ENNReal.ofReal (C * q n) ∧
                  ∀ y : EuclideanSpace ℝ (Fin d),
                    |CERW.cellLocalTime (X · ω) n y - 2 * d * ε * max (r n - ‖y‖) 0|
                      ≤ C * r n * q n ^ ((1 : ℝ) / d))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.inner_radius_from_common_event.{u} hd
