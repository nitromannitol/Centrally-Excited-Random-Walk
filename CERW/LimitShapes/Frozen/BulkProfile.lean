import CERW.LimitShapes.BulkProfileProbability
import CERW.Frozen.BulkProfile

/-!
# prop:bulk-profile

The statement at `prop:bulk-profile`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `prop:bulk-profile`, with the standing assumptions and constant scopes of
    the paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.bulk_profile {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      let Good : (ℕ → Site d) → ℕ → Prop := fun Y n =>
        ∀ y : Site d, euclidNorm y ≤ θ * r n →
          |(CERW.localTime Y n y : ℝ) - 2 * d * ε * (r n - euclidNorm y)|
            ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n)
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good (X · ω) n)
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.bulk_profile_from_common_event hd
