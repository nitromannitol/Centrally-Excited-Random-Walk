module

public import CERW.LimitShapes.LimitLaws.FixedSiteCentering
public import CERW.Frozen.FixedSiteCentering

@[expose] public section

/-!
# lem:fixed-site-centering

The statement at `lem:fixed-site-centering`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `lem:fixed-site-centering`, with the standing assumptions and constant
    scopes of the paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.fixed_site_centering {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ y : Site d, ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          |CERW.potential d ε (CERW.cellSet (X · ω) n) (CERW.toSpace y)
              - 2 * d * ε * (r n - euclidNorm y)
              - CERW.quadraticMart ε (X · ω) n / (ωd * r n ^ d)|
            ≤ C * if d = 2 then Real.log n ^ 3 else 1
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.LimitLaws.fixed_site_centering hd
