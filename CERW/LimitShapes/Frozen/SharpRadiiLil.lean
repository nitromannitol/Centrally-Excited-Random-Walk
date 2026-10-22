import CERW.Frozen.SharpRadiiLil

/-!
# thm:sharp

The statement at `thm:sharp, part (ii`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `thm:sharp`, with the standing assumptions and constant scopes of the paper.
    -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.sharp_radii_lil {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ r n - CERW.innerRadius (X · ω) n) ∧
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ CERW.maxRadius (X · ω) n - r n)
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Frozen.sharp_radii_lil hd
