module

public import CERW.Frozen.FreedmanBound

@[expose] public section

/-!
# lem:freedman

The statement at `lem:freedman`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `lem:freedman`, with the standing assumptions and constant scopes of the
    paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.freedman_bound :
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ), Martingale Z ℱ μ →
        (∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) →
        μ {ω | ¬ |Z n ω - Z 0 ω|
            ≤ C * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log n) + Real.log n)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Frozen.freedman_bound
