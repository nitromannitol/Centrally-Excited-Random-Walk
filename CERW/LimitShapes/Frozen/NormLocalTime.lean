import CERW.LimitShapes.LocalTime
import CERW.LimitShapes.LocalApproximation

/-!
# lem:local

The statement at `lem:local`.
-/

universe u

open MeasureTheory
open LatticeProb (Site)

/-- The conclusion of `lem:local`, with the standing assumptions and constant scopes of the paper.
    -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.norm_local_time_potential {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
            |CERW.cellLocalTime (X · ω) n y
                - CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y| ≤
              C * Real.log n + C *
                (if d = 2 then Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                  else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.local_time_potential_from_dynkin hd
