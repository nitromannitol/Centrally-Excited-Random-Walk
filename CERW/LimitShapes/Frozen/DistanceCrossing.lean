module

public import CERW.LimitShapes.Crossing.Probability
public import CERW.LimitShapes.Crossing.ExponentialProbability

@[expose] public section

/-!
# The simultaneous distance crossing estimate

The estimate `eq:distance-crossing` is uniform over all earlier times and all
nonnegative real norm levels. Its constant precedes the subgradient field and law.
-/

universe u

open MeasureTheory
open LatticeProb (Site)

/-- The distance crossing estimate holds simultaneously over times and real norm levels
with polynomial exceptional probability at the terminal horizon. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.distance_crossing_bound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ N : ℕ, 2 ≤ N →
        μ {ω | ¬ CERW.LimitShapes.DistanceCrossingBound Ψ C (X · ω) N} ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.Crossing.ExponentialProbability.distance_crossing_from_exponential
    hd hΨ hε hell p hp
