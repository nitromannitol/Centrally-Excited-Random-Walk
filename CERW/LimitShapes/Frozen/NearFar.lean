import CERW.Frozen.NearFar

/-!
# lem:near-far

The statement at `lem:near-far`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `lem:near-far`, with the standing assumptions and constant scopes of the
    paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.near_far {d : ℕ} (hd : 2 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∃ C : ℝ, 0 < C ∧
      ∀ w b lam : ℝ, 1 ≤ w → w ≤ b → 1 ≤ lam →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
        D ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w} →
        (∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
          volume (D ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (lam * t ^ (d - 1))) →
        (∀ y : EuclideanSpace ℝ (Fin d), ∫ v in D, ‖v - y‖ ^ (2 - (d : ℝ)) ≤ lam * b) →
        ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
          CERW.positivePotential d ε D y
            ≤ C * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + C * lam
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Frozen.near_far hd
