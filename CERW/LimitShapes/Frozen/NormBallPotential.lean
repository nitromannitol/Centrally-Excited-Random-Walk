import CERW.Frozen.NormBallPotential

/-!
# lem:ballpotential

The statement at `lem:ballpotential`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `lem:ballpotential`, with the standing assumptions and constant scopes of
    the paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.norm_ball_potential {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε Ψ {v | Ψ v < ρ} y = 2 * d * ε * max (ρ - Ψ y) 0
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Frozen.norm_ball_potential hd hΨ ε hρ y
