import CERW.Frozen.CellGradient

/-!
# lem:cell

The statement at `lem:cell`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `lem:cell`, with the standing assumptions and constant scopes of the paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.cell_gradient {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m →
        CERW.IsDistribLaplacian Ψ m →
      ∀ x : Site d,
        ENNReal.ofReal (∫ v in CERW.cell x, ‖gradient Ψ v - ξ x‖)
          ≤ ENNReal.ofReal C * m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Frozen.cell_gradient hd
