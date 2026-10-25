module

public import CERW.Frozen.LayerPotential

@[expose] public section

/-!
# lem:layer

The statement at `lem:layer`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `lem:layer`, with the standing assumptions and constant scopes of the paper.
    -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.layer_potential {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (hb : 0 ≤ b) (ha : 0 < a) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDm : MeasurableSet D) (hD : D ⊆ {v | b ≤ Ψ v ∧ Ψ v ≤ b + a})
    (y : EuclideanSpace ℝ (Fin d)) :
    |CERW.normPotential d ε Ψ D y| ≤ 2 * d * ε * a
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Frozen.layer_potential hd hΨ hε hb ha hDm hD y
