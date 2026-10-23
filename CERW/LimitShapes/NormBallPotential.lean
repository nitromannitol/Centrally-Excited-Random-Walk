import CERW.Support.Norm.GradientIdentity
import CERW.Support.Norm.NormGaugeConsequences

/-!
# Norm ball potential from the gradient identity

Lemma `lem:ballpotential` follows by applying `eq:gradient-identity` to `(ρ - Ψ)₊`.
The identification with the gauge of the closed unit ball supplies its almost everywhere gradient.
-/

open MeasureTheory Filter Topology

namespace CERW.LimitShapes

open CERW.Support.Norm.NormGaugeConsequences
open private CERW.Support.Norm.lipschitzWith_isNorm
  CERW.Support.Norm.isBounded_sublevel from CERW.Support.Norm.BallLayer

/-- Lemma `lem:ballpotential`, obtained from the general gradient identity for `(ρ - Ψ)₊`. -/
theorem norm_ball_potential_from_gradient {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε Ψ {v | Ψ v < ρ} y = 2 * d * ε * max (ρ - Ψ y) 0 := by
  have hd1 : 1 ≤ d := by omega
  have hc := CERW.Generic.Norm.norm_continuous hΨ
  have hf := ((LipschitzWith.const ρ).sub
    (CERW.Support.Norm.lipschitzWith_isNorm hΨ)).max_const 0
  have hs : HasCompactSupport (fun v => max (ρ - Ψ v) 0) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (Metric.isCompact_of_isClosed_isBounded
        (isClosed_le hc continuous_const) (CERW.Support.Norm.isBounded_sublevel hΨ hd1 ρ))
    intro v hv
    change Ψ v ≤ ρ
    by_contra hn
    exact hv (max_eq_right (by linarith))
  have hae := CERW.Support.Norm.GaugePotential.gradient_truncation_ae
    (convex_normClosedUnitBall hΨ) (zero_mem_interior_normClosedUnitBall hΨ) hρ
  rw [gauge_normClosedUnitBall hd1 hΨ] at hae
  have hD : MeasurableSet {v | Ψ v < ρ} :=
    measurableSet_lt hc.measurable measurable_const
  have hi : (∫ v, inner ℝ (gradient (fun w => max (ρ - Ψ w) 0) v) (v - y) /
      ‖v - y‖ ^ d) =
      -∫ v in {v | Ψ v < ρ}, inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d := by
    rw [← integral_neg, ← integral_indicator hD]
    refine integral_congr_ae ?_
    filter_upwards [hae] with v hv
    rw [hv]
    by_cases hmem : v ∈ {w | Ψ w < ρ}
    · simp only [Set.indicator_of_mem hmem, inner_neg_left, neg_div]
    · simp only [Set.indicator_of_notMem hmem, neg_zero, inner_zero_left, zero_div]
  have hid := (CERW.Support.Norm.GradientIdentity.gradient_identity hd hf hs y).2
  rw [hi] at hid
  have hint := neg_injective hid
  unfold CERW.normPotential
  rw [hint]
  have hω := (CERW.unitBallVolume_pos d).ne'
  field_simp

end CERW.LimitShapes
