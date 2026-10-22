import CERW.LimitShapes.CommonEvent

/-!
# The probability of the common event

The six estimates at `sec:norm-event` hold outside a polynomially small event.
All constants and the time threshold precede the subgradient field and realization.
-/

universe u

open MeasureTheory
open LatticeProb (Site)

/-- The literal common event has polynomial exceptional probability with positive
constants uniform in the subgradient field and the walk realization. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.exists_common_event {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) (p : ℝ) (hp : 0 < p) :
    ∃ K : CERW.LimitShapes.EventConstants,
      0 < K.cCo ∧ 0 < K.CCo ∧ 0 < K.CLoc ∧ 0 < K.CQuad ∧
      0 < K.CSquare ∧ 0 < K.CMart ∧ 0 < K.CCross ∧
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
          μ (CERW.LimitShapes.section5Event Ψ ε ξ K X n)ᶜ ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.CommonEvent.exists_common_event hd hΨ hε hell p hp
