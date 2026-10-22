import CERW.LimitShapes.ContactEvent

/-!
# Contact potential on the common event

The common event at `sec:norm-event` has polynomial exceptional probability,
and `lem:contact` holds on it with constants depending only on the source parameters.
-/

universe u

open MeasureTheory Topology
open LatticeProb (Site)

/-- The contact conclusion together with the actual common-event probability bound,
with every event and contact constant chosen before the subgradient field and law. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.contact_potential_on_common_event {d : ℕ} (hd : 2 ≤ d)
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
              ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ᵐ ω ∂μ, ω ∈ CERW.LimitShapes.section5Event Ψ ε ξ K X n →
            ∀ y₀ : EuclideanSpace ℝ (Fin d),
              Ψ y₀ = CERW.normInnerRadius Ψ (X · ω) n →
              y₀ ∈ closure (CERW.cellSet (X · ω) n)ᶜ →
              CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y₀ ≤
                C * CERW.Support.Norm.ContactEvent.scale d Ψ ε n *
                  CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.ContactEvent.contact_potential_on_common_event hd hΨ hε hell p hp
