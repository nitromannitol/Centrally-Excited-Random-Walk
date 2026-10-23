import CERW.LimitShapes.Energy.Contact
import CERW.LimitShapes.ContactPotential

/-!
# lem:contact

The statement at `lem:contact`, on the event defined in
`sec:norm-event` of the same source. The deterministic formulation applies to every
legal path and every choice of nonnegative event constants.
-/

open MeasureTheory Topology
open LatticeProb (Site)

/-- The deterministic conclusion of `lem:contact` for the fixed constants of the common event. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.contact_potential {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ K : CERW.LimitShapes.EventConstants, 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CMart →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates Ψ ε ξ K X n →
        ∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = CERW.normInnerRadius Ψ X n →
          y₀ ∈ closure (CERW.cellSet X n)ᶜ →
          CERW.normPotential d ε Ψ (CERW.cellSet X n) y₀ ≤
            C * CERW.Support.Norm.ContactEvent.scale d Ψ ε n *
              CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.Energy.contact_potential_from_energy hd
