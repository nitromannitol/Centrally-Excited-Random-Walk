import CERW.LimitShapes.ContactApproximation
import CERW.LimitShapes.LocalBracket

/-!
# ContactPotential

The proof of the estimate in the paper, using the common martingale event.
-/

open MeasureTheory Topology
open LatticeProb (Site)

/-- The estimate follows from the deterministic inputs on the common event. -/
theorem CERW.LimitShapes.contact_potential_bound {d : ℕ} (hd : 2 ≤ d) :
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
:= by
  intro Ψ hΨ ε hε hell K hCco hCloc hCmart
  obtain ⟨Cw, hCw, hweight⟩ :=
    CERW.LimitShapes.localMartingaleBound_to_weight hd hΨ hε hell hCmart
  obtain ⟨C, hC, n₀, h⟩ := CERW.LimitShapes.contact_bound_of_approximation_inputs hd hΨ hε
    K.cCo K.CCo K.CLoc Cw hCco hCloc hCw
  refine ⟨C, hC, max n₀ 2, le_max_right _ _, ?_⟩
  intro ξ hξ hξ0 X n hn hty hE
  exact h ξ hξ hξ0 X n ((le_max_left _ _).trans hn) hty hE.1 hE.2.1
    (hweight ξ hξ hξ0 X n ((le_max_right _ _).trans hn) hE.2.2.2.2.1)
