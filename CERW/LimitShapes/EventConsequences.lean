import CERW.LimitShapes.Frozen.ContactPotential
import CERW.LimitShapes.InnerApproximation

/-!
# Deterministic consequences of the common event

On the coarse event the walk never reaches the quadratic stopping radius.
The contact and quadratic estimates therefore supply the inputs of the
Euclidean inner-radius argument.
-/

open MeasureTheory Topology
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes

open CERW CERW.Support.Norm.ContactEvent

/-- Stopping leaves the quadratic sum unchanged when the path stays inside the ball. -/
theorem stoppedQuadratic_eq {d : ℕ} (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (R : ℝ) (X : ℕ → Site d) (n : ℕ)
    (h : ∀ j : ℕ, j < n → euclidNorm (X j) < R) :
    stoppedQuadratic ε ξ R X n = quadraticMartingale d ε ξ X n := by
  unfold stoppedQuadratic quadraticMartingale
  refine Finset.sum_congr rfl fun j hj => ?_
  exact if_pos (fun k hk => h k (lt_of_le_of_lt hk (Finset.mem_range.mp hj)))

/-- The radius scale is positive at every positive time. -/
theorem scale_pos {d : ℕ} (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    0 < scale d Ψ ε n := by
  have hV := CERW.Support.Norm.ContactAssembly.normBallVolume_pos' hd hΨ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The stopped Azuma bound gives the unstopped quadratic bound on the coarse event. -/
theorem quadratic_bound_of_event {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {K : EventConstants}
    (hc : 0 < K.cCo) (hQ : 0 ≤ K.CQuad) {X : ℕ → Site d} {n : ℕ} (hn : 0 < n)
    (hE : EventEstimates Ψ ε ξ K X n) :
    QuadraticEstimate d ε ξ (K.CQuad / K.cCo) X n := by
  have hr := scale_pos hd hΨ hε hn
  have hco := hE.1
  obtain ⟨_, _, _, _, hRlow, hRhigh⟩ := hco
  have hstop : stoppedQuadratic ε ξ ((K.CCo + 1) * scale d Ψ ε n) X n =
      quadraticMartingale d ε ξ X n := by
    apply stoppedQuadratic_eq
    intro j hj
    have hjR := euclidNorm_le_maxRadius X (Nat.le_of_lt hj)
    linarith
  have hquad := hE.2.2.1
  rw [hstop] at hquad
  refine hquad.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  calc K.CQuad * scale d Ψ ε n =
      (K.CQuad / K.cCo) * (K.cCo * scale d Ψ ε n) := by field_simp
    _ ≤ (K.CQuad / K.cCo) * (maxRadius X n + 1) :=
      mul_le_mul_of_nonneg_left (hRlow.trans (le_add_of_nonneg_right zero_le_one))
        (div_nonneg hQ hc.le)

open CERW.Support.Norm.Section5Localization

/-- The Euclidean inner-radius, volume, and profile bounds on the six-estimate event. -/
theorem inner_on_event {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (K : EventConstants)
    (hc : 0 < K.cCo) (hCo : 0 ≤ K.CCo) (hLoc : 0 ≤ K.CLoc)
    (hQuad : 0 ≤ K.CQuad) (hMart : 0 ≤ K.CMart) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 →
          IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) →
        ξ 0 = 0 → ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
        EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
        InnerConclusion d ε C X n := by
  have hΨ : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
    CERW.Support.Norm.Section5Localization.isNorm_euclidean
  have hell : ∀ i : Fin d, ε * ‖coordVec i‖ < 1 / (d : ℝ) := by
    intro i
    simpa only [coordVec, PiLp.norm_single, norm_one, mul_one] using hεd
  obtain ⟨Cc, hCc, nc, hnc, hcontact⟩ := contact_potential hd _ hΨ ε hε hell K hCo hLoc hMart
  let J : CERW.Support.Norm.ContactEvent.EventConstants :=
    ⟨K.cCo, K.CCo, K.CLoc, 0, 0, K.CQuad / K.cCo, 0⟩
  obtain ⟨C, hC, ni, hinner⟩ := InnerApproximation.inner_of_approximation_inputs hd hε J hCc
  refine ⟨C, hC, max ni nc, hnc.trans (le_max_right _ _), ?_⟩
  intro ξ hξ hξ0 X n hn hty hE
  have hn2 : 2 ≤ n := hnc.trans ((le_max_right _ _).trans hn)
  have hQ := quadratic_bound_of_event (by omega : 1 ≤ d) hΨ hε hc hQuad (by omega) hE
  exact hinner ξ hξ hξ0 X n ((le_max_left _ _).trans hn) hty ⟨hE.1, hE.2.1, hQ⟩
    (hcontact ξ hξ hξ0 X n ((le_max_right _ _).trans hn) hty hE)

end CERW.LimitShapes
