import CERW.LimitShapes.Energy.SiteEstimate
import CERW.LimitShapes.Energy.GlobalPotential

/-!
# Square-energy and contact bounds

The site energy estimate extends to the whole space by the cell modulus. Continuity
then gives the contact bound of Lemma `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb
open CERW.Support.Norm.ContactEvent

/-- The global square-energy bounds of `eq:square-one-sided`. -/
theorem exists_square_one_sided {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ))
    (K : CERW.LimitShapes.EventConstants) (hCo : 0 ≤ K.CCo) (hMart : 0 ≤ K.CMart) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates Ψ ε ξ K X n →
        (∀ v : EuclideanSpace ℝ (Fin d), CERW.cellLocalTime X n v / 2 -
            C * CERW.Support.Norm.ContactEvent.scale d Ψ ε n *
              CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n ≤
            CERW.normPotential d ε Ψ (CERW.cellSet X n) v) ∧
        (∀ v : EuclideanSpace ℝ (Fin d), v ∉ CERW.cellSet X n →
          |CERW.normPotential d ε Ψ (CERW.cellSet X n) v| ≤
            C * CERW.Support.Norm.ContactEvent.scale d Ψ ε n *
              CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n) := by
  obtain ⟨S, hS, Ns, hNs, hs⟩ := exists_site_one_sided hd hΨ hε hell K hCo hMart
  obtain ⟨G, hG, Ng, hNg, hg⟩ := exists_global_one_sided_of_sites hd hΨ hε S hS.le
  obtain ⟨Nr, hNr, hr⟩ := exists_site_scale_threshold hd hΨ hε
  refine ⟨2 * G, by positivity, max Ns (max Ng Nr), by omega, ?_⟩
  intro ξ hξ hξ0 X n hn hpath hev
  have hns : Ns ≤ n := by omega
  have hng : Ng ≤ n := by omega
  have hnr : Nr ≤ n := by omega
  obtain ⟨hL, hR, hcube⟩ := hr n hnr
  have hscale := scale_mul_contactRate Ψ ε n (by linarith)
  have hlog : Real.log (n : ℝ) ≤ scale d Ψ ε n * contactRate d Ψ ε n := by
    rw [hscale]
    split_ifs with hd2
    · have hL0 : 0 ≤ Real.log (n : ℝ) := by linarith
      have hLsq : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
      have hLR : Real.log (n : ℝ) ≤ scale d Ψ ε n := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hLsq) hL0]
      have hsqrt := Real.sq_sqrt (show 0 ≤ scale d Ψ ε n * Real.log n by positivity)
      have hsqrt0 := Real.sqrt_nonneg (scale d Ψ ε n * Real.log n)
      nlinarith [mul_nonneg (sub_nonneg.mpr hLR) hL0]
    · exact le_rfl
  have hdelta : Real.log ((n : ℝ) + 2) ≤
      2 * (scale d Ψ ε n * contactRate d Ψ ε n) :=
    (log_add_two_le_two_log (by omega)).trans (by linarith)
  have herr : S * scale d Ψ ε n * contactRate d Ψ ε n ≤
      S * (2 * (scale d Ψ ε n * contactRate d Ψ ε n)) := by
    have : 0 ≤ scale d Ψ ε n * contactRate d Ψ ε n := by linarith
    nlinarith [mul_nonneg hS.le this]
  have hsites := hs ξ hξ hξ0 X n hns hpath hev
  have hout := hg X n hng hpath _ hdelta (by
    intro z hz
    obtain ⟨hl, hu⟩ := hsites z hz
    exact ⟨by linarith, fun hzero => (hu hzero).trans herr⟩)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hout

/-- Continuity extends the exterior square-energy bound to the contact points of
Lemma `lem:contact`. -/
theorem contact_potential_from_energy {d : ℕ} (hd : 2 ≤ d) :
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
              CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n := by
  intro Ψ hΨ ε hε hell K hCo _hLoc hMart
  obtain ⟨C, hC, N, hN, hs⟩ := exists_square_one_sided hd hΨ hε hell K hCo hMart
  refine ⟨C, hC, N, by omega, ?_⟩
  intro ξ hξ hξ0 X n hn hpath hev y₀ _hy₀ hycl
  have hext := (hs ξ hξ hξ0 X n hn hpath hev).2
  have hcont := CERW.Support.Norm.CoarseVolume.continuous_normPotential hd hΨ hε
    @CERW.Support.Norm.norm_potential_geometry
    (CERW.Support.Occupation.measurableSet_cellSet X n)
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ d) X n))
  exact closure_minimal (fun v hv => (le_abs_self _).trans (hext v hv))
    (isClosed_le hcont continuous_const) hycl

end CERW.LimitShapes.Energy
