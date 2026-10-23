import CERW.LimitShapes.Energy.SiteScales
import CERW.LimitShapes.Energy.Bracket

/-!
# Pointwise inputs for the site estimate

The deterministic comparison and the actual local martingale in Lemma `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb
open CERW.Support.Norm CERW.Support.Norm.ContactEvent

/-- Subgradients satisfy the coordinate ellipticity required by the transition kernel. -/
theorem subgradient_coordinate_bound {d : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ x, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0) :
    ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) := by
  intro z i
  by_cases hz : z = 0
  · subst z
    rw [hξ0]
    simp only [PiLp.zero_apply, abs_zero, mul_zero]
    positivity
  · exact (mul_le_mul_of_nonneg_left
      (CERW.Generic.Norm.subgradient_abs_coord_le hΨ (hξ z hz) i) hε).trans (hell i).le

/-- The pointwise potential decomposition has logarithmic error in Lemma `lem:contact`. -/
theorem exists_site_pointwise_bound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), 3 ≤ n → PathTyping d X →
      ∀ y : Site d, euclidNorm y ≤ 3 * (n : ℝ) →
        |(localTime X n y : ℝ) - normPotential d ε Ψ (cellSet X n) (toSpace y) +
          dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y)) X n| ≤
            P * Real.log n := by
  obtain ⟨h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  have hB : ContactShared.BregmanSumBound d Ψ :=
    ContactBregman.bregmanSumBound_of hd hΨ
      (fun φ h1 h2 h3 => ContactWeakLap.inner_gradient_integral_nonpos hΨ h1 h2 h3)
      (ContactCellTest.cellTestBound hd hΨ)
  obtain ⟨P, hP, hp⟩ :=
    ContactPointwise.exists_abs_localTime_sub_normPotential_add_driftDynkin_le.{0} hd hΨ hB hK
  refine ⟨2 * (P * (1 + ε)), by positivity, ?_⟩
  intro ξ hξ hξ0 X n hn ⟨hX0, hsteps⟩ y hy
  have hnorm := CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hsteps
  have ht := hp ε hε.le ξ hξ hξ0 (fun j (_ : Unit) => X j) () hX0 hnorm n
    (by omega) y hy
  rw [← CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin
    (by omega : 1 ≤ d) ε ξ (fun z => latticeKernel d (z - y))
    (fun j (_ : Unit) => X j) n ()] at ht
  exact ht.trans (by
    have := mul_le_mul_of_nonneg_left (log_add_two_le_two_log hn)
      (by positivity : 0 ≤ P * (1 + ε))
    nlinarith only [this])

end CERW.LimitShapes.Energy
