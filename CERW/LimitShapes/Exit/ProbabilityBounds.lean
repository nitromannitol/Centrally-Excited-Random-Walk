import CERW.LimitShapes.Exit.ProbabilityBoundsAux
import CERW.LimitShapes.Exit.UpperProbability

/-!
# Two-sided exit probabilities

The upper exit event and the simultaneous distance crossing event imply both time bounds
in Proposition `prop:coarse`. Their exceptional probabilities are added.
-/

universe u

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory

/-- The first exit time and all occupation times satisfy Proposition `prop:coarse`,
with constants uniform in the subgradient field and the probability space. -/
theorem exit_bounds :
    ∀ {d : ℕ} (_hd : 2 ≤ d)
      (Ψ : EuclideanSpace ℝ (Fin d) → ℝ), CERW.IsNorm Ψ →
      ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
      ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X →
      ∀ R : ℝ, R₀ ≤ R →
        μ {ω | ¬ ∃ τ : ℕ,
          c * R ^ (d + 1) ≤ (τ : ℝ) ∧ (τ : ℝ) ≤ C * R ^ (d + 1) ∧
          R ≤ Ψ (CERW.toSpace (X τ ω)) ∧
          (∀ j : ℕ, j < τ → Ψ (CERW.toSpace (X j ω)) < R) ∧
          (∀ y : Site d, (CERW.localTime (X · ω) τ y : ℝ) ≤ C * R)} ≤
            ENNReal.ofReal (C * R ^ (-p)) := by
  intro d hd Ψ hΨ ε hε hell p hp
  obtain ⟨B, hB, ru, hru, hu⟩ := exists_exit_upper_probability.{u} hd hΨ hε p hp
  obtain ⟨D, hD, hc⟩ :=
    CERW.LimitShapes.Crossing.Probability.distance_crossing_bound.{u} hd hΨ hε hell p hp
  obtain ⟨A, hA, ha⟩ := exists_exit_approximation hd hΨ hε B hB
  have hD' : 0 < D * (d + 3 : ℝ) := by positivity
  obtain ⟨c, hcp, rl, hrl, hl⟩ :=
    exists_exit_lower_of_approximation hd hΨ hε A (D * (d + 3 : ℝ)) hA hD'
  let C := B + D
  have hBC : B ≤ C := by dsimp only [C]; linarith
  have hC : 0 < C := hB.trans_le hBC
  let R₀ := max ru (max rl (max (B + 2)
    (max (Real.exp 1) (normMax Ψ * (3 + Real.sqrt d)))))
  have hru₀ : ru ≤ R₀ := le_max_left _ _
  have hrl₀ : rl ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hB₀ : B + 2 ≤ R₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have he₀ : Real.exp 1 ≤ R₀ :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have ht₀ : normMax Ψ * (3 + Real.sqrt d) ≤ R₀ :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨c, C, hcp, hC, R₀, hru.trans hru₀, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX R hR
  have hcoord := Energy.subgradient_coordinate_bound hΨ hε.le hell ξ hξ hξ0
  have huR := hu ξ hξ hξ0 hcoord μ X hX R (hru₀.trans hR)
  have hR2 : 2 ≤ R := hru.trans (hru₀.trans hR)
  have hR1 : 1 ≤ R := by linarith
  have hRp : 0 < R := by linarith
  have hBR : B + 2 ≤ R := hB₀.trans hR
  have hlogR : 1 ≤ Real.log R := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) (he₀.trans hR)
  let N := ⌈R ^ (d + 2)⌉₊
  obtain ⟨hN, hRN, hBN, _, hlogN⟩ :=
    exit_horizon_bounds d hR2 (show B + 1 ≤ R by linarith) (le_refl R)
  have hcN := hc ξ hξ hξ0 μ X hX N hN
  let Eu : Set Ω := {ω | ¬ ∃ τ : ℕ, (τ : ℝ) ≤ B * R ^ (d + 1) ∧
    R ≤ Ψ (toSpace (X τ ω)) ∧
    (∀ j : ℕ, j < τ → Ψ (toSpace (X j ω)) < R) ∧
    (∀ y : Site d, (localTime (X · ω) τ y : ℝ) ≤ B * R) ∧
    (∀ y : Site d, euclidNorm y ≤ (2 / normMin Ψ + 2 * Real.sqrt d) * R →
      |dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y))
        (X · ω) τ| ≤ B * Real.sqrt R * Real.log R)}
  let Ec : Set Ω := {ω | ¬ CERW.LimitShapes.DistanceCrossingBound Ψ D (X · ω) N}
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by rw [ae_iff]; exact hX.start
  have hs := ae_all_iff.mpr
    (CERW.Support.Drift.ae_sub_mem_unitSteps_drift (by omega) hε.le hcoord hX)
  have hsub : {ω | ¬ ∃ τ : ℕ,
      c * R ^ (d + 1) ≤ (τ : ℝ) ∧ (τ : ℝ) ≤ C * R ^ (d + 1) ∧
      R ≤ Ψ (toSpace (X τ ω)) ∧
      (∀ j : ℕ, j < τ → Ψ (toSpace (X j ω)) < R) ∧
      (∀ y : Site d, (localTime (X · ω) τ y : ℝ) ≤ C * R)} ≤ᵐ[μ] (Eu ∪ Ec : Set Ω) := by
    filter_upwards [h0, hs] with ω hzero hsteps hbad
    by_cases heu : ω ∈ Eu
    · exact Or.inl heu
    by_cases hec : ω ∈ Ec
    · exact Or.inr hec
    obtain ⟨τ, ht, hex, hi, hlt, hm⟩ := Classical.not_not.mp heu
    have hpath : CERW.Support.Norm.ContactEvent.PathTyping d (X · ω) := ⟨hzero, hsteps⟩
    obtain ⟨ht3, hts⟩ := exit_time_large (by omega) hΨ hpath (ht₀.trans hR) hex
    have htN : τ ≤ N := by exact_mod_cast (ht.trans hBN.le)
    have happ := ha ξ hξ hξ0 (X · ω) τ ht3 hts hpath R hR1 hlogR
      (exit_time_log_bound hR2 hBR ht) hm
    have hcross := radius_bound_of_distance_crossing (by omega) hΨ hD.le htN hlogN
      (Classical.not_not.mp hec)
    have hlow := hl R (hrl₀.trans hR) (X · ω) τ hzero hsteps hi hex happ hcross
    exfalso
    apply hbad
    exact ⟨τ, hlow, ht.trans (mul_le_mul_of_nonneg_right hBC (pow_nonneg hRp.le _)),
      hex, hi, fun y => (hlt y).trans (mul_le_mul_of_nonneg_right hBC hRp.le)⟩
  calc
    μ _ ≤ μ (Eu ∪ Ec) := measure_mono_ae hsub
    _ ≤ μ Eu + μ Ec := measure_union_le _ _
    _ ≤ ENNReal.ofReal (B * R ^ (-p)) + ENNReal.ofReal (D * (N : ℝ) ^ (-p)) :=
      add_le_add huR hcN
    _ ≤ ENNReal.ofReal (B * R ^ (-p)) + ENNReal.ofReal (D * R ^ (-p)) := by
      apply add_le_add le_rfl
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hRp hRN (by linarith : -p ≤ 0)) hD.le
    _ = ENNReal.ofReal (C * R ^ (-p)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp only [C]
      ring

end CERW.LimitShapes.Exit
