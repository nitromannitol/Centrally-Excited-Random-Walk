module

public import CERW.LimitShapes.Exit.UpperProbabilityAux

@[expose] public section

/-!
# Exit-time upper bounds with polynomial probability

The upper exit-time estimates in Proposition `prop:coarse` follow from the bootstrap on the
uniform Freedman event, then counting occupation times to improve the exit-time bound.
-/

universe u

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory

/-- The exit time, occupation times and kernel martingales satisfy the upper bounds
of Proposition `prop:coarse`, except on an event of polynomially small probability. -/
theorem exists_exit_upper_probability {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) →
        ξ 0 = 0 → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X →
      ∀ R : ℝ, R₀ ≤ R →
        μ {ω | ¬ ∃ τ : ℕ, (τ : ℝ) ≤ C * R ^ (d + 1) ∧
          R ≤ Ψ (CERW.toSpace (X τ ω)) ∧
          (∀ j : ℕ, j < τ → Ψ (CERW.toSpace (X j ω)) < R) ∧
          (∀ y : Site d, (CERW.localTime (X · ω) τ y : ℝ) ≤ C * R) ∧
          (∀ y : Site d,
            euclidNorm y ≤ (2 / CERW.normMin Ψ + 2 * Real.sqrt d) * R →
            |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
              (fun z => CERW.latticeKernel d (z - y)) (X · ω) τ| ≤
              C * Real.sqrt R * Real.log R)} ≤ ENNReal.ofReal (C * R ^ (-p)) := by
  obtain ⟨F, hF, hfreedman⟩ := exists_uniform_kernel_freedman.{u} hd p hp
  have hk : (1 : ℝ) ≤ d + 3 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hA : 0 < F * (d + 3 : ℝ) := by positivity
  obtain ⟨B, hB, r, hr, hboot⟩ := exists_exit_bootstrap hd hΨ hε _ hA
  let ρ := 2 / normMin Ψ + 2 * Real.sqrt d
  let V := B * (2 / normMin Ψ + 1) ^ d
  let C := max (max B F) V + 1
  have hBC : B ≤ C := by
    dsimp [C]
    linarith [le_max_left B F, le_max_left (max B F) V]
  have hFC : F ≤ C := by
    dsimp [C]
    linarith [le_max_right B F, le_max_left (max B F) V]
  have hVC : V ≤ C := by dsimp [C]; linarith [le_max_right (max B F) V]
  have hC : 0 < C := hB.trans_le hBC
  refine ⟨C, hC, max r (max (B + 1) ρ), hr.trans (le_max_left _ _), ?_⟩
  intro ξ hξ hξ0 hcoord Ω _ μ _ X hX R hR
  have hrR : r ≤ R := (le_max_left _ _).trans hR
  have hR2 : 2 ≤ R := hr.trans hrR
  have hR1 : 1 ≤ R := by linarith
  have hRp : 0 < R := by linarith
  have hBR : B + 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hρR : ρ ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  let N := ⌈R ^ (d + 2)⌉₊
  obtain ⟨hN2, hRN, hBN, hρN, hlog⟩ := exit_horizon_bounds d hR2 hBR hρR
  have hf := hfreedman ε ξ hε.le hcoord μ X hX N hN2
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by rw [ae_iff]; exact hX.start
  have hs := ae_all_iff.mpr
    (CERW.Support.Drift.ae_sub_mem_unitSteps_drift (by omega) hε.le hcoord hX)
  refine (measure_mono_ae ?_).trans (hf.trans ?_)
  · filter_upwards [h0, hs] with ω hzero hsteps hbad
    intro hgood
    apply hbad
    obtain ⟨τ, _, hexit, hi, hl, hmarts⟩ :=
      hboot ξ hξ hξ0 hcoord R hrR N hBN (X · ω) hzero
        (fun j _ => hsteps j) (fun t ht y hy => by
          have htarget : euclidNorm y ≤ 3 * (N : ℝ) := hy.trans hρN
          have hft := hgood t ht y htarget
          have hc := freedman_log_comparison
            (V := dynkinBracket (driftStepProb d ε ξ)
              (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y))
              (X · ω) t)
            (Real.log_natCast_nonneg N) (Real.log_nonneg hR1) hk hlog
          exact hft.trans (by
            calc F * _ ≤ F * ((d + 3 : ℝ) * _) :=
                mul_le_mul_of_nonneg_left hc hF.le
              _ = _ := by ring))
    have ht := time_le_of_localTime_bound (by omega) hΨ (X · ω) τ hR1 hB.le hi hl
    refine ⟨τ, ht.trans ?_, hexit, hi, ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_right hVC (pow_nonneg hRp.le _)
    · intro y
      exact (hl y).trans (mul_le_mul_of_nonneg_right hBC hRp.le)
    · intro y hy
      exact (hmarts y hy).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBC (Real.sqrt_nonneg R)) (Real.log_nonneg hR1))
  · apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hRp hRN (by linarith : -p ≤ 0)) hF.le).trans
      (mul_le_mul_of_nonneg_right hFC (Real.rpow_nonneg hRp.le _))

end CERW.LimitShapes.Exit
