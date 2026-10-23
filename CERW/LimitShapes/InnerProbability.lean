import CERW.LimitShapes.EuclideanEvent
import CERW.LimitShapes.EventConsequences

/-!
# Inner-radius probability on the common event

The deterministic proof of Proposition `prop:inner` applies on the literal common event.
Enlarging its constant covers the finitely many times below the deterministic threshold.
-/

universe u

open MeasureTheory
open scoped symmDiff Pointwise
open LatticeProb (Site)

namespace CERW.LimitShapes

open CERW CERW.Support.Norm.ContactEvent
open CERW.Support.Norm.Section5Localization
open CERW.Support.Norm.EuclideanCoarse

/-- All three conclusions of Proposition `prop:inner` increase with their constant. -/
private theorem innerConclusion_mono {d : ℕ} {ε A B : ℝ} {x : ℕ → Site d}
    {n : ℕ} (hAB : A ≤ B) (hr : 0 ≤ scale d (fun v => ‖v‖) ε n)
    (hq : 0 ≤ contactRate d (fun v => ‖v‖) ε n)
    (h : InnerConclusion d ε A x n) : InnerConclusion d ε B x n := by
  refine ⟨h.1.trans ?_, h.2.1.trans ?_, fun y => (h.2.2 y).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hr) hq
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAB hq)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hr)
      (Real.rpow_nonneg hq _)

/-- Proposition `prop:inner`, using the six estimates on the literal common event. -/
theorem inner_radius_from_common_event : CERW.Support.Statements.inner_radius.{u} := by
  intro d hd
  dsimp only
  intro ε hε hεd p hp
  obtain ⟨K, hc, hCo, hLoc, hQuad, _, hMart, _, Cp, hCp, np, _, hprob⟩ :=
    EuclideanEvent.exists_euclidean_event.{u} hd hε hεd p hp
  obtain ⟨Ci, hCi, ni, _, hinner⟩ :=
    inner_on_event hd hε hεd K hc hCo.le hLoc.le hQuad.le hMart.le
  let N := max np ni
  let C := Ci + Cp + (N : ℝ) ^ p
  have hNpow : 0 ≤ (N : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg N) p
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  by_cases hNn : N ≤ n
  · have hr : 0 ≤ scale d (fun v => ‖v‖) ε n :=
      (scale_pos (d := d) (n := n) (by omega)
        CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean hε (by omega)).le
    have hq : 0 ≤ contactRate d (fun v => ‖v‖) ε n := by
      unfold contactRate
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) hr
    have hCiC : Ci ≤ C := by dsimp [C]; linarith
    have hCpC : Cp ≤ C := by dsimp [C]; linarith
    have hXd := (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX
    have hsub : ∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
          (toSpace x) (unitDir (toSpace x)) := by
      intro x hx
      exact isSubgradient_unitDir fun h => hx (eq_zero_of_toSpace_eq_zero h)
    have hbound : μ {ω | ¬ InnerConclusion d ε C (X · ω) n} ≤
        μ (section5Event (fun v => ‖v‖) ε (fun x => unitDir (toSpace x)) K X n)ᶜ := by
      apply measure_mono_ae
      filter_upwards [ae_legal_of_isDriftCERW hXd] with ω hlegal
      intro hbad hgood
      exact hbad (innerConclusion_mono hCiC hr hq
        (hinner _ hsub unitDir_toSpace_zero _ n
          ((le_max_right np ni).trans hNn) hlegal hgood))
    have hfinal := hbound.trans ((hprob μ X hX n
      ((le_max_left np ni).trans hNn)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCpC hnp)))
    simpa only [InnerConclusion, scale, contactRate, normBallVolume_norm,
      unitBallVolume, normInnerRadius, innerRadius] using hfinal
  · apply prob_le_one.trans
    rw [ENNReal.one_le_ofReal]
    have hpow : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hnpos p
    have hle : (n : ℝ) ^ p ≤ (N : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast (by omega : n ≤ N)) hp.le
    rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, le_div_iff₀ hpow, one_mul]
    dsimp [C]
    linarith

end CERW.LimitShapes
