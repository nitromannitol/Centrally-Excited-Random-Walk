module

public import CERW.LimitShapes.EuclideanEvent
public import CERW.LimitShapes.Curvature.FluctuationProbabilityAux
public import CERW.LimitShapes.Curvature.EventBorelCantelli

@[expose] public section

/-!
# Fluctuation probabilities from the literal common event

Theorem `thm:fluctuations` combines the deterministic common-event estimates, then applies
Borel--Cantelli with a summable exceptional exponent. The same constant gives both conclusions.
-/

universe u

open CERW LatticeProb MeasureTheory Filter

namespace CERW.LimitShapes.Curvature

open CERW.Support.Norm.EuclideanCoarse
open CERW.Support.Norm.Section5Localization

/-- The common-event outer and profile estimates imply all of Theorem `thm:fluctuations`,
including polynomial tails and the almost sure eventual assertion with the same constant. -/
theorem fluctuation_rates_of_event_bounds
    (houter : ∀ {d : ℕ} (_hd : 2 ≤ d) {ε : ℝ}, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ K : CERW.LimitShapes.EventConstants,
        0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
        CERW.maxRadius X n ≤ CERW.Support.Outer.Radius.radius d ε n + C *
          (if d = 2 then Real.sqrt (CERW.Support.Outer.Radius.radius d ε n) *
            Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)))
    (hprofile : ∀ {d : ℕ} (_hd : 2 ≤ d) {ε : ℝ}, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ K : CERW.LimitShapes.EventConstants,
        0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
      ∀ y : EuclideanSpace ℝ (Fin d),
        |CERW.cellLocalTime X n y - 2 * d * ε *
          max (CERW.Support.Outer.Radius.radius d ε n - ‖y‖) 0| ≤
          C * (if d = 2 then Real.sqrt (CERW.Support.Outer.Radius.radius d ε n) *
            Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (CERW.Support.Outer.Radius.radius d ε n * Real.log n))) :
    CERW.Support.Statements.fluctuation_rates.{u} := by
  intro d hd
  dsimp only
  intro ε hε hεd p hp
  let ps := p + 2
  have hps : 1 < ps := by dsimp only [ps]; linarith
  obtain ⟨K, hc, hCo, hLoc, hQuad, _, hMart, hCross, Cp, hCp, np, _, hprob⟩ :=
    EuclideanEvent.exists_euclidean_event.{u} hd hε hεd ps (by linarith)
  obtain ⟨Ci, hCi, ni, _, hinner⟩ :=
    inner_on_event hd hε hεd K hc hCo.le hLoc.le hQuad.le hMart.le
  obtain ⟨Co, hCoPos, no, _, houter⟩ :=
    houter hd hε hεd K hc hCo.le hLoc.le hQuad.le hMart.le hCross
  obtain ⟨Cl, hCl, nl, _, hprofile⟩ :=
    hprofile hd hε hεd K hc hCo.le hLoc.le hQuad.le hMart.le hCross
  let N := max (max np ni) (max no nl)
  let C := Ci + Co + Cl + Cp + (N : ℝ) ^ ps
  have hNpow : 0 ≤ (N : ℝ) ^ ps := Real.rpow_nonneg (Nat.cast_nonneg N) ps
  have hC : 0 < C := by dsimp only [C]; positivity
  have hiC : Ci ≤ C := by dsimp only [C]; linarith
  have hoC : Co ≤ C := by dsimp only [C]; linarith
  have hlC : Cl ≤ C := by dsimp only [C]; linarith
  have hpC : Cp ≤ C := by dsimp only [C]; linarith
  have htail : ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ n : ℕ, 2 ≤ n → μ {ω | ¬ fluctuation_good ε C (X · ω) n} ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (-ps)) := by
    intro Ω _ μ _ X hX n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    by_cases hNn : N ≤ n
    · have hXd := (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX
      have hsub : ∀ x : Site d, x ≠ 0 →
          IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
            (toSpace x) (unitDir (toSpace x)) := by
        intro x hx
        exact isSubgradient_unitDir fun h => hx (eq_zero_of_toSpace_eq_zero h)
      have hbad : μ {ω | ¬ fluctuation_good ε C (X · ω) n} ≤
          μ (section5Event (fun v => ‖v‖) ε (fun x => unitDir (toSpace x)) K X n)ᶜ := by
        apply measure_mono_ae
        filter_upwards [ae_legal_of_isDriftCERW hXd] with ω hlegal
        intro hfail hgood
        apply hfail
        apply fluctuation_good_of_bounds hd hε hiC hoC hlC hn
        · exact hinner _ hsub unitDir_toSpace_zero _ n (by dsimp [N] at hNn; omega)
            hlegal hgood
        · exact houter _ hsub unitDir_toSpace_zero _ n (by dsimp [N] at hNn; omega)
            hlegal hgood
        · exact hprofile _ hsub unitDir_toSpace_zero _ n (by dsimp [N] at hNn; omega)
            hlegal hgood
      exact hbad.trans ((hprob μ X hX n (by dsimp [N] at hNn; omega)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpC
          (Real.rpow_nonneg hnpos.le _))))
    · apply prob_le_one.trans
      rw [ENNReal.one_le_ofReal]
      have hpow : 0 < (n : ℝ) ^ ps := Real.rpow_pos_of_pos hnpos ps
      have hle : (n : ℝ) ^ ps ≤ (N : ℝ) ^ ps :=
        Real.rpow_le_rpow hnpos.le (by exact_mod_cast (by omega : n ≤ N)) (by linarith)
      rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, le_div_iff₀ hpow, one_mul]
      dsimp only [C]
      linarith
  have hresult : (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ n : ℕ, 2 ≤ n → μ {ω | ¬ fluctuation_good ε C (X · ω) n} ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, fluctuation_good ε C (X · ω) n) := by
    constructor
    · intro Ω _ μ _ X hX n hn
      apply (htail μ X hX n hn).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (by omega : 1 ≤ n)) (by dsimp only [ps]; linarith)
    · intro Ω _ μ _ X hX
      exact ae_eventually_of_polynomial_bound μ
        (fun n ω => fluctuation_good ε C (X · ω) n) hps (htail μ X hX)
  refine ⟨C, hC, ?_⟩
  simpa only [fluctuation_good, CERW.Support.Outer.Radius.radius, unitBallVolume] using hresult

end CERW.LimitShapes.Curvature
