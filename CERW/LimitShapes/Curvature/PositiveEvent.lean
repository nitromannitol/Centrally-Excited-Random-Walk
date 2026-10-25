module

public import CERW.LimitShapes.Curvature.EventData
public import CERW.LimitShapes.Curvature.Global
public import CERW.LimitShapes.Curvature.PositiveBound

@[expose] public section

/-! # Positive potential on the common event

The global curvature estimate gives the positive bound of `eq:positive-bound`.
-/

namespace CERW.LimitShapes.Curvature

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.ContactEvent

/-- The positive potential bound of `eq:positive-bound` on the actual common event. -/
theorem exists_positive_on_event :
    ∀ {d : ℕ} (_hd : 2 ≤ d) {ε : ℝ}, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ K : CERW.LimitShapes.EventConstants,
        0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
      let r := scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
      let delta := r * contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
      let b := CERW.innerRadius X n
      let R := CERW.maxRadius X n + 2 * Real.sqrt d
      let E := CERW.cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b
      ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ R →
        positivePotential d ε E y ≤
          C * ((delta * (R - b) ^ (d - 1)) ^ ((1 : ℝ) / d) + delta) := by
  intro d hd ε hε hεd K hc hCo hLoc hQuad hMart _hCross
  obtain ⟨A, C, hA, hC, N, hN, hdata⟩ :=
    exists_annular_event_data hd hε hεd K hc hCo hLoc hQuad hMart
  let F := (2 * A) ^ d * (C + unitBallVolume d / (2 * ε) * C)
  let M := 1 + C + F
  have hvol := (unitBallVolume_pos d).le
  have hF : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg (pow_nonneg (by linarith) _) (by positivity)
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hCM : C ≤ M := by dsimp [M]; linarith
  have hFM : F ≤ M := by dsimp [M]; linarith
  obtain ⟨B, hB, hbound⟩ := exists_annulus_positive_bound hd hε A M hA hM
  refine ⟨B, hB, N, hN, ?_⟩
  intro ξ hξ hξ0 X n hn hpath hev
  rw [CERW.Support.Norm.Section5Localization.field_eq_unitDir hξ hξ0] at hev
  obtain ⟨hb, _, _, hdelt, hw, hbR, hRA, hband, hmass, hpot⟩ :=
    hdata X n hn hpath hev
  dsimp only at hb hdelt hw hbR hRA hband hmass hpot ⊢
  let delta := scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
    contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
  let b := innerRadius X n
  let R := maxRadius X n + 2 * Real.sqrt d
  let E := cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b
  have hd0 : 0 ≤ delta := by change 1 ≤ delta at hdelt; linarith
  have hlow : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
      -(C * delta) ≤ potential d ε E y := by
    intro y hy
    have hp := hpot y hy
    have hl := cellLocalTime_nonneg X n y
    change cellLocalTime X n y / 2 - C * delta ≤ potential d ε E y at hp
    linarith
  have hEm := (annular_measurable_band (by omega : 1 ≤ d) X n).1
  have hcurv := curvatureIntegral_le_global hd hε hb hbR hA hRA
    (mul_nonneg hC.le hd0) (mul_nonneg hC.le hd0) hEm hband hmass hlow
  have hcurv' : ∀ y : EuclideanSpace ℝ (Fin d), curvatureIntegral E y ≤ M * delta := by
    intro y
    calc
      _ ≤ (2 * A) ^ d *
          (C * delta + unitBallVolume d / (2 * ε) * (C * delta)) := hcurv y
      _ = F * delta := by dsimp [F]; ring
      _ ≤ M * delta := mul_le_mul_of_nonneg_right hFM hd0
  intro y hy hyR
  apply hbound b (R - b) delta hb hw (by dsimp [b, R] at *; linarith) hdelt E hEm
  · intro v hv
    obtain ⟨hv1, hv2⟩ := hband v hv
    exact ⟨hv1, by dsimp [b, R] at *; linarith⟩
  · exact hmass.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCM hd0) (pow_nonneg hb.le _))
  · exact hcurv'
  · intro y hy
    simpa only [neg_mul] using
      (neg_le_neg (mul_le_mul_of_nonneg_right hCM hd0)).trans (hlow y hy)

  · exact hy
  · dsimp [b, R] at *
    linarith

end CERW.LimitShapes.Curvature
