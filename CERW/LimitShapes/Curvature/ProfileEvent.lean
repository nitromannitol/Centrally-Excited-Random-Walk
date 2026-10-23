import CERW.LimitShapes.Curvature.ProfileApproximation
import CERW.LimitShapes.Curvature.ProfileScales

/-!
# The global profile on the common event

The positive annular potential and the width bound imply the profile estimate in
Theorem `thm:fluctuations` (iii), following `sec:global-profile`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory
open LatticeProb (Site)
open CERW.Support.Norm.ContactEvent

/-- The annular potential and width bounds imply the uniform global profile estimate. -/
theorem profile_on_event_of_bounds
    (hpositive : ∀ {d : ℕ} (_hd : 2 ≤ d) {ε : ℝ}, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ K : CERW.LimitShapes.EventConstants,
        0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
      let r := CERW.Support.Norm.ContactEvent.scale d
        (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
      let delta := r * CERW.Support.Norm.ContactEvent.contactRate d
        (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
      let b := CERW.innerRadius X n
      let R := CERW.maxRadius X n + 2 * Real.sqrt d
      let E := CERW.cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b
      ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ R →
        positivePotential d ε E y ≤
          C * ((delta * (R - b) ^ (d - 1)) ^ ((1 : ℝ) / d) + delta))
    (hwidth : ∀ {d : ℕ} (_hd : 2 ≤ d) {ε : ℝ}, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ K : CERW.LimitShapes.EventConstants,
        0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
      CERW.maxRadius X n + 2 * Real.sqrt d - CERW.innerRadius X n ≤
        C * (CERW.Support.Norm.ContactEvent.scale d
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
          CERW.Support.Norm.ContactEvent.contactRate d
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n) * Real.log n ^ d) :
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
      ∀ y : EuclideanSpace ℝ (Fin d),
        |CERW.cellLocalTime X n y - 2 * d * ε *
          max (CERW.Support.Outer.Radius.radius d ε n - ‖y‖) 0| ≤
          C * (if d = 2 then Real.sqrt (CERW.Support.Outer.Radius.radius d ε n) *
            Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (CERW.Support.Outer.Radius.radius d ε n * Real.log n)) := by
  intro d hd ε hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨B, hB, Np, hNp, hp⟩ :=
    hpositive hd hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨A, hA, Nw, hNw, hw⟩ :=
    hwidth hd hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨Ad, D, _, hD, Nd, hNd, he⟩ :=
    exists_annular_event_data hd hε hεd K hc hCo hLoc hQuad hMart
  obtain ⟨P, hP, hg⟩ := exists_global_potential_bound hd A B D hA hB hD.le
  obtain ⟨Ci, hCi, Ni, hNi, hi⟩ :=
    CERW.LimitShapes.inner_on_event hd hε hεd K hc hCo hLoc hQuad hMart
  obtain ⟨Ns, hNs, hs⟩ := exists_profile_scale_threshold hd hε
  obtain ⟨Nq, hNq, hq⟩ := exists_annular_scale_threshold hd hε
    (Ci := 2 * Ci) (hCi := by positivity)
  let C := K.CLoc + K.CLoc * Real.sqrt K.CCo + P + 2 * d * ε * Ci
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, max Np (max Nw (max Nd (max Ni (max Ns (max Nq d))))), by omega, ?_⟩
  intro ξ hξ hξ0 X n hn hpath hev y
  let Ψ := fun v : EuclideanSpace ℝ (Fin d) => ‖v‖
  let r := scale d Ψ ε n
  let delta := r * contactRate d Ψ ε n
  let L := Real.log n
  let S := if d = 2 then Real.sqrt r * L ^ ((3 : ℝ) / 2) else Real.sqrt (r * L)
  have hradius : CERW.Support.Outer.Radius.radius d ε n = r := by
    simp only [r, Ψ, scale, CERW.Support.Outer.Radius.radius,
      CERW.Support.Inner.normBallVolume_norm, unitBallVolume]
  rw [hradius]
  change |cellLocalTime X n y - 2 * d * ε * max (r - ‖y‖) 0| ≤ C * S
  have hcanonical := hev
  rw [CERW.Support.Norm.Section5Localization.field_eq_unitDir hξ hξ0] at hcanonical
  obtain ⟨hb, hhalf, _, hdelta, _, hbR, _, hband, _, hlower⟩ :=
    he X n (by omega) hpath hcanonical
  obtain ⟨hL, hpow⟩ := hs n (by omega)
  have hr : 0 < r := by
    have hone : 1 ≤ Real.log n ^ (2 * d) := one_le_pow₀ hL
    dsimp [r, Ψ]
    linarith
  have hds : delta = if d = 2 then Real.sqrt (r * L) else L :=
    Energy.scale_mul_contactRate Ψ ε n hr
  have hM := hev.1.2.2.2.1
  obtain ⟨hLS, hdS, hdpS, hMS⟩ := profile_scale_bounds hd hL hpow
    (Nat.cast_nonneg (maxLocalTime X n)) hCo hM
  change L ≤ S at hLS
  change (if d = 2 then Real.sqrt (r * L) else L) ≤ S at hdS
  rw [← hds] at hdS hdpS
  change delta * L ^ (d - 1) ≤ S at hdpS
  change (if d = 2 then Real.sqrt (maxLocalTime X n : ℝ) * L
    else Real.sqrt ((maxLocalTime X n : ℝ) * L)) ≤ Real.sqrt K.CCo * S at hMS
  have hS : 0 ≤ S := (by linarith : 0 ≤ L).trans hLS
  have hglo : ∀ z : EuclideanSpace ℝ (Fin d),
      |potential d ε (cellSet X n \ Metric.ball 0 (innerRadius X n)) z| ≤
        P * delta * L ^ (d - 1) := by
    apply hg ε (innerRadius X n) (maxRadius X n + 2 * Real.sqrt d) delta L
      hε hb hbR hdelta hL
      (hw ξ hξ hξ0 X n (by omega) hpath hev)
      _ (annular_measurable_band (by omega : 1 ≤ d) X n).1 hband
    · intro z hz
      have hl := hlower z hz
      have hnz := cellLocalTime_nonneg X n z
      change -D * delta ≤ _
      change cellLocalTime X n z / 2 - D * delta ≤ _ at hl
      linarith
    · exact hp ξ hξ hξ0 X n (by omega) hpath hev
  have hir := (hi ξ hξ hξ0 X n (by omega) hpath hev).1
  have hir' : |innerRadius X n - r| ≤ Ci * delta := by
    change |innerRadius X n - r| ≤ Ci * r * contactRate d Ψ ε n at hir
    simpa only [delta, mul_assoc] using hir
  by_cases hy : ‖y‖ ≤ 2 * (n : ℝ)
  · have hl := hev.2.1 y hy
    rw [CERW.Support.Inner.normPotential_norm_eq (by omega : 1 ≤ d)] at hl
    have herr := local_time_profile_error hd hε.le X n hb hir' hglo y hl
    have hlocal : K.CLoc * L + K.CLoc *
        (if d = 2 then Real.sqrt (maxLocalTime X n : ℝ) * L
          else Real.sqrt ((maxLocalTime X n : ℝ) * L)) ≤
        (K.CLoc + K.CLoc * Real.sqrt K.CCo) * S := by
      have h1 := mul_le_mul_of_nonneg_left hLS hLoc
      have h2 := mul_le_mul_of_nonneg_left hMS hLoc
      nlinarith only [h1, h2]
    have hpot : P * delta * L ^ (d - 1) ≤ P * S := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdpS hP.le
    have hin : 2 * (d : ℝ) * ε * (Ci * delta) ≤ (2 * d * ε * Ci) * S := by
      have := mul_le_mul_of_nonneg_left hdS
        (show 0 ≤ 2 * (d : ℝ) * ε * Ci by positivity)
      simpa only [mul_assoc] using this
    dsimp [C]
    change _ ≤ (K.CLoc + K.CLoc * Real.sqrt K.CCo + P + 2 * d * ε * Ci) * S
    exact herr.trans (by dsimp only [L] at hlocal; nlinarith only [hlocal, hpot, hin])
  · have hmax : maxRadius X n ≤ (n : ℝ) :=
      CERW.Support.Occupation.maxRadius_le_of_steps X hpath.1 hpath.2 n
    have hinner := CERW.Support.Outer.Radius.innerRadius_le (by omega : 1 ≤ d) X n
    have hsq : Real.sqrt (d : ℝ) ≤ (n : ℝ) := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      exact (Real.sqrt_le_self_iff.mpr (Or.inr hd1)).trans (by exact_mod_cast (show d ≤ n by omega))
    have hsmall : r ≤ 2 * (n : ℝ) := by
      have hqsmall := (hq n (by omega)).2.2
      change (2 * Ci) * contactRate d Ψ ε n ≤ 1 / 2 at hqsmall
      have he : Ci * r * contactRate d Ψ ε n ≤ r / 4 := by
        nlinarith [mul_le_mul_of_nonneg_left hqsmall hr.le]
      have he' : Ci * delta ≤ r / 4 := by
        simpa only [delta, mul_assoc] using he
      have hib : 3 * r / 4 ≤ innerRadius X n := by
        linarith only [(abs_le.mp hir').1, he']
      linarith only [hib, hinner, hmax, hsq]
    rw [local_time_profile_eq_zero (by omega : 1 ≤ d) X n
      (by linarith : maxRadius X n + Real.sqrt d ≤ 2 * (n : ℝ)) hsmall y
      (lt_of_not_ge hy) (2 * d * ε)]
    exact mul_nonneg hC.le hS

end CERW.LimitShapes.Curvature
