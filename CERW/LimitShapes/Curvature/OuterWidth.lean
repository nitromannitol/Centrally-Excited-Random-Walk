import CERW.LimitShapes.Curvature.OuterLocalTime
import CERW.LimitShapes.Curvature.Width
import CERW.LimitShapes.Profile

/-! # Outer width on the common event

The crossing estimate and Young absorption give `eq:outer-reduction`.
-/

namespace CERW.LimitShapes.Curvature

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.ContactEvent CERW.Support.Outer.Radius

/-- The width bound obtained by absorbing the exterior occupation term. -/
theorem exists_outer_width_on_event :
    ∀ {d : ℕ} (_hd : 2 ≤ d) {ε : ℝ}, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ K : CERW.LimitShapes.EventConstants,
        0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
      maxRadius X n + 2 * Real.sqrt d - innerRadius X n ≤
        C * (scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
          contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n) * Real.log n ^ d := by
  intro d hd ε hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨B, hB, Nb, hNb, hloc⟩ :=
    exists_exterior_localTime_on_event hd hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨A₀, C₀, _, _, Nd, hNd, hdata⟩ :=
    exists_annular_event_data hd hε hεd K hc hCo hLoc hQuad hMart
  obtain ⟨Ns, hNs, hs⟩ := Energy.exists_site_scale_threshold hd
    CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean hε
  let A := K.CCross + 2 * Real.sqrt d
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨C, hC, hwidth⟩ := exists_width_bound hd A B hA hB
  refine ⟨C, hC, max Nb (max Nd Ns), by omega, ?_⟩
  intro ξ hξ hξ0 X n hn hpath hev
  have hl := hloc ξ hξ hξ0 X n (by omega) hpath hev
  have hevu := hev
  rw [CERW.Support.Norm.Section5Localization.field_eq_unitDir hξ hξ0] at hevu
  obtain ⟨hb, _, _, hdelt, hw, _⟩ := hdata X n (by omega) hpath hevu
  have hlog := (hs n (by omega)).1
  have hcross := CERW.LimitShapes.Profile.crossOK_of_distance hev.2.2.2.2.2
  have hcros := hcross (innerRadius X n) hb.le
  dsimp only at hl hb hdelt hw ⊢
  let delta := scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
    contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
  let w := maxRadius X n + 2 * Real.sqrt d - innerRadius X n
  let Q := (delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) + delta
  have hd0 : 0 ≤ delta := by change 1 ≤ delta at hdelt; linarith
  have hq : 0 ≤ Q := add_nonneg (Real.rpow_nonneg (by positivity) _) hd0
  have hl' : (outerMax X n (innerRadius X n) : ℝ) ≤ B * Q := hl
  have hcros' : maxRadius X n ≤ innerRadius X n +
      K.CCross * (1 + B * Q) * Real.log n := by
    apply hcros.trans
    gcongr
  apply hwidth w delta (Real.log n) (by change 1 ≤ w at hw; linarith) hdelt hlog
  have hsqrt := Real.sqrt_nonneg (d : ℝ)
  have hextra : 2 * Real.sqrt d ≤ 2 * Real.sqrt d * (1 + B * Q) * Real.log n := by
    have h1 : 1 ≤ (1 + B * Q) * Real.log n := by
      nlinarith [mul_nonneg hB.le hq]
    nlinarith
  dsimp [w, A]
  nlinarith only [hcros', hextra]

end CERW.LimitShapes.Curvature
