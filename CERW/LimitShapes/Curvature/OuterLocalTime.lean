module

public import CERW.LimitShapes.Curvature.PositiveEvent
public import CERW.Support.Outer.Radius.PotentialConvolution
public import CERW.Support.Outer.Radius.PathBounds

@[expose] public section

/-! # Exterior occupation on the common event

The positive potential bounds the actual exterior local-time supremum in
`eq:outer-reduction`.
-/

namespace CERW.LimitShapes.Curvature

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.ContactEvent CERW.Support.Outer.Radius

/-- The exterior local-time supremum satisfies the bound used in `eq:outer-reduction`. -/
theorem exists_exterior_localTime_on_event {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) (K : CERW.LimitShapes.EventConstants)
    (hc : 0 < K.cCo) (hCo : 0 ≤ K.CCo) (hLoc : 0 ≤ K.CLoc)
    (hQuad : 0 ≤ K.CQuad) (hMart : 0 ≤ K.CMart) (hCross : 0 < K.CCross) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), N ≤ n → PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
      let delta := scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
        contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
      let w := maxRadius X n + 2 * Real.sqrt d - innerRadius X n
      (outerMax X n (innerRadius X n) : ℝ) ≤
        B * ((delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) + delta) := by
  obtain ⟨P, hP, Np, hNp, hp⟩ :=
    exists_positive_on_event hd hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨A, C, _, hC, Nd, hNd, hdta⟩ :=
    exists_annular_event_data hd hε hεd K hc hCo hLoc hQuad hMart
  refine ⟨2 * (P + C), by positivity, max Np Nd, by omega, ?_⟩
  intro ξ hξ hξ0 X n hn hpath hev
  have hpos := hp ξ hξ hξ0 X n (by omega) hpath hev
  have hevu := hev
  rw [CERW.Support.Norm.Section5Localization.field_eq_unitDir hξ hξ0] at hevu
  obtain ⟨hb, _, _, hdelt, hw, _, _, _, _, hpot⟩ :=
    hdta X n (by omega) hpath hevu
  dsimp only at hpos hb hdelt hw hpot ⊢
  let delta := scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
    contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
  let w := maxRadius X n + 2 * Real.sqrt d - innerRadius X n
  let E := cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius X n)
  let Q := (delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) + delta
  have hd0 : 0 ≤ delta := by change 1 ≤ delta at hdelt; linarith
  have hq : 0 ≤ Q := add_nonneg (Real.rpow_nonneg (by positivity) _) hd0
  have hdelq : delta ≤ Q := by
    dsimp [Q]
    linarith [Real.rpow_nonneg (show 0 ≤ delta * w ^ (d - 1) by positivity)
      ((1 : ℝ) / d)]
  have hEm := (annular_measurable_band (by omega : 1 ≤ d) X n).1
  have hEfin : volume E ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (Set.sdiff_subset.trans
      (CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ d) X n))).trans_lt
        (measure_ball_lt_top)
  have hsite : ∀ z ∈ departureRange X n, innerRadius X n ≤ euclidNorm z →
      (localTime X n z : ℝ) ≤ 2 * (P + C) * Q := by
    intro z hz hzb
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hz
    have hzR : ‖toSpace z‖ ≤ maxRadius X n + 2 * Real.sqrt d := by
      rw [norm_toSpace, ← hjz]
      exact (euclidNorm_le_maxRadius X (Finset.mem_range.mp hj).le).trans
        (le_add_of_nonneg_right (by positivity))
    have hzb' : innerRadius X n ≤ ‖toSpace z‖ := by rwa [norm_toSpace]
    have hl := hpot (toSpace z) hzb'
    rw [cellLocalTime_of_mem_cell X n (toSpace_mem_cell z)] at hl
    have hu := (ev_potential_le_positivePotential (by omega) hε.le hEm hEfin
      (toSpace z)).trans (hpos (toSpace z) hzb' hzR)
    change potential d ε E (toSpace z) ≤ P * Q at hu
    change (localTime X n z : ℝ) / 2 - C * delta ≤ potential d ε E (toSpace z) at hl
    nlinarith [mul_le_mul_of_nonneg_left hdelq hC.le]
  have hsup : outerMax X n (innerRadius X n) ≤ ⌊2 * (P + C) * Q⌋₊ := by
    classical
    apply Finset.sup_le
    intro z hz
    obtain ⟨hz, hzb⟩ := Finset.mem_filter.mp hz
    exact Nat.le_floor (hsite z hz hzb)
  exact (Nat.cast_le.mpr hsup).trans (Nat.floor_le (by positivity))

end CERW.LimitShapes.Curvature
