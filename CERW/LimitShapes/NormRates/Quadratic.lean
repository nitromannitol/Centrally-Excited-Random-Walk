module

public import CERW.LimitShapes.Frozen.NormBallPotential
public import CERW.LimitShapes.EventConsequences
public import CERW.Support.Norm.NormGaugeConsequences
public import CERW.Support.Norm.ShapeRates

@[expose] public section

/-!
# Quadratic comparison of radius and volume

The quadratic identity of Proposition `prop:norm-shape` compares the norm integral
with elapsed time on the actual stopped quadratic event. Cell errors and the
excess outside the inner ball give the radius-volume comparison.
-/

open MeasureTheory Topology
open LatticeProb (Site euclidNorm)
open CERW CERW.Support.Norm
open CERW.Support.Norm.ContactEvent (scale PathTyping quadraticMartingale)
open private integral_normSublevel_self measurableSet_normSublevel
  inradius_facts ball_subset_cellSet from CERW.Support.Norm.ShapeRates

namespace CERW.LimitShapes.NormRates

/-- Integrating a norm over the occupied cells changes its lattice sum by a cell error. -/
theorem abs_integral_cellSet_sub_sum {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (X : ℕ → Site d) (n : ℕ) :
    |(∫ v in cellSet X n, Ψ v) - ∑ y ∈ departureRange X n, Ψ (toSpace y)| ≤
      normMax Ψ * (Real.sqrt d / 2) * (departureRange X n).card := by
  classical
  have hΛ : 0 ≤ normMax Ψ :=
    (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).1.le.trans
      (ContactAssembly.normMin_le_normMax hd hΨ)
  have hcont := CERW.Generic.Norm.norm_continuous hΨ
  have hcell (y : Site d) : IntegrableOn Ψ (cell y) :=
    (hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (toSpace y) (Real.sqrt d / 2))).mono_set (by
        intro v hv
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv)
  have herr (y : Site d) :
      |(∫ v in cell y, Ψ v) - Ψ (toSpace y)| ≤ normMax Ψ * (Real.sqrt d / 2) := by
    have hconst : ∫ _ in cell y, Ψ (toSpace y) = Ψ (toSpace y) := by
      simp [measureReal_def, CERW.Support.Occupation.volume_cell]
    rw [← hconst, ← integral_sub (hcell y)
      (integrableOn_const (by rw [CERW.Support.Occupation.volume_cell]; simp))]
    have hbound := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := cell y) (f := fun v => Ψ v - Ψ (toSpace y))
      (by rw [CERW.Support.Occupation.volume_cell]; simp)
      (fun v hv => by
        rw [Real.norm_eq_abs]
        exact (CERW.Generic.Norm.abs_sub_le hΨ v (toSpace y)).trans
          ((CERW.Generic.Norm.le_normMax_mul hΨ _).trans
            (mul_le_mul_of_nonneg_left
              (CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv) hΛ)))
    simpa [Real.norm_eq_abs, measureReal_def, CERW.Support.Occupation.volume_cell]
      using hbound
  rw [cellSet, integral_biUnion_finset (departureRange X n)
    (fun y _ => CERW.Support.Occupation.measurableSet_cell y)
    (fun y _ z _ hyz => cell_disjoint hyz) (fun y _ => hcell y),
    ← Finset.sum_sub_distrib]
  calc |∑ y ∈ departureRange X n, ((∫ v in cell y, Ψ v) - Ψ (toSpace y))|
      ≤ ∑ y ∈ departureRange X n, |(∫ v in cell y, Ψ v) - Ψ (toSpace y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ departureRange X n, normMax Ψ * (Real.sqrt d / 2) :=
      Finset.sum_le_sum fun y _ => herr y
    _ = _ := by simp [mul_comm]

/-- The actual quadratic event controls the norm integral, without integrating local time. -/
theorem abs_time_sub_integral_of_event {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x))
    {K : EventConstants} {X : ℕ → Site d} {n : ℕ} (hn : 0 < n)
    (hpath : PathTyping d X) (hE : EventEstimates Ψ ε ξ K X n) :
    |(n : ℝ) - 2 * ε * ∫ v in cellSet X n, Ψ v| ≤
      K.CQuad * scale d Ψ ε n * Real.sqrt (n * Real.log n) +
        (K.CCo * scale d Ψ ε n) ^ 2 +
        ε * normMax Ψ * Real.sqrt d * (departureRange X n).card := by
  have hr := scale_pos hd hΨ hε hn
  have hR := hE.1.2.2.2.2.2
  have hstop : stoppedQuadratic ε ξ ((K.CCo + 1) * scale d Ψ ε n) X n =
      quadraticMartingale d ε ξ X n := by
    apply stoppedQuadratic_eq
    intro j hj
    have := euclidNorm_le_maxRadius X (Nat.le_of_lt hj)
    linarith
  have hQ := hE.2.2.1
  rw [hstop] at hQ
  have hid := NormGaugeConsequences.sq_euclidNorm_eq_norm hΨ ε hξ hpath.1 hpath.2 n
  have hcell := abs_integral_cellSet_sub_sum hd hΨ X n
  have hx0 : 0 ≤ euclidNorm (X n) := LatticeProb.euclidNorm_nonneg _
  have hxR := (euclidNorm_le_maxRadius X (le_refl n)).trans hR
  have hsq : euclidNorm (X n) ^ 2 ≤ (K.CCo * scale d Ψ ε n) ^ 2 :=
    pow_le_pow_left₀ hx0 hxR 2
  have hsplit : (n : ℝ) - 2 * ε * ∫ v in cellSet X n, Ψ v =
      (euclidNorm (X n) ^ 2 - quadraticMartingale d ε ξ X n) -
        2 * ε * ((∫ v in cellSet X n, Ψ v) -
          ∑ y ∈ departureRange X n, Ψ (toSpace y)) := by linarith [hid]
  rw [hsplit]
  calc _ ≤ |euclidNorm (X n) ^ 2 - quadraticMartingale d ε ξ X n| +
      |2 * ε * ((∫ v in cellSet X n, Ψ v) -
        ∑ y ∈ departureRange X n, Ψ (toSpace y))| := abs_sub _ _
    _ ≤ euclidNorm (X n) ^ 2 + |quadraticMartingale d ε ξ X n| +
        2 * ε * |(∫ v in cellSet X n, Ψ v) -
          ∑ y ∈ departureRange X n, Ψ (toSpace y)| := by
      rw [abs_mul, abs_of_pos (mul_pos two_pos hε)]
      gcongr
      simpa only [abs_of_nonneg (sq_nonneg (euclidNorm (X n)))] using
        (abs_sub (euclidNorm (X n) ^ (2 : ℕ)) (quadraticMartingale d ε ξ X n))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcell (by positivity : 0 ≤ 2 * ε)]

/-- Splitting the norm integral at the inner ball gives the quadratic radius comparison. -/
theorem abs_time_sub_inner_ball_of_event {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x))
    {K : EventConstants} {X : ℕ → Site d} {n : ℕ} (hn : 0 < n)
    (hpath : PathTyping d X) (hE : EventEstimates Ψ ε ξ K X n)
    (hr : Real.sqrt d ≤ scale d Ψ ε n) :
    |(n : ℝ) - 2 * ε * (d * normBallVolume Ψ *
        normInnerRadius Ψ X n ^ (d + 1) / (d + 1))| ≤
      K.CQuad * scale d Ψ ε n * Real.sqrt (n * Real.log n) +
        (K.CCo * scale d Ψ ε n) ^ 2 +
        ε * normMax Ψ * Real.sqrt d * (departureRange X n).card +
        2 * ε * normMax Ψ * ((K.CCo + 1) * scale d Ψ ε n) *
          (volume (cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n})).toReal := by
  have hd1 : 1 ≤ d := by omega
  set D := cellSet X n
  set b := normInnerRadius Ψ X n
  set R := (K.CCo + 1) * scale d Ψ ε n
  set E := D \ {v | Ψ v < b}
  have hDR : D ⊆ Metric.ball 0 R :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 X n).trans
      (Metric.ball_subset_ball (by
        have hR := hE.1.2.2.2.2.2
        dsimp [R]
        linarith))
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDR
  have hDm : MeasurableSet D := CERW.Support.Occupation.measurableSet_cellSet X n
  have hEm : MeasurableSet E := hDm.diff (measurableSet_normSublevel hΨ b)
  obtain ⟨hb, hsub, _⟩ := inradius_facts hd1 hΨ hDb
    (ρ := 1 / 2) (by norm_num) (ball_subset_cellSet X n hpath.1 hn)
  change 0 < b at hb
  change {v | Ψ v < b} ⊆ D at hsub
  have hint : IntegrableOn Ψ D :=
    ((CERW.Generic.Norm.norm_continuous hΨ).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).mono_set
        (hDR.trans Metric.ball_subset_closedBall)
  have hsplit : (∫ v in D, Ψ v) =
      (∫ v in {v | Ψ v < b}, Ψ v) + ∫ v in E, Ψ v := by
    conv_lhs => rw [← Set.union_sdiff_cancel hsub]
    exact setIntegral_union Set.disjoint_sdiff_right hEm
      (hint.mono_set hsub) (hint.mono_set Set.sdiff_subset)
  have hball := integral_normSublevel_self hd hΨ
    CERW.LimitShapes.norm_ball_potential CERW.Support.Norm.norm_potential_geometry hb
  have hΛ : 0 ≤ normMax Ψ :=
    (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1).1.le.trans
      (ContactAssembly.normMin_le_normMax hd1 hΨ)
  have hEb : Bornology.IsBounded E := hDb.subset Set.sdiff_subset
  have hbound : |∫ v in E, Ψ v| ≤ normMax Ψ * R * (volume E).toReal := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := E) (f := Ψ)
      hEb.measure_lt_top (fun v hv => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg ((CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 v)]
        exact (CERW.Generic.Norm.le_normMax_mul hΨ v).trans
          (mul_le_mul_of_nonneg_left ((mem_ball_zero_iff.mp (hDR hv.1)).le) hΛ))
    simpa only [Real.norm_eq_abs, measureReal_def, mul_comm] using h
  have hmass := abs_time_sub_integral_of_event hd1 hΨ hε hξ hn hpath hE
  have heq : (n : ℝ) - 2 * ε * (d * normBallVolume Ψ * b ^ (d + 1) / (d + 1)) =
      ((n : ℝ) - 2 * ε * ∫ v in D, Ψ v) + 2 * ε * ∫ v in E, Ψ v := by
    rw [hsplit, hball]
    ring
  rw [heq]
  calc _ ≤ |(n : ℝ) - 2 * ε * ∫ v in D, Ψ v| + |2 * ε * ∫ v in E, Ψ v| :=
      abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_pos (mul_pos two_pos hε)]
      have hmul := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 2 * ε)
      nlinarith [hmul]

end CERW.LimitShapes.NormRates
