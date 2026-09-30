import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The measure of a spherical cap

A cap of angular radius `ε ≤ 1` on the unit sphere of `ℝ^d` has surface measure at least
`c_d ε^{d-1}`, the sharp order. (Mathlib's general bound has order `ε^d`.) The cone over the cap
inside the unit ball contains a box that is long in the radial direction and has width of order
`ε` in the other `d - 1` directions. A reflection moves the pole `e_0` to any point of the sphere.
This is the cap estimate behind `eq:cap-average`.
-/

namespace CERW.Generic.Newton

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- The Lebesgue measure of the box `{v | 1/2 < v 0 < 3/4, |v i| < a (i ≠ 0)}` in `ℝ^{n+1}` is
`(1/4) (2 a)^n`. -/
private lemma volume_box_eq {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    volume {v : EuclideanSpace ℝ (Fin (n + 1)) |
        1 / 2 < v 0 ∧ v 0 < 3 / 4 ∧ ∀ i, i ≠ 0 → |v i| < a}
      = ENNReal.ofReal (1 / 4 * (2 * a) ^ n) := by
  let lo : Fin (n + 1) → ℝ := fun i => if i = 0 then 1 / 2 else -a
  let hi : Fin (n + 1) → ℝ := fun i => if i = 0 then 3 / 4 else a
  let P : Set (Fin (n + 1) → ℝ) := Set.univ.pi fun i => Set.Ioo (lo i) (hi i)
  have hset : {v : EuclideanSpace ℝ (Fin (n + 1)) |
        1 / 2 < v 0 ∧ v 0 < 3 / 4 ∧ ∀ i, i ≠ 0 → |v i| < a}
      = WithLp.ofLp ⁻¹' P := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_preimage, P, Set.mem_univ_pi, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2, h3⟩ i
      by_cases hi0 : i = 0
      · subst hi0
        simp only [lo, hi, if_true]
        exact ⟨h1, h2⟩
      · simp only [lo, hi, if_neg hi0]
        exact abs_lt.mp (h3 i hi0)
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · simpa only [lo, hi, if_true] using (h 0).1
      · simpa only [lo, hi, if_true] using (h 0).2
      · intro i hi0
        have hlo : lo i < v i := (h i).1
        have hhi : v i < hi i := (h i).2
        simp only [lo, hi, if_neg hi0] at hlo hhi
        exact abs_lt.mpr ⟨hlo, hhi⟩
  rw [hset]
  rw [(PiLp.volume_preserving_ofLp (Fin (n + 1))).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ioo).nullMeasurableSet]
  rw [Real.volume_pi_Ioo, Fin.prod_univ_succ]
  have h0 : ENNReal.ofReal (hi 0 - lo 0) = ENNReal.ofReal (1 / 4) := by norm_num [lo, hi]
  have h2a : ∀ i : Fin n, hi i.succ - lo i.succ = 2 * a := by
    intro i
    have hne : (i.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero i
    simp only [lo, hi, hne, if_false]
    ring
  have hn : ∏ i : Fin n, ENNReal.ofReal (hi i.succ - lo i.succ) = ENNReal.ofReal (2 * a) ^ n := by
    rw [Finset.prod_congr rfl (fun i _ => by rw [h2a i]), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [h0, hn, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 2 * a),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 4)]

/-- A reflection carries the box `B` into the cone over the spherical cap of radius `ε`. -/
private lemma reflection_image_box_subset_cone {n : ℕ} {ε a : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ha : a = ε / (4 * Real.sqrt (n + 1)))
    (θ₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Submodule.reflection
        (ℝ ∙ (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) -
          (θ₀ : EuclideanSpace ℝ (Fin (n + 1)))))ᗮ ''
      {v : EuclideanSpace ℝ (Fin (n + 1)) |
        1 / 2 < v 0 ∧ v 0 < 3 / 4 ∧ ∀ i, i ≠ 0 → |v i| < a}
    ⊆ Set.Ioo (0 : ℝ) 1 • ((↑) '' Metric.ball θ₀ ε) := by
  set e0 : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1 with he0
  set R : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    Submodule.reflection (ℝ ∙ (e0 - (θ₀ : EuclideanSpace ℝ (Fin (n + 1)))))ᗮ with hR
  set B : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {v | 1 / 2 < v 0 ∧ v 0 < 3 / 4 ∧ ∀ i, i ≠ 0 → |v i| < a} with hB
  set cone : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    Set.Ioo (0 : ℝ) 1 • ((↑) '' Metric.ball θ₀ ε) with hcone
  have ha_nonneg : 0 ≤ a := by rw [ha]; positivity
  have hθnorm : ‖(θ₀ : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    have hmem := θ₀.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hmem
    exact hmem
  have hRe0 : R e0 = (θ₀ : EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [hR]
    refine Submodule.reflection_sub ?_
    simp [he0, hθnorm]
  have hsub : R '' B ⊆ cone := by
    rw [hcone]
    rintro y ⟨v, hvB, rfl⟩
    rw [hB] at hvB
    obtain ⟨hv1, hv2, hv3⟩ := hvB
    have hv0pos : 0 < v 0 := by linarith
    have hv_ne : v ≠ 0 := by
      intro h
      have := hv1
      rw [h] at this
      norm_num at this
    have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    have hv_norm_ne : ‖v‖ ≠ 0 := ne_of_gt hv_norm_pos
    set w : EuclideanSpace ℝ (Fin (n + 1)) := v - (v 0) • e0 with hw
    have hw0 : w 0 = 0 := by rw [hw]; simp [he0]
    have hw_sq : ‖w‖ ^ 2 = ∑ i : Fin n, (v i.succ) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      rw [show w 0 ^ 2 = 0 by rw [hw0]; ring, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      have hne : (i.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero i
      rw [hw]
      simp [he0, hne]
    have hv_sq : ‖v‖ ^ 2 = (v 0) ^ 2 + ∑ i : Fin n, (v i.succ) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    have hsum_le : ∑ i : Fin n, (v i.succ) ^ 2 ≤ (n : ℝ) * a ^ 2 := by
      calc ∑ i : Fin n, (v i.succ) ^ 2 ≤ ∑ _i : Fin n, a ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hne : (i.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero i
            have hx := hv3 i.succ hne
            have hlt : (v i.succ) ^ 2 < a ^ 2 := by
              apply sq_lt_sq.mpr
              rwa [abs_of_nonneg ha_nonneg]
            exact hlt.le
        _ = (n : ℝ) * a ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hw_sq_lt : ‖w‖ ^ 2 < ((n : ℝ) + 1) * a ^ 2 := by
      rw [hw_sq]
      calc ∑ i : Fin n, (v i.succ) ^ 2 ≤ (n : ℝ) * a ^ 2 := hsum_le
        _ < ((n : ℝ) + 1) * a ^ 2 := by
            have ha2 : 0 < a ^ 2 := by rw [ha]; positivity
            nlinarith
    have hw_norm_lt : ‖w‖ < ε / 4 := by
      have hsq : ‖w‖ ^ 2 < (ε / 4) ^ 2 := by
        calc ‖w‖ ^ 2 < ((n : ℝ) + 1) * a ^ 2 := hw_sq_lt
          _ = (ε / 4) ^ 2 := by
              rw [ha, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
              field_simp
      have := sq_lt_sq.mp hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : (0:ℝ) ≤ ε/4)] at this
    have hv_gt : 1 / 2 < ‖v‖ := by
      have hsq : (1 / 2 : ℝ) ^ 2 < ‖v‖ ^ 2 := by
        rw [hv_sq]
        have h20 : (1 / 2 : ℝ) ^ 2 < (v 0) ^ 2 := by nlinarith
        nlinarith [sq_nonneg (∑ i : Fin n, (v i.succ) ^ 2)]
      have := sq_lt_sq.mp hsq
      rwa [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), abs_of_nonneg (norm_nonneg _)] at this
    have hv_lt : ‖v‖ < 1 := by
      have hdecomp : v = (v 0) • e0 + w := by rw [hw]; module
      calc ‖v‖ = ‖(v 0) • e0 + w‖ := by conv_lhs => rw [hdecomp]
        _ ≤ ‖(v 0) • e0‖ + ‖w‖ := norm_add_le _ _
        _ = |v 0| + ‖w‖ := by
            rw [show ‖(v 0) • e0‖ = |v 0| by simp [norm_smul, he0]]
        _ = v 0 + ‖w‖ := by rw [abs_of_pos hv0pos]
        _ < 3 / 4 + ε / 4 := by linarith
        _ ≤ 1 := by linarith
    have hdist : dist (R (‖v‖⁻¹ • v)) (θ₀ : EuclideanSpace ℝ (Fin (n + 1))) < ε := by
      rw [← hRe0, LinearIsometryEquiv.dist_map, dist_eq_norm]
      have h1 : ‖v‖⁻¹ • v - e0 = ‖v‖⁻¹ • (v - ‖v‖ • e0) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hv_norm_ne, one_smul]
      rw [h1, norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖⁻¹)]
      have h2 : ‖v - ‖v‖ • e0‖ ≤ 2 * ‖w‖ := by
        have hdecomp2 : v - ‖v‖ • e0 = w + (v 0 - ‖v‖) • e0 := by rw [hw]; module
        calc ‖v - ‖v‖ • e0‖ = ‖w + (v 0 - ‖v‖) • e0‖ := by rw [hdecomp2]
          _ ≤ ‖w‖ + ‖(v 0 - ‖v‖) • e0‖ := norm_add_le _ _
          _ = ‖w‖ + |v 0 - ‖v‖| := by
              rw [show ‖(v 0 - ‖v‖) • e0‖ = |v 0 - ‖v‖| by simp [norm_smul, he0]]
          _ ≤ ‖w‖ + ‖w‖ := by
              have hb := abs_norm_sub_norm_le v ((v 0) • e0)
              have hv0e0 : ‖(v 0) • e0‖ = v 0 := by simp [norm_smul, he0, abs_of_pos hv0pos]
              rw [hv0e0, ← hw] at hb
              have : |v 0 - ‖v‖| ≤ ‖w‖ := by simpa [abs_sub_comm] using hb
              linarith
          _ = 2 * ‖w‖ := by ring
      have h3 : ‖v‖⁻¹ * (2 * ‖w‖) < ε := by
        have hinv : ‖v‖⁻¹ < 2 := by
          calc ‖v‖⁻¹ = 1 / ‖v‖ := by rw [one_div]
            _ < 1 / (1 / 2 : ℝ) := one_div_lt_one_div_of_lt (by norm_num) hv_gt
            _ = 2 := by norm_num
        calc ‖v‖⁻¹ * (2 * ‖w‖) ≤ 2 * (2 * ‖w‖) := by gcongr
          _ = 4 * ‖w‖ := by ring
          _ < ε := by linarith
      calc ‖v‖⁻¹ * ‖v - ‖v‖ • e0‖ ≤ ‖v‖⁻¹ * (2 * ‖w‖) := by gcongr
        _ < ε := h3
    rw [← Set.image2_smul, Set.mem_image2]
    refine ⟨‖v‖, ⟨hv_norm_pos, hv_lt⟩, R (‖v‖⁻¹ • v), ?_, ?_⟩
    · refine ⟨⟨R (‖v‖⁻¹ • v), ?_⟩, ?_, rfl⟩
      · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, LinearIsometryEquiv.norm_map, norm_smul,
          Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hv_norm_pos)), inv_mul_cancel₀ hv_norm_ne]
      · rw [Metric.mem_ball, Subtype.dist_eq]; exact hdist
    · rw [← LinearIsometryEquiv.map_smul, smul_smul, mul_inv_cancel₀ hv_norm_ne, one_smul]
  exact hsub

/-- A spherical cap of angular radius `ε ∈ (0, 1]` has measure at least
`(d/4) (ε/(4√d))^{d-1}`. -/
theorem le_toSphere_ball (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (θ₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    (d : ℝ) / 4 * (ε / (4 * Real.sqrt d)) ^ (d - 1) ≤
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere (Metric.ball θ₀ ε)).toReal := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hd
  set a : ℝ := ε / (4 * Real.sqrt (n + 1)) with ha
  set e0 : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1 with he0
  set R : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    Submodule.reflection (ℝ ∙ (e0 - (θ₀ : EuclideanSpace ℝ (Fin (n + 1)))))ᗮ with hR
  set B : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {v | 1 / 2 < v 0 ∧ v 0 < 3 / 4 ∧ ∀ i, i ≠ 0 → |v i| < a} with hB
  set cone : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    Set.Ioo (0 : ℝ) 1 • ((↑) '' Metric.ball θ₀ ε) with hcone
  have ha_nonneg : 0 ≤ a := by rw [ha]; positivity
  have hsub : R '' B ⊆ cone := by
    rw [hR, he0, hB, hcone]
    exact reflection_image_box_subset_cone (n := n) (ε := ε) (a := a) hε hε1 ha θ₀
  have hB_meas : MeasurableSet B := by
    rw [hB]; measurability
  have hvolB : volume B = ENNReal.ofReal (1 / 4 * (2 * a) ^ n) := by
    rw [hB]; exact volume_box_eq ha_nonneg
  have hvolR : volume (R '' B) = volume B := by
    rw [LinearIsometryEquiv.image_eq_preimage_symm]
    exact (LinearIsometryEquiv.measurePreserving R.symm).measure_preimage hB_meas.nullMeasurableSet
  have hle : ENNReal.ofReal (1 / 4 * (2 * a) ^ n) ≤ volume cone := by
    rw [← hvolB, ← hvolR]
    exact measure_mono hsub
  have htoSphere : (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        (Metric.ball θ₀ ε)
      = ((n + 1 : ℕ) : ℝ≥0∞) * volume cone := by
    rw [MeasureTheory.Measure.toSphere_apply' volume measurableSet_ball, finrank_euclideanSpace_fin]
  have hge : ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 4 * (2 * a) ^ n) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere (Metric.ball θ₀ ε) := by
    rw [htoSphere]
    exact mul_le_mul_right hle _
  have h2a_eq : 2 * a = ε / (2 * Real.sqrt (n + 1)) := by
    rw [ha]; field_simp; ring
  have hc' : ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 4 * (2 * a) ^ n)
      = ENNReal.ofReal (((n + 1 : ℝ) / 4) * (ε / (2 * Real.sqrt (n + 1))) ^ n) := by
    rw [← ENNReal.ofReal_natCast (n + 1),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
    congr 1
    rw [show ((n + 1 : ℕ) : ℝ) * (1 / 4 * (2 * a) ^ n)
        = ((n + 1 : ℕ) : ℝ) / 4 * (2 * a) ^ n by ring, h2a_eq]
    simp only [Nat.cast_add, Nat.cast_one]
  have hbase_le : ε / (4 * Real.sqrt (n + 1)) ≤ ε / (2 * Real.sqrt (n + 1)) := by
    apply div_le_div_of_nonneg_left hε.le
    · positivity
    · nlinarith [Real.sqrt_nonneg (n + 1 : ℝ)]
  have hpow_le : (ε / (4 * Real.sqrt (n + 1))) ^ n ≤ (ε / (2 * Real.sqrt (n + 1))) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase_le n
  have hc_le : ((n + 1 : ℝ) / 4) * (ε / (4 * Real.sqrt (n + 1))) ^ n ≤
      ((n + 1 : ℝ) / 4) * (ε / (2 * Real.sqrt (n + 1))) ^ n :=
    mul_le_mul_of_nonneg_left hpow_le (by positivity)
  have hfinal : ENNReal.ofReal (((n + 1 : ℝ) / 4) * (ε / (4 * Real.sqrt (n + 1))) ^ n) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere (Metric.ball θ₀ ε) :=
    (ENNReal.ofReal_le_ofReal hc_le).trans (hc' ▸ hge)
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
      (Metric.ball θ₀ ε) ≠ ⊤ :=
    ne_top_of_le_ne_top (MeasureTheory.measure_lt_top _ _).ne (measure_mono (Set.subset_univ _))
  have hres := ENNReal.toReal_mono hfin hfinal
  rw [ENNReal.toReal_ofReal (by positivity)] at hres
  simpa using hres

end CERW.Generic.Newton
