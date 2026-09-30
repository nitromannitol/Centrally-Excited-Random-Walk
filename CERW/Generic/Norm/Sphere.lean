import CERW.Generic.Norm.Basic

/-!
# A norm on the Euclidean unit sphere

A norm is continuous, and on the Euclidean unit sphere it attains its largest value
`Λ_Ψ = normMax Ψ` and its least value `c_Ψ = normMin Ψ > 0`; by homogeneity
`c_Ψ |x| ≤ Ψ(x) ≤ Λ_Ψ |x|`.
-/

namespace CERW.Generic.Norm

open CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A norm on `ℝ^d` is continuous. -/
theorem norm_continuous (hΨ : IsNorm Ψ) : Continuous Ψ := by
  have hnonneg : ∀ x, 0 ≤ Ψ x := (map_zero_nonneg_neg hΨ).2.1
  have hcoord : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d), |x i| ≤ ‖x‖ := by
    intro x i
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  refine (LipschitzWith.of_dist_le' (K := ∑ i, Ψ (coordVec i)) fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  calc |Ψ x - Ψ y| ≤ Ψ (x - y) := abs_sub_le hΨ x y
    _ ≤ ∑ i, |(x - y) i| * Ψ (coordVec i) := le_sum_coord hΨ (x - y)
    _ ≤ ∑ i, ‖x - y‖ * Ψ (coordVec i) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hcoord (x - y) i) (hnonneg _)
    _ = ‖x - y‖ * ∑ i, Ψ (coordVec i) := by rw [Finset.mul_sum]
    _ = (∑ i, Ψ (coordVec i)) * ‖x - y‖ := by ring

/-- The image of the Euclidean unit sphere under a norm is bounded above. -/
private lemma norm_image_bddAbove (hΨ : IsNorm Ψ) :
    BddAbove (Ψ '' Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).bddAbove_image
    (norm_continuous hΨ).continuousOn

/-- `Ψ(x) ≤ Λ_Ψ |x|`. -/
theorem le_normMax_mul (hΨ : IsNorm Ψ) (x : EuclideanSpace ℝ (Fin d)) :
    Ψ x ≤ normMax Ψ * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [(map_zero_nonneg_neg hΨ).1]
  · have hbdd : BddAbove (Ψ '' Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      norm_image_bddAbove hΨ
    have hnormx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    set u : EuclideanSpace ℝ (Fin d) := ‖x‖⁻¹ • x with hu
    have hnorm_u : ‖u‖ = 1 := by
      rw [hu, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x)]
      exact inv_mul_cancel₀ hnormx
    have hu_mem : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact hnorm_u
    have hmax : Ψ u ≤ normMax Ψ :=
      le_csSup hbdd (Set.mem_image_of_mem Ψ hu_mem)
    have hxu : Ψ x = ‖x‖ * Ψ u := by
      have hxsmul : x = ‖x‖ • u := by
        rw [hu, smul_inv_smul₀ hnormx]
      conv_lhs => rw [hxsmul]
      rw [hΨ.smul, abs_of_nonneg (norm_nonneg x)]
    calc Ψ x = ‖x‖ * Ψ u := hxu
      _ ≤ ‖x‖ * normMax Ψ := mul_le_mul_of_nonneg_left hmax (norm_nonneg x)
      _ = normMax Ψ * ‖x‖ := by ring

/-- `c_Ψ > 0` and `c_Ψ |x| ≤ Ψ(x)`. -/
theorem normMin_pos_mul_le (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 < normMin Ψ ∧ ∀ x : EuclideanSpace ℝ (Fin d), normMin Ψ * ‖x‖ ≤ Ψ x := by
  have hd0 : 0 < d := by omega
  have hmem : coordVec (⟨0, hd0⟩ : Fin d) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    simp [coordVec, PiLp.norm_single]
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty := ⟨_, hmem⟩
  have hbddBelow : BddBelow (Ψ '' Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).bddBelow_image
      (norm_continuous hΨ).continuousOn
  obtain ⟨u, hu_mem, hu_min⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).exists_isMinOn hne
      (norm_continuous hΨ).continuousOn
  have hle : Ψ u ≤ normMin Ψ :=
    le_csInf (hne.image Ψ) fun b hb => by
      obtain ⟨v, hv, hvb⟩ := hb
      rw [← hvb]
      exact hu_min hv
  have hge : normMin Ψ ≤ Ψ u :=
    csInf_le hbddBelow (Set.mem_image_of_mem Ψ hu_mem)
  have hmin_eq : normMin Ψ = Ψ u := le_antisymm hge hle
  have hpos : 0 < normMin Ψ := by
    rw [hmin_eq]
    refine lt_of_le_of_ne ((map_zero_nonneg_neg hΨ).2.1 u) ?_
    intro hzero
    have hu0 : u = 0 := hΨ.eq_zero u hzero.symm
    rw [hu0, Metric.mem_sphere, dist_self] at hu_mem
    exact zero_ne_one hu_mem
  refine ⟨hpos, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [(map_zero_nonneg_neg hΨ).1]
  · have hnormx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    set u' : EuclideanSpace ℝ (Fin d) := ‖x‖⁻¹ • x with hu'
    have hnorm_u : ‖u'‖ = 1 := by
      rw [hu', norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x)]
      exact inv_mul_cancel₀ hnormx
    have hu'_mem : u' ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact hnorm_u
    have hle_u : normMin Ψ ≤ Ψ u' := by
      rw [hmin_eq]
      exact hu_min hu'_mem
    have hxu : Ψ x = ‖x‖ * Ψ u' := by
      have hxsmul : x = ‖x‖ • u' := by
        rw [hu', smul_inv_smul₀ hnormx]
      conv_lhs => rw [hxsmul]
      rw [hΨ.smul, abs_of_nonneg (norm_nonneg x)]
    calc normMin Ψ * ‖x‖ ≤ Ψ u' * ‖x‖ :=
          mul_le_mul_of_nonneg_right hle_u (norm_nonneg x)
      _ = ‖x‖ * Ψ u' := by ring
      _ = Ψ x := hxu.symm

end CERW.Generic.Norm
