import CERW.Support.Occupation.CellWeight
import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Geometry.TailBasic

/-!
# The tail beyond a radius is controlled by the source sum

In `eq:radial-source`, the left side `Σ_{x ∈ A_n, |x| > r + 3} |x|^{1-d}` bounds a positive multiple
of `F(r + b)`. Every point of `D_n` with `|v| > r + b` lies in the cell of a departure site `x`
with `|x| > r + b - √d/2 > r + 3`. The weighted integral of that cell is at most
`2^{d-1} |x|^{1-d}`.
-/

namespace CERW.Support.Coarse

open MeasureTheory LatticeProb CERW CERW.Support.Occupation

variable {d : ℕ}

/-- If `v` lies in the cell of `x`, then `|x| - √d/2 ≤ ‖v‖`. -/
private lemma euclidNorm_sub_sqrt_div_two_le_norm {x : Site d}
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cell x) :
    euclidNorm x - Real.sqrt d / 2 ≤ ‖v‖ := by
  have htri : euclidNorm x ≤ ‖v‖ + ‖v - toSpace x‖ := by
    have h := norm_le_norm_add_norm_sub' (toSpace x) v
    rw [norm_toSpace, norm_sub_rev] at h
    exact h
  have hsub := norm_sub_toSpace_le_of_mem_cell hv
  linarith

/-- If `v` lies in the cell of `x`, then `‖v‖ - √d/2 ≤ |x|`. -/
private lemma norm_sub_sqrt_div_two_le_euclidNorm {x : Site d}
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cell x) :
    ‖v‖ - Real.sqrt d / 2 ≤ euclidNorm x := by
  have htri : ‖v‖ ≤ euclidNorm x + ‖v - toSpace x‖ := by
    have h := norm_le_norm_add_norm_sub' v (toSpace x)
    rwa [norm_toSpace] at h
  have hsub := norm_sub_toSpace_le_of_mem_cell hv
  linarith

/-- For `b > 3 + √d/2` and `r ≥ √d`,
`σ_d F(r + b) ≤ 2^{d-1} Σ_{x ∈ A_n, |x| > r + 3} |x|^{1-d}`. -/
theorem tail_le_sum_rpow (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) {r b : ℝ}
    (hb : 3 + Real.sqrt d / 2 < b) (hr : Real.sqrt d ≤ r) :
    d * unitBallVolume d * tail d (cellSet X n) (r + b) ≤
      2 ^ ((d : ℝ) - 1) * ∑ x ∈ (departureRange X n).filter (fun x => r + 3 < euclidNorm x),
        euclidNorm x ^ (1 - (d : ℝ)) := by
  classical
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd) : d ≠ 0)
  have hne : d * unitBallVolume d ≠ 0 :=
    mul_ne_zero hd0 (ne_of_gt (unitBallVolume_pos d))
  have hs_pos : 0 < r + 3 - Real.sqrt d / 2 := by
    have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
    linarith
  have hbdd : Bornology.IsBounded (cellSet X n) :=
    Metric.isBounded_ball.subset (cellSet_subset_ball hd X n)
  have hIntBig : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (cellSet X n ∩ {v | r + 3 - Real.sqrt d / 2 < ‖v‖}) :=
    CERW.Support.Geometry.integrableOn_tail (measurableSet_cellSet X n) hbdd hs_pos
  have hUsub : (⋃ x ∈ (departureRange X n).filter (fun x => r + 3 < euclidNorm x), cell x)
      ⊆ cellSet X n ∩ {v | r + 3 - Real.sqrt d / 2 < ‖v‖} := by
    intro v hv
    rw [Set.mem_iUnion₂] at hv
    obtain ⟨x, hx, hvx⟩ := hv
    rw [Finset.mem_filter] at hx
    obtain ⟨hxdep, hxr⟩ := hx
    constructor
    · exact Set.mem_iUnion₂.mpr ⟨x, hxdep, hvx⟩
    · simp only [Set.mem_setOf_eq]
      have hbound : euclidNorm x - Real.sqrt d / 2 ≤ ‖v‖ :=
        euclidNorm_sub_sqrt_div_two_le_norm hvx
      linarith
  have hIntU : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (⋃ x ∈ (departureRange X n).filter (fun x => r + 3 < euclidNorm x), cell x) :=
    hIntBig.mono_set hUsub
  have hEsubU : cellSet X n ∩ {v | r + b < ‖v‖} ⊆
      ⋃ x ∈ (departureRange X n).filter (fun x => r + 3 < euclidNorm x), cell x := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [Set.mem_setOf_eq] at hv2
    have hxc : cellCenter v ∈ departureRange X n := (mem_cellSet_iff X n v).mp hv1
    refine Set.mem_iUnion₂.mpr ⟨cellCenter v, ?_, mem_cell_cellCenter v⟩
    rw [Finset.mem_filter]
    refine ⟨hxc, ?_⟩
    have hbound : ‖v‖ - Real.sqrt d / 2 ≤ euclidNorm (cellCenter v) :=
      norm_sub_sqrt_div_two_le_euclidNorm (mem_cell_cellCenter v)
    linarith
  calc
    d * unitBallVolume d * tail d (cellSet X n) (r + b)
        = ∫ v in cellSet X n ∩ {v | r + b < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) := by
          rw [tail, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      _ ≤ ∫ v in ⋃ x ∈ (departureRange X n).filter (fun x => r + 3 < euclidNorm x), cell x,
            ‖v‖ ^ (1 - (d : ℝ)) := by
          exact setIntegral_mono_set hIntU
            (Filter.Eventually.of_forall fun v => Real.rpow_nonneg (norm_nonneg v) _)
            (Filter.Eventually.of_forall fun v hv => hEsubU hv)
      _ = ∑ x ∈ (departureRange X n).filter (fun x => r + 3 < euclidNorm x),
            ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by
          rw [integral_biUnion_finset ((departureRange X n).filter
                (fun x => r + 3 < euclidNorm x))
            (fun x _ => measurableSet_cell x)
            (fun x _ y _ hxy => cell_disjoint hxy)
            (fun x hx => hIntU.mono_set (by
              intro v hv
              exact Set.mem_iUnion₂.mpr ⟨x, hx, hv⟩))]
      _ ≤ ∑ x ∈ (departureRange X n).filter (fun x => r + 3 < euclidNorm x),
            2 ^ ((d : ℝ) - 1) * euclidNorm x ^ (1 - (d : ℝ)) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_filter] at hx
          exact (setIntegral_rpow_mem_Icc hd (by linarith)).2
      _ = 2 ^ ((d : ℝ) - 1) * ∑ x ∈ (departureRange X n).filter
            (fun x => r + 3 < euclidNorm x), euclidNorm x ^ (1 - (d : ℝ)) := by
          rw [Finset.mul_sum]

end CERW.Support.Coarse
