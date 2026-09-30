import CERW.Support.Occupation.Facts

/-!
# The cell set lies in a ball

Every point of a cell is within `√d/2` of the cell's site, so every point of `D_n` is within
`H_n + √d/2` of the origin, and in dimension `d ≥ 1` the cell set lies in the open ball of
radius `H_n + √d`.
-/

namespace CERW.Support.Occupation

open LatticeProb CERW

variable {d : ℕ}

/-- Every coordinate of a point of the cell `C_x` differs from the corresponding coordinate
of `x` by at most `1/2`. -/
theorem norm_coord_sub_toSpace_le_of_mem_cell {x : Site d} {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ cell x) (i : Fin d) : ‖(v - toSpace x) i‖ ≤ 1 / 2 := by
  have h1 : ((x i : ℤ) : ℝ) - 1 / 2 ≤ v i := (hv i).1
  have h2 : v i < ((x i : ℤ) : ℝ) + 1 / 2 := (hv i).2
  rw [WithLp.ofLp_sub, Pi.sub_apply, toSpace_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Every point of the cell `C_x` is within `√d / 2` of `x`. -/
theorem norm_sub_toSpace_le_of_mem_cell {x : Site d} {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ cell x) : ‖v - toSpace x‖ ≤ Real.sqrt d / 2 := by
  have hsum : ∑ i : Fin d, ‖(v - toSpace x) i‖ ^ 2 ≤ (d : ℝ) / 4 := by
    calc ∑ i : Fin d, ‖(v - toSpace x) i‖ ^ 2
        ≤ ∑ _i : Fin d, (1 / 2 : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            sq_le_sq' (by linarith [norm_nonneg ((v - toSpace x) i)])
              (norm_coord_sub_toSpace_le_of_mem_cell hv i)
      _ = (d : ℝ) / 4 := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          ring
  calc ‖v - toSpace x‖ = Real.sqrt (∑ i : Fin d, ‖(v - toSpace x) i‖ ^ 2) :=
        EuclideanSpace.norm_eq _
    _ ≤ Real.sqrt ((d : ℝ) / 4) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d / 2 := by
        rw [Real.sqrt_div' d (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num

/-- Every point of `D_n` is within `H_n + √d/2` of the origin. -/
theorem norm_le_of_mem_cellSet (X : ℕ → Site d) (n : ℕ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ cellSet X n) : ‖v‖ ≤ maxRadius X n + Real.sqrt d / 2 := by
  obtain ⟨x, hx, hvx⟩ := Set.mem_iUnion₂.mp hv
  have hxball : euclidNorm x ≤ maxRadius X n :=
    LatticeProb.mem_ballFinset_iff.mp (departureRange_subset_ballFinset X n hx)
  calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ := norm_le_norm_add_norm_sub' v (toSpace x)
    _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace x]
    _ ≤ maxRadius X n + Real.sqrt d / 2 :=
        add_le_add hxball (norm_sub_toSpace_le_of_mem_cell hvx)

/-- In dimension `d ≥ 1`, `D_n` lies in the open ball of radius `H_n + √d`. -/
theorem cellSet_subset_ball (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) :
    cellSet X n ⊆ Metric.ball 0 (maxRadius X n + Real.sqrt d) := by
  intro v hv
  rw [mem_ball_zero_iff]
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlt : Real.sqrt d / 2 < Real.sqrt d := by
    have hpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
    linarith
  linarith [norm_le_of_mem_cellSet X n hv]

end CERW.Support.Occupation
