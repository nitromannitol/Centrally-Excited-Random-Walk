import CERW.Support.Occupation.Facts

/-!
# Membership in the cell set

A point lies in the cell set `D_n = ⋃_{x ∈ A_n} C_x` exactly when its `cellCenter` has been
departed from, and a lattice site lies in `D_n` exactly when it lies in `A_n`. The cell local
time vanishes off `D_n`.
-/

namespace CERW.Support.Occupation

open LatticeProb CERW

variable {d : ℕ}

/-- A point lies in `D_n` exactly when its `cellCenter` lies in `A_n`. -/
theorem mem_cellSet_iff (X : ℕ → Site d) (n : ℕ) (v : EuclideanSpace ℝ (Fin d)) :
    v ∈ cellSet X n ↔ cellCenter v ∈ departureRange X n := by
  rw [cellSet, Set.mem_iUnion₂]
  constructor
  · rintro ⟨x, hx, hv⟩
    rw [← eq_cellCenter_of_mem_cell hv]
    exact hx
  · rintro h
    exact ⟨cellCenter v, h, mem_cell_cellCenter v⟩

/-- An embedded lattice site lies in `D_n` exactly when it lies in `A_n`. -/
theorem toSpace_mem_cellSet_iff (X : ℕ → Site d) (n : ℕ) (x : Site d) :
    toSpace x ∈ cellSet X n ↔ x ∈ departureRange X n := by
  rw [mem_cellSet_iff, ← eq_cellCenter_of_mem_cell (toSpace_mem_cell x)]

/-- The cell local time vanishes off `D_n`. -/
theorem cellLocalTime_eq_zero_of_not_mem (X : ℕ → Site d) (n : ℕ)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∉ cellSet X n) : cellLocalTime X n v = 0 := by
  rw [cellLocalTime]
  have h : cellCenter v ∉ departureRange X n := fun hc => hv ((mem_cellSet_iff X n v).mpr hc)
  rw [mem_departureRange_iff, not_lt, Nat.le_zero] at h
  rw [h, Nat.cast_zero]

end CERW.Support.Occupation
