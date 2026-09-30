import CERW.Model.Space

/-!
# Local times, ranges and occupation quantities

Pathwise quantities of a lattice path `X : ℕ → ℤ^d` (`eq:local-range`, `eq:occupation`,
`eq:interval-def`, `eq:shell-def`). The departure local time `ℓ_n(x)` counts the times
`j < n` with `X_j = x`. The departure range `A_n` is the set of sites with positive local
time, and the range `V_n` also contains the current position `X_n`. The cell set
`D_n = ⋃_{x ∈ A_n} C_x` and the cell local time `ℓ̃_n`, equal to `ℓ_n(x)` on `C_x`, carry
these to `ℝ^d`. Where a body is a convenient reformulation of the paper's wording, the
paper's characterization is proved next to it.
-/

namespace CERW

open LatticeProb

variable {d : ℕ}

/-- The departure local time `ℓ_n(x) = #{j < n : X_j = x}`. -/
def localTime (X : ℕ → Site d) (n : ℕ) (x : Site d) : ℕ :=
  ((Finset.range n).filter fun j => X j = x).card

/-- The departure range `A_n`, the sites visited at times `0, …, n-1`. -/
def departureRange (X : ℕ → Site d) (n : ℕ) : Finset (Site d) :=
  (Finset.range n).image X

/-- `A_n = {x : ℓ_n(x) > 0}`, as in `eq:local-range`. -/
theorem mem_departureRange_iff {X : ℕ → Site d} {n : ℕ} {x : Site d} :
    x ∈ departureRange X n ↔ 0 < localTime X n x := by
  simp [departureRange, localTime, Finset.card_pos, Finset.Nonempty]

/-- The range `V_n = {X_0, …, X_n}`. -/
def visitedRange (X : ℕ → Site d) (n : ℕ) : Finset (Site d) :=
  (Finset.range (n + 1)).image X

/-- `V_n = A_n ∪ {X_n}`. -/
theorem visitedRange_eq_insert (X : ℕ → Site d) (n : ℕ) :
    visitedRange X n = insert (X n) (departureRange X n) := by
  simp [visitedRange, departureRange, Finset.range_add_one, Finset.image_insert]

/-- The maximal departure local time `M_n = max_x ℓ_n(x)`, attained on `A_n`. -/
def maxLocalTime (X : ℕ → Site d) (n : ℕ) : ℕ :=
  (departureRange X n).sup (localTime X n)

/-- Every local time is at most `M_n`; off `A_n` the local time vanishes. -/
theorem localTime_le_maxLocalTime (X : ℕ → Site d) (n : ℕ) (x : Site d) :
    localTime X n x ≤ maxLocalTime X n := by
  by_cases hx : x ∈ departureRange X n
  · exact Finset.le_sup hx
  · rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hx
    rw [hx]
    exact Nat.zero_le _

/-- The largest distance `H_n = max_{0 ≤ j ≤ n} |X_j|` from the origin. -/
noncomputable def maxRadius (X : ℕ → Site d) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    fun j => euclidNorm (X j)

/-- Every position up to time `n` lies within distance `H_n` of the origin. -/
theorem euclidNorm_le_maxRadius (X : ℕ → Site d) {n j : ℕ} (hj : j ≤ n) :
    euclidNorm (X j) ≤ maxRadius X n :=
  Finset.le_sup' (fun j => euclidNorm (X j)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- The number `k_{s,t}` of first departures `I_j = 1{X_j ∉ A_j}` at times `s ≤ j < t`. -/
def freshCount (X : ℕ → Site d) (s t : ℕ) : ℕ :=
  ((Finset.Ico s t).filter fun j => X j ∉ departureRange X j).card

/-- The interval local time `ℓ_{s,t}(x) = #{s ≤ j < t : X_j = x}`. -/
def intervalLocalTime (X : ℕ → Site d) (s t : ℕ) (x : Site d) : ℕ :=
  ((Finset.Ico s t).filter fun j => X j = x).card

/-- The interval maximum `M_{s,t} = max_x ℓ_{s,t}(x)`, attained at a site visited in `[s, t)`. -/
def intervalMax (X : ℕ → Site d) (s t : ℕ) : ℕ :=
  ((Finset.Ico s t).image X).sup (intervalLocalTime X s t)

/-- Every interval local time is at most `M_{s,t}`. -/
theorem intervalLocalTime_le_intervalMax (X : ℕ → Site d) (s t : ℕ) (x : Site d) :
    intervalLocalTime X s t x ≤ intervalMax X s t := by
  by_cases hx : x ∈ (Finset.Ico s t).image X
  · exact Finset.le_sup hx
  · have h0 : intervalLocalTime X s t x = 0 := by
      rw [intervalLocalTime, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj hjx
      exact hx (Finset.mem_image.mpr ⟨j, hj, hjx⟩)
    rw [h0]
    exact Nat.zero_le _

open scoped Classical in
/-- The shell maximum `M_sh(r) = max_{||x| - r| ≤ 3} ℓ_n(x)` of `eq:shell-def`. -/
noncomputable def shellMax (X : ℕ → Site d) (n r : ℕ) : ℕ :=
  ((ballFinset d ((r : ℝ) + 3)).filter fun x => |euclidNorm x - r| ≤ 3).sup (localTime X n)

/-- Every site of the shell `||x| - r| ≤ 3` has local time at most `M_sh(r)`. -/
theorem localTime_le_shellMax (X : ℕ → Site d) (n r : ℕ) {x : Site d}
    (hx : |euclidNorm x - r| ≤ 3) : localTime X n x ≤ shellMax X n r := by
  classical
  refine Finset.le_sup (f := localTime X n) (Finset.mem_filter.mpr ⟨?_, hx⟩)
  rw [mem_ballFinset_iff]
  linarith [(abs_le.mp hx).2]

/-- The cell set `D_n = ⋃_{x ∈ A_n} C_x`. -/
def cellSet (X : ℕ → Site d) (n : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ x ∈ departureRange X n, cell x

/-- The cell local time `ℓ̃_n`, equal to `ℓ_n(x)` on the cell `C_x`. -/
noncomputable def cellLocalTime (X : ℕ → Site d) (n : ℕ) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (localTime X n (cellCenter v) : ℝ)

/-- `ℓ̃_n` equals `ℓ_n(x)` on `C_x`, including the value zero on unoccupied cells. -/
theorem cellLocalTime_of_mem_cell (X : ℕ → Site d) (n : ℕ) {x : Site d}
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cell x) :
    cellLocalTime X n v = (localTime X n x : ℝ) := by
  rw [cellLocalTime, ← eq_cellCenter_of_mem_cell hv]

end CERW
