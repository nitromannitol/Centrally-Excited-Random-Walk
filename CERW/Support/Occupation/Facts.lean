import CERW.Model.Occupation
import CERW.Support.Law.Moments

/-!
# Pathwise facts about local times and ranges

Deterministic identities and inequalities for the occupation quantities of a lattice path.
The local times over the departure range add up to the elapsed time, so `n ≤ M_n R_n`. Every
site of `A_n` has exactly one first departure, so `k_{0,n} = R_n`. Interval local times are
dominated by full local times. A nearest-neighbour path from the origin stays in the ball of
radius `n` up to time `n`, and its departure range lies in the lattice ball of radius `H_n`.
-/

namespace CERW.Support.Occupation

open LatticeProb CERW

variable {d : ℕ}

/-- The departure range grows with time. -/
theorem departureRange_mono (X : ℕ → Site d) {m n : ℕ} (h : m ≤ n) :
    departureRange X m ⊆ departureRange X n := by
  intro x hx
  rw [departureRange] at hx ⊢
  exact Finset.image_subset_image (Finset.range_subset_range.mpr h) hx

/-- One more step adds the current position to the departure range. -/
theorem departureRange_succ (X : ℕ → Site d) (n : ℕ) :
    departureRange X (n + 1) = insert (X n) (departureRange X n) := by
  rw [departureRange, Finset.range_add_one, Finset.image_insert]
  rfl

/-- At most `n` sites are departed from by time `n`. -/
theorem card_departureRange_le (X : ℕ → Site d) (n : ℕ) : (departureRange X n).card ≤ n := by
  rw [departureRange]
  calc ((Finset.range n).image X).card ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

/-- The local times over the departure range sum to the elapsed time. -/
theorem sum_localTime_eq (X : ℕ → Site d) (n : ℕ) :
    ∑ x ∈ departureRange X n, localTime X n x = n := by
  simp only [localTime, departureRange]
  rw [← Finset.card_eq_sum_card_image X (Finset.range n), Finset.card_range]

/-- The elapsed time is at most the maximal local time times the number of sites:
`n ≤ M_n R_n`. -/
theorem le_maxLocalTime_mul_card (X : ℕ → Site d) (n : ℕ) :
    n ≤ maxLocalTime X n * (departureRange X n).card := by
  calc n = ∑ x ∈ departureRange X n, localTime X n x := (sum_localTime_eq X n).symm
    _ ≤ ∑ _x ∈ departureRange X n, maxLocalTime X n :=
        Finset.sum_le_sum fun x _ => localTime_le_maxLocalTime X n x
    _ = (departureRange X n).card * maxLocalTime X n := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ = maxLocalTime X n * (departureRange X n).card := Nat.mul_comm _ _

/-- No local time exceeds the elapsed time. -/
theorem maxLocalTime_le (X : ℕ → Site d) (n : ℕ) : maxLocalTime X n ≤ n := by
  apply Finset.sup_le
  intro x _
  calc localTime X n x = ((Finset.range n).filter fun j => X j = x).card := rfl
    _ ≤ (Finset.range n).card := Finset.card_filter_le _ _
    _ = n := Finset.card_range n

/-- Every departed site has exactly one first departure: `k_{0,n} = R_n`. -/
theorem freshCount_zero (X : ℕ → Site d) (n : ℕ) :
    freshCount X 0 n = (departureRange X n).card := by
  induction n with
  | zero => simp [freshCount, departureRange]
  | succ n ih =>
    have hIco : Finset.Ico 0 (n + 1) = insert n (Finset.Ico 0 n) := by
      rw [← Finset.range_eq_Ico, Finset.range_add_one, Finset.range_eq_Ico]
    rw [freshCount, departureRange_succ, hIco, Finset.filter_insert]
    simp only [freshCount] at ih
    by_cases h : X n ∈ departureRange X n
    · rw [if_neg (not_not.mpr h), Finset.insert_eq_of_mem h, ih]
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem h, ih]

/-- There are at most `t - s` first departures in `[s, t)`. -/
theorem freshCount_le (X : ℕ → Site d) (s t : ℕ) : freshCount X s t ≤ t - s := by
  rw [freshCount]
  calc (((Finset.Ico s t).filter fun j => X j ∉ departureRange X j)).card
      ≤ (Finset.Ico s t).card := Finset.card_filter_le _ _
    _ = t - s := Nat.card_Ico s t

/-- The interval local time from time `0` is the local time. -/
theorem intervalLocalTime_zero (X : ℕ → Site d) (n : ℕ) (x : Site d) :
    intervalLocalTime X 0 n x = localTime X n x := by
  rw [intervalLocalTime, localTime, (Finset.range_eq_Ico n).symm]

/-- Local times split at an intermediate time: `ℓ_s(x) + ℓ_{s,t}(x) = ℓ_t(x)`. -/
theorem localTime_add_intervalLocalTime (X : ℕ → Site d) {s t : ℕ} (h : s ≤ t) (x : Site d) :
    localTime X s x + intervalLocalTime X s t x = localTime X t x := by
  have hrange : Finset.range t = Finset.range s ∪ Finset.Ico s t := by
    ext j
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range s) (Finset.Ico s t) := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 s t
  simp only [localTime, intervalLocalTime]
  rw [hrange, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter hdisj

/-- Interval local times are dominated by the local time at any later time. -/
theorem intervalLocalTime_le_localTime (X : ℕ → Site d) {s t n : ℕ} (ht : t ≤ n)
    (x : Site d) : intervalLocalTime X s t x ≤ localTime X n x := by
  rw [localTime, intervalLocalTime]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro j hj
  rw [Finset.mem_Ico] at hj
  exact Finset.mem_range.mpr (lt_of_lt_of_le hj.2 ht)

/-- The interval maximum is dominated by the maximal local time at any later time. -/
theorem intervalMax_le_maxLocalTime (X : ℕ → Site d) {s t n : ℕ} (ht : t ≤ n) :
    intervalMax X s t ≤ maxLocalTime X n := by
  apply Finset.sup_le
  intro x _
  exact (intervalLocalTime_le_localTime X ht x).trans (localTime_le_maxLocalTime X n x)

/-- The Euclidean norm of lattice sites is subadditive. -/
theorem euclidNorm_add_le (x y : Site d) : euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by
  have h : toSpace (x + y) = toSpace x + toSpace y := by
    apply PiLp.ext
    intro i
    simp [toSpace_apply, Pi.add_apply, Int.cast_add]
  calc euclidNorm (x + y) = ‖toSpace (x + y)‖ := (norm_toSpace (x + y)).symm
    _ = ‖toSpace x + toSpace y‖ := by rw [h]
    _ ≤ ‖toSpace x‖ + ‖toSpace y‖ := norm_add_le _ _
    _ = euclidNorm x + euclidNorm y := by rw [norm_toSpace, norm_toSpace]

/-- A nearest-neighbour path from the origin is within distance `j` of the origin at time `j`. -/
theorem euclidNorm_le_of_steps (X : ℕ → Site d) (h0 : X 0 = 0)
    (hstep : ∀ j, X (j + 1) - X j ∈ unitSteps d) (j : ℕ) : euclidNorm (X j) ≤ j := by
  induction j with
  | zero => rw [h0]; simp
  | succ j ih =>
    have hnorm : euclidNorm (X (j + 1) - X j) = 1 :=
      CERW.Support.Law.euclidNorm_of_mem_unitSteps (hstep j)
    calc euclidNorm (X (j + 1))
        = euclidNorm (X j + (X (j + 1) - X j)) := by rw [add_sub_cancel]
      _ ≤ euclidNorm (X j) + euclidNorm (X (j + 1) - X j) := euclidNorm_add_le _ _
      _ ≤ (j : ℝ) + 1 := by rw [hnorm]; linarith
      _ = ((j + 1 : ℕ) : ℝ) := by push_cast; ring

/-- A nearest-neighbour path from the origin has `H_n ≤ n`. -/
theorem maxRadius_le_of_steps (X : ℕ → Site d) (h0 : X 0 = 0)
    (hstep : ∀ j, X (j + 1) - X j ∈ unitSteps d) (n : ℕ) : maxRadius X n ≤ n := by
  apply Finset.sup'_le
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  calc euclidNorm (X j) ≤ (j : ℝ) := euclidNorm_le_of_steps X h0 hstep j
    _ ≤ (n : ℝ) := by exact_mod_cast hjn

/-- The departure range lies in the lattice ball of radius `H_n`. -/
theorem departureRange_subset_ballFinset (X : ℕ → Site d) (n : ℕ) :
    departureRange X n ⊆ ballFinset d (maxRadius X n) := by
  intro x hx
  rw [departureRange] at hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  rw [LatticeProb.mem_ballFinset_iff]
  exact euclidNorm_le_maxRadius X (Nat.le_of_lt (Finset.mem_range.mp hj))

end CERW.Support.Occupation
