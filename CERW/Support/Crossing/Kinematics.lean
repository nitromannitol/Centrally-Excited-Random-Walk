import CERW.Support.Occupation.Facts

/-!
# Duration and drift on a crossing interval

On a time interval `[s, t)` the interval local times over the visited sites add up to `t - s`,
so `t - s ≤ m M_{s,t}` with `m` the number of distinct sites (the duration bound before
`eq:crossing-before-young`). A site `x` with `v · x > b > 0` and `|x| < r` has inward direction
with `v · u_x > b/r` (the projected mean of a first departure).
-/

namespace CERW.Support.Crossing

open LatticeProb CERW

variable {d : ℕ}

/-- The interval local times over the sites visited in `[s, t)` sum to `t - s`. -/
theorem sum_intervalLocalTime (X : ℕ → Site d) (s t : ℕ) :
    ∑ x ∈ (Finset.Ico s t).image X, intervalLocalTime X s t x = t - s := by
  simp only [intervalLocalTime]
  rw [← Finset.card_eq_sum_card_image X (Finset.Ico s t), Nat.card_Ico]

/-- The duration of `[s, t)` is at most the number of distinct sites times `M_{s,t}`. -/
theorem sub_le_card_mul_intervalMax (X : ℕ → Site d) (s t : ℕ) :
    t - s ≤ ((Finset.Ico s t).image X).card * intervalMax X s t := by
  rw [← sum_intervalLocalTime X s t]
  calc ∑ x ∈ (Finset.Ico s t).image X, intervalLocalTime X s t x
      ≤ ∑ _x ∈ (Finset.Ico s t).image X, intervalMax X s t :=
        Finset.sum_le_sum fun x _ => intervalLocalTime_le_intervalMax X s t x
    _ = ((Finset.Ico s t).image X).card * intervalMax X s t := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]

/-- If `v · x > b > 0` and `|x| < r`, then `v · u_x > b / r`. -/
theorem div_lt_inner_unitDir {v x : EuclideanSpace ℝ (Fin d)} {b r : ℝ} (hb : 0 < b)
    (hvx : b < inner ℝ v x) (hxr : ‖x‖ < r) : b / r < inner ℝ v (unitDir x) := by
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [inner_zero_right] at hvx
    exact absurd hvx (not_lt.mpr (le_of_lt hb))
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hinnerpos : 0 < inner ℝ v x := lt_trans hb hvx
  have hkey : b / r < inner ℝ v x / ‖x‖ :=
    div_lt_div₀ hvx (le_of_lt hxr) (le_of_lt hinnerpos) hxpos
  change b / r < inner ℝ v (‖x‖⁻¹ • x)
  rw [real_inner_smul_right, inv_mul_eq_div]
  exact hkey

end CERW.Support.Crossing
