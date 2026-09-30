import CERW.Model.Occupation

/-!
# Sums over first visits

Each site of the departure range `A_n = {x_0, …, x_{n-1}}` is visited for the first time exactly
once before time `n`. So a sum over the first-visit times `j < n` of `g(x_j)` is the sum of `g` over
`A_n`. With the extra condition `x_j ≠ 0` of the first-departure rule, the site `0` is omitted.
The indicator sum of the visits to `y` is the local time `ℓ_n(y)`. These identities turn the
Dynkin compensator of `b(X_j - y)` into the source sum of `eq:dynkin`.
-/

namespace CERW.Support.Occupation

open Finset CERW LatticeProb

variable {d : ℕ}

/-- A sum over first-visit times is a sum over the departure range. -/
theorem sum_fresh_eq_sum_departureRange {M : Type*} [AddCommMonoid M] (x : ℕ → Site d) (n : ℕ)
    (g : Site d → M) :
    ∑ j ∈ range n, (if x j ∉ (range j).image x then g (x j) else 0) =
      ∑ z ∈ departureRange x n, g z := by
  induction n with
  | zero => simp [departureRange]
  | succ n ih =>
    have hsucc : departureRange x (n + 1) = insert (x n) (departureRange x n) := by
      rw [departureRange, Finset.range_add_one, Finset.image_insert]
      rfl
    rw [Finset.sum_range_succ, ih, hsucc]
    simp only [departureRange]
    by_cases h : x n ∈ (range n).image x
    · rw [Finset.insert_eq_of_mem h, if_neg (not_not.mpr h), add_zero]
    · rw [Finset.sum_insert h, if_pos h]
      exact add_comm _ _

/-- A sum over first visits to nonzero sites is a sum over the nonzero sites of the departure
range. -/
theorem sum_fresh_ne_zero_eq_sum_departureRange {M : Type*} [AddCommMonoid M]
    (x : ℕ → Site d) (n : ℕ) (g : Site d → M) :
    ∑ j ∈ range n, (if x j ≠ 0 ∧ x j ∉ (range j).image x then g (x j) else 0) =
      ∑ z ∈ departureRange x n, (if z ≠ 0 then g z else 0) := by
  rw [← sum_fresh_eq_sum_departureRange x n (fun z => if z ≠ 0 then g z else 0)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : x j = 0 <;> simp [h]

/-- The number of visits to `y` before time `n` is the local time `ℓ_n(y)`. -/
theorem sum_ite_eq_localTime (x : ℕ → Site d) (n : ℕ) (y : Site d) :
    ∑ j ∈ range n, (if x j = y then (1 : ℝ) else 0) = (localTime x n y : ℝ) := by
  rw [Finset.sum_boole, localTime]

end CERW.Support.Occupation
