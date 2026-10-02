import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The sum of the increments of a nondecreasing sequence over a block

For a nondecreasing real sequence `V` and indices `a ≤ b`, the sum over `t < n` of the increments
`V (t + 1) - V t` kept at the times `a ≤ t < b` is at most `V b - V a` for every `n`, and equals
`V b - V a` once `n ≥ b`. The times are compared in `WithTop ℕ`, as for stopping times.
-/

namespace CERW.Generic.Martingale.LilLower

/-- The comparison of times in `WithTop ℕ` is the comparison of the underlying naturals. -/
private lemma block_cond_iff (a b t : ℕ) :
    ((a : WithTop ℕ) ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < (b : WithTop ℕ)) ↔ (a ≤ t ∧ t < b) := by
  norm_cast

/-- The sum of the increments over `a ≤ t < b`, cut off at time `n`, is
`V (min b n) - V (min a n)`. -/
private lemma block_sum_eq_min (V : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) (n : ℕ) :
    ∑ t ∈ Finset.range n, (if (a : WithTop ℕ) ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < (b : WithTop ℕ)
      then (1 : ℝ) else 0) * (V (t + 1) - V t) = V (min b n) - V (min a n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [block_cond_iff]
    by_cases h1 : n < a
    · have h2 : ¬ (a ≤ n ∧ n < b) := fun h => absurd h.1 (not_le.2 h1)
      rw [if_neg h2, min_eq_right (by omega : n ≤ a), min_eq_right (by omega : n ≤ b),
        min_eq_right (by omega : n + 1 ≤ a), min_eq_right (by omega : n + 1 ≤ b)]
      simp
    · by_cases h3 : n < b
      · have h2 : a ≤ n ∧ n < b := ⟨not_lt.1 h1, h3⟩
        rw [if_pos h2, min_eq_right (by omega : n ≤ b), min_eq_left (by omega : a ≤ n),
          min_eq_right (by omega : n + 1 ≤ b), min_eq_left (by omega : a ≤ n + 1)]
        rw [one_mul, sub_add_sub_cancel']
      · have h2 : ¬ (a ≤ n ∧ n < b) := fun h => h3 h.2
        rw [if_neg h2, min_eq_left (by omega : b ≤ n), min_eq_left (by omega : a ≤ n),
          min_eq_left (by omega : b ≤ n + 1), min_eq_left (by omega : a ≤ n + 1)]
        simp

/-- The sum of the increments of a nondecreasing sequence over `a ≤ t < b`, cut off at time `n`,
is at most `V b - V a`. -/
theorem block_sum_le {V : ℕ → ℝ} (hmono : ∀ n, V n ≤ V (n + 1)) {a b : ℕ} (hab : a ≤ b)
    (n : ℕ) :
    ∑ t ∈ Finset.range n, (if (a : WithTop ℕ) ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < (b : WithTop ℕ)
      then (1 : ℝ) else 0) * (V (t + 1) - V t) ≤ V b - V a := by
  have hm : Monotone V := monotone_nat_of_le_succ hmono
  rw [block_sum_eq_min V hab n]
  by_cases h : n ≤ a
  · rw [min_eq_right h, min_eq_right (h.trans hab)]
    rw [sub_self]
    exact sub_nonneg.2 (hm hab)
  · rw [min_eq_left (not_le.1 h).le]
    exact sub_le_sub_right (hm (min_le_left b n)) _

/-- The same sum equals `V b - V a` once `n ≥ b`. -/
theorem block_sum_eq {V : ℕ → ℝ} {a b n : ℕ} (hab : a ≤ b) (hn : b ≤ n) :
    ∑ t ∈ Finset.range n, (if (a : WithTop ℕ) ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < (b : WithTop ℕ)
      then (1 : ℝ) else 0) * (V (t + 1) - V t) = V b - V a := by
  rw [block_sum_eq_min V hab n, min_eq_left hn, min_eq_left (hab.trans hn)]

end CERW.Generic.Martingale.LilLower
