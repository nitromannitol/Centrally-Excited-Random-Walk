import CERW.Generic.Martingale.Lil.Statements

/-!
# Stopping at the first passage

A process from `0` that exceeds `r` by time `n` still exceeds `r` at time `n` once it is stopped
predictably at its first passage above `r`.
-/

universe u

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- Each `X i` with `i ≤ j` is at most the running maximum at time `j`. -/
theorem le_runMax {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) {i j : ℕ} (h : i ≤ j) :
    X i ω ≤ runMax X j ω := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.mp h
    exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hi | hi
    · exact le_trans (ih (Nat.lt_succ_iff.mp hi)) (le_max_left _ _)
    · obtain rfl : i = j + 1 := le_antisymm h hi
      exact le_max_right _ _

/-- The running maximum at time `j` is at most `c` if every `X i` with `i ≤ j` is. -/
theorem runMax_le {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) {j : ℕ} {c : ℝ}
    (h : ∀ i ≤ j, X i ω ≤ c) : runMax X j ω ≤ c := by
  induction j with
  | zero => exact h 0 le_rfl
  | succ j ih =>
    exact max_le (ih fun i hi => h i (Nat.le_succ_of_le hi)) (h (j + 1) le_rfl)

/-- Stopping at the first passage above `r` keeps a passage above `r`. -/
theorem first_passage : FirstPassage.{u} := by
  intro Ω X r ω n h0 hex
  have hτ := Nat.find_spec hex
  set τ := Nat.find hex with hτdef
  have hτn : τ ≤ n := hτ.1
  have hgate_one : ∀ j ∈ Finset.range τ, bracketIndicator (passLevel X) r j ω = 1 := by
    intro j hj
    refine bracketIndicator_of_le (runMax_le X ω fun i hi => ?_)
    have hjτ : j < τ := Finset.mem_range.mp hj
    have hlt : i < Nat.find hex := lt_of_le_of_lt hi hjτ
    have := Nat.find_min hex hlt
    by_contra hcon
    exact this ⟨le_trans hlt.le hτn, not_le.mp hcon⟩
  have hgate_zero : ∀ j ∈ Finset.Ico τ n, bracketIndicator (passLevel X) r j ω = 0 := by
    intro j hj
    refine bracketIndicator_of_lt ?_
    exact lt_of_lt_of_le hτ.2 (le_runMax X ω (Finset.mem_Ico.mp hj).1)
  have htail : ∑ j ∈ Finset.Ico τ n,
      bracketIndicator (passLevel X) r j ω * (X (j + 1) ω - X j ω) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hgate_zero j hj, zero_mul]
  have hhead : ∑ j ∈ Finset.range τ,
      bracketIndicator (passLevel X) r j ω * (X (j + 1) ω - X j ω) = X τ ω := by
    rw [Finset.sum_congr rfl fun j hj => by rw [hgate_one j hj, one_mul],
      Finset.sum_range_sub (fun j => X j ω), h0, sub_zero]
  unfold firstPassage predictableStop
  rw [← Finset.sum_range_add_sum_Ico _ hτn, hhead, htail, add_zero]
  exact hτ.2

end CERW.Generic.Martingale.Lil
