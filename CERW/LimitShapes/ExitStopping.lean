module

public import CERW.LimitShapes.Event

@[expose] public section

/-!
# Bounds and quadratic sums at the first exit

A path with increments bounded by one overshoots an open Euclidean ball by at most one.
The stopped quadratic sum of Section `sec:norm-event` includes precisely the departures
strictly before an explicitly specified first exit, at every terminal horizon.
-/

namespace CERW.LimitShapes.ExitStopping

/-- The first exit overshoots the radius by at most the bound on one increment. -/
theorem exit_norm_le {d : ℕ} (X : ℕ → LatticeProb.Site d) (R : ℝ) (τ : ℕ)
    (hτ : 0 < τ)
    (hstep : ∀ j : ℕ, ‖CERW.toSpace (X (j + 1)) - CERW.toSpace (X j)‖ ≤ 1)
    (hbefore : ∀ j : ℕ, j < τ → LatticeProb.euclidNorm (X j) < R) :
    LatticeProb.euclidNorm (X τ) ≤ R + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hτ)
  have hnorm := norm_add_le (CERW.toSpace (X k))
    (CERW.toSpace (X (k + 1)) - CERW.toSpace (X k))
  have heq : CERW.toSpace (X k) +
      (CERW.toSpace (X (k + 1)) - CERW.toSpace (X k)) =
      CERW.toSpace (X (k + 1)) := by abel
  rw [heq, CERW.norm_toSpace, CERW.norm_toSpace] at hnorm
  exact hnorm.trans (add_le_add (hbefore k (by omega)).le (hstep k))

/-- Stopping at the first exit retains exactly the increments with index below
both the terminal horizon and the exit time, including an exit at time zero. -/
theorem stoppedQuadratic_eq_sum_range_min {d : ℕ} (ε : ℝ)
    (ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (X : ℕ → LatticeProb.Site d) (τ n : ℕ)
    (hbefore : ∀ j : ℕ, j < τ → LatticeProb.euclidNorm (X j) < R)
    (hexit : R ≤ LatticeProb.euclidNorm (X τ)) :
    CERW.LimitShapes.stoppedQuadratic ε ξ R X n =
      ∑ j ∈ Finset.range (min n τ),
        2 * inner ℝ (CERW.toSpace (X j))
          (CERW.toSpace (X (j + 1)) - CERW.toSpace (X j) +
            ε • (if X j ∉ CERW.departureRange X j then ξ (X j) else 0)) := by
  classical
  have hguard (j : ℕ) :
      (∀ k ≤ j, LatticeProb.euclidNorm (X k) < R) ↔ j < τ := by
    constructor
    · intro h
      by_contra hj
      exact (not_lt_of_ge hexit) (h τ (Nat.le_of_not_gt hj))
    · intro hj k hk
      exact hbefore k (hk.trans_lt hj)
  unfold CERW.LimitShapes.stoppedQuadratic
  simp_rw [hguard]
  calc
    _ = ∑ j ∈ Finset.range (min n τ),
        if j < τ then
          2 * inner ℝ (CERW.toSpace (X j))
            (CERW.toSpace (X (j + 1)) - CERW.toSpace (X j) +
              ε • (if X j ∉ CERW.departureRange X j then ξ (X j) else 0))
        else 0 := by
      symm
      apply Finset.sum_subset
      · intro j hj
        exact Finset.mem_range.mpr
          ((Finset.mem_range.mp hj).trans_le (min_le_left n τ))
      · intro j hjn hj
        have hjτ : ¬ j < τ := by
          intro hjτ
          exact hj (Finset.mem_range.mpr
            (lt_min (Finset.mem_range.mp hjn) hjτ))
        simp only [if_neg hjτ]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos ((Finset.mem_range.mp hj).trans_le (min_le_right n τ))]

end CERW.LimitShapes.ExitStopping
