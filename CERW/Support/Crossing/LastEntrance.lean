import Mathlib.Order.Nat
import Mathlib.Analysis.InnerProductSpace.PiL2
import CERW.Support.Law.Moments

/-!
# The last entrance into a half-space

A real sequence that starts at or below `b` and rises by at most one per step has a last
entrance before any time `τ > 0`. This is a time `s ≤ τ` with `f(s) ≤ b + 1` and `f > b` on
`[s, τ)`. Applied to the projection `v · X_j` of a nearest-neighbour path on a unit direction, it
selects the crossing intervals of `eq:coarse-entrance` and of the outer bound. Every unit step
changes such a projection by at most one.
-/

namespace CERW.Support.Crossing

open LatticeProb CERW

/-- The last entrance: if `f 0 ≤ b`, `f (j + 1) ≤ f j + 1` for all `j`, and `0 < τ`, then there
is `0 < s ≤ τ` with `f s ≤ b + 1` and `b < f j` for all `s ≤ j < τ`. -/
theorem exists_last_entrance {f : ℕ → ℝ} {b : ℝ} {τ : ℕ} (h0 : f 0 ≤ b)
    (hstep : ∀ j, f (j + 1) ≤ f j + 1) (hτ : 0 < τ) :
    ∃ s, 0 < s ∧ s ≤ τ ∧ f s ≤ b + 1 ∧ ∀ j, s ≤ j → j < τ → b < f j := by
  classical
  refine ⟨Nat.findGreatest (fun j => f j ≤ b) (τ - 1) + 1, Nat.succ_pos _, ?_, ?_, ?_⟩
  · have hle : Nat.findGreatest (fun j => f j ≤ b) (τ - 1) ≤ τ - 1 :=
      Nat.findGreatest_le _
    omega
  · have hspec : f (Nat.findGreatest (fun j => f j ≤ b) (τ - 1)) ≤ b :=
      Nat.findGreatest_spec (P := fun j => f j ≤ b) (m := 0) (n := τ - 1)
        (Nat.zero_le _) h0
    have hstep' := hstep (Nat.findGreatest (fun j => f j ≤ b) (τ - 1))
    linarith
  · intro j hsj hjτ
    have hnot : ¬ f j ≤ b :=
      Nat.findGreatest_is_greatest (P := fun j => f j ≤ b) (n := τ - 1)
        (by omega) (by omega)
    exact not_le.mp hnot

/-- The projection of a unit step on a unit direction is at most one. -/
theorem inner_toSpace_le_one {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {e : Site d} (he : e ∈ unitSteps d) : inner ℝ v (toSpace e) ≤ 1 := by
  calc inner ℝ v (toSpace e) ≤ ‖v‖ * ‖toSpace e‖ := real_inner_le_norm v (toSpace e)
    _ = 1 * euclidNorm e := by rw [hv, norm_toSpace]
    _ = 1 := by rw [CERW.Support.Law.euclidNorm_of_mem_unitSteps he, one_mul]

end CERW.Support.Crossing
