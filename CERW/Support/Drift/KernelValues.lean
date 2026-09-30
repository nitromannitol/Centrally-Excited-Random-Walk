import CERW.Model.DriftKernel
import CERW.Support.Law.Moments

/-!
# The values of the drift first-departure kernel

`driftFirstStep d ε w` takes the value `1/(2d) - (ε/2) w_i` at `e_i`, the value
`1/(2d) + (ε/2) w_i` at `-e_i`, and `0` at every step that is not a unit step.
-/

namespace CERW.Support.Drift

open LatticeProb CERW CERW.Support.Law

variable {d : ℕ}

/-- The drift kernel at `e_i` is `1/(2d) - (ε/2) w_i`. -/
theorem driftFirstStep_unit (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    driftFirstStep d ε w (unit i) = 1 / (2 * d) - ε / 2 * w i := by
  unfold driftFirstStep
  rw [Finset.sum_eq_single i]
  · simp [unit_ne_neg_unit i]
  · intro j _ hj
    have h1 : unit i ≠ unit j := fun h => hj (unit_injective h).symm
    have h2 : unit i ≠ -unit j := unit_ne_neg_unit' i j
    simp [h1, h2]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The drift kernel at `-e_i` is `1/(2d) + (ε/2) w_i`. -/
theorem driftFirstStep_neg_unit (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    driftFirstStep d ε w (-unit i) = 1 / (2 * d) + ε / 2 * w i := by
  unfold driftFirstStep
  rw [Finset.sum_eq_single i]
  · simp [(unit_ne_neg_unit i).symm]
  · intro j _ hj
    have h1 : -unit i ≠ unit j := by
      intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj)] at this
    have h2 : -unit i ≠ -unit j := by
      intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj)] at this
    simp [h1, h2]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The drift kernel vanishes off the unit steps. -/
theorem driftFirstStep_eq_zero (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) {e : Site d}
    (he : e ∉ unitSteps d) : driftFirstStep d ε w e = 0 := by
  unfold driftFirstStep
  apply Finset.sum_eq_zero
  intro i _
  have h1 : e ≠ unit i := fun h => he (mem_unitSteps.mpr ⟨i, Or.inl h⟩)
  have h2 : e ≠ -unit i := fun h => he (mem_unitSteps.mpr ⟨i, Or.inr h⟩)
  simp [h1, h2]

end CERW.Support.Drift
