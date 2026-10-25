module

public import CERW.LimitShapes.Event

@[expose] public section

/-!
# Dynkin identities for the shifted square kernel

The shifted-square test function in `lem:contact` has an exact increment expansion into
a linear kernel increment and its square. Summing this expansion gives the pathwise
Dynkin energy identity for the actual drift transition weights.
-/

namespace CERW.LimitShapes.SquareDynkin

open CERW LatticeProb

/-- The mean increment of the shifted square is its linear increment plus the
weighted square increment, by pointwise expansion of the square. -/
theorem squareKernel_stepMean {d : ℕ}
    (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d))
    (X : ℕ → LatticeProb.Site d) (n t : ℕ) (y : LatticeProb.Site d) :
    let g : LatticeProb.Site d → ℝ := fun z => CERW.latticeKernel d (z - y)
    let γ := CERW.LimitShapes.kernelShift d Ψ ε n
    CERW.stepMean (CERW.driftStepProb d ε ξ)
        (CERW.LimitShapes.squareKernel Ψ ε n y) X t =
      2 * (g (X t) - γ) * CERW.stepMean (CERW.driftStepProb d ε ξ) g X t +
        ∑ e ∈ CERW.unitSteps d,
          CERW.driftStepProb d ε ξ X t e * (g (X t + e) - g (X t)) ^ 2 := by
  dsimp only
  unfold stepMean squareKernel
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- The shifted-square Dynkin formula separates the linear kernel increment from
the weighted square increments along the path. -/
theorem squareKernel_dynkin_identity {d : ℕ}
    (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d))
    (X : ℕ → LatticeProb.Site d) (n : ℕ) (y : LatticeProb.Site d) :
    let g : LatticeProb.Site d → ℝ := fun z => CERW.latticeKernel d (z - y)
    let γ := CERW.LimitShapes.kernelShift d Ψ ε n
    (g (X n) - γ) ^ 2 - (g (X 0) - γ) ^ 2 =
      CERW.dynkinMart (CERW.driftStepProb d ε ξ)
          (CERW.LimitShapes.squareKernel Ψ ε n y) X n +
        ∑ t ∈ Finset.range n,
          (2 * (g (X t) - γ) * CERW.stepMean (CERW.driftStepProb d ε ξ) g X t +
            ∑ e ∈ CERW.unitSteps d,
              CERW.driftStepProb d ε ξ X t e * (g (X t + e) - g (X t)) ^ 2) := by
  dsimp only
  simp_rw [← squareKernel_stepMean Ψ ε ξ X n]
  unfold dynkinMart squareKernel
  exact (sub_add_cancel _ _).symm

end CERW.LimitShapes.SquareDynkin
