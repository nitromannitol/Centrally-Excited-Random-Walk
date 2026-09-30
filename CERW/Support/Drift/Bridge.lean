import CERW.Support.Drift.KernelSums
import CERW.Model.Law
import CERW.Model.DriftLaw

/-!
# The Euclidean walk as the walk with drift field `x/|x|`

The first-departure probabilities of the Euclidean walk are those of the drift field
`ξ(x) = u_x = x/|x|` (with `u_0 = 0`), so `IsCERW μ ε X` is `IsDriftCERW μ ε u X`. The one-step
probabilities of any drift field sum to one over the unit steps.
-/

namespace CERW.Support.Drift

open LatticeProb CERW CERW.Support.Law MeasureTheory

variable {d : ℕ}

/-- The `i`-th coordinate of the direction `u_x = x/|x|` of a site is `x_i/|x|`. -/
private theorem unitDir_toSpace_apply (y : Site d) (i : Fin d) :
    unitDir (toSpace y) i = ((y i : ℤ) : ℝ) / euclidNorm y := by
  rw [unitDir, PiLp.smul_apply, norm_toSpace, toSpace_apply, smul_eq_mul, inv_mul_eq_div]

/-- The Euclidean first-departure kernel `firstStep` at `x` is the drift first-departure kernel
`driftFirstStep` at the direction `u_x = x/|x|`. -/
private theorem firstStep_eq_driftFirstStep (ε : ℝ) (y : Site d) (e : Site d) :
    firstStep d ε y e = driftFirstStep d ε (unitDir (toSpace y)) e := by
  unfold firstStep driftFirstStep
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [unitDir_toSpace_apply]

/-- The Euclidean one-step law is the drift one-step law of the field `x ↦ u_x`. -/
theorem stepProb_eq_driftStepProb (ε : ℝ) (x : ℕ → Site d) (n : ℕ) (e : Site d) :
    stepProb d ε x n e = driftStepProb d ε (fun z => unitDir (toSpace z)) x n e := by
  unfold stepProb driftStepProb
  split_ifs with h
  · exact firstStep_eq_driftFirstStep ε (x n) e
  · rfl

/-- `IsCERW μ ε X` is `IsDriftCERW μ ε u X` for the field `u(x) = x/|x|`. -/
theorem isCERW_iff_isDriftCERW {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ε : ℝ)
    (X : ℕ → Ω → Site d) :
    IsCERW μ ε X ↔ IsDriftCERW μ ε (fun z => unitDir (toSpace z)) X := by
  constructor
  · intro h
    refine ⟨h.measurable, h.start, ?_⟩
    intro n x
    simpa only [stepProb_eq_driftStepProb ε x n (x (n + 1) - x n)] using h.step n x
  · intro h
    refine ⟨h.measurable, h.start, ?_⟩
    intro n x
    simpa only [stepProb_eq_driftStepProb ε x n (x (n + 1) - x n)] using h.step n x

/-- The drift one-step probabilities sum to one over the unit steps. -/
theorem sum_driftStepProb (hd : 1 ≤ d) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) (n : ℕ) : ∑ e ∈ unitSteps d, driftStepProb d ε ξ x n e = 1 := by
  unfold driftStepProb
  split_ifs with h
  · exact sum_driftFirstStep hd ε (ξ (x n))
  · exact sum_srwStep hd

end CERW.Support.Drift
