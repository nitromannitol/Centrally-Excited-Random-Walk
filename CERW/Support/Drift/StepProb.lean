import CERW.Support.Drift.KernelValues
import CERW.Support.Drift.KernelSums

/-!
# The one-step law of the walk with a drift field

`driftStepProb d ε ξ x n` depends on the path only through `x 0, …, x n`, vanishes off the unit
steps, and is nonnegative when `0 ≤ ε` and `ε |ξ_i(z)| ≤ 1/d` for every site `z` and coordinate `i`.
-/

namespace CERW.Support.Drift

open LatticeProb CERW CERW.Support.Law

variable {d : ℕ}

/-- The one-step probabilities depend on the path only through `x 0, …, x n`. -/
theorem driftStepProb_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {x y : ℕ → Site d}
    {n : ℕ} (h : ∀ j ≤ n, x j = y j) (e : Site d) :
    driftStepProb d ε ξ x n e = driftStepProb d ε ξ y n e := by
  have himage : (Finset.range n).image x = (Finset.range n).image y :=
    Finset.image_congr fun j hj => h j (Finset.mem_range.mp hj).le
  simp only [driftStepProb, himage, h n le_rfl]

/-- The one-step probabilities vanish off the unit steps. -/
theorem driftStepProb_eq_zero (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d)
    (n : ℕ) {e : Site d} (he : e ∉ unitSteps d) : driftStepProb d ε ξ x n e = 0 := by
  unfold driftStepProb
  split_ifs with h
  · exact driftFirstStep_eq_zero ε (ξ (x n)) he
  · exact srwStep_eq_zero he

/-- The one-step probabilities are nonnegative when `0 ≤ ε` and `ε |ξ_i(z)| ≤ 1/d`. -/
theorem driftStepProb_nonneg {ε : ℝ} (hε : 0 ≤ ε) {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) (x : ℕ → Site d) (n : ℕ) (e : Site d) :
    0 ≤ driftStepProb d ε ξ x n e := by
  unfold driftStepProb
  split_ifs with h
  · exact driftFirstStep_nonneg hε (hξ (x n)) e
  · exact srwStep_nonneg e

end CERW.Support.Drift
