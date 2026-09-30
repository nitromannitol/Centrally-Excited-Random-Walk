import CERW.Support.Law.Moments

/-!
# Conditional means of a function after one step

The central difference `D f(y) = Σ_i ((f(y + e_i) - f(y - e_i))/2) e_i`. A simple random walk
step averages `f` to `P f(y)`. A first departure from `x` averages it to
`P f(y) - ε u_x · D f(y)`. This is the drift of every Dynkin martingale of the paper
(`eq:dynkin`, the proof of `lem:radial`, `eq:vector-def`, `eq:quadratic`).
-/

namespace CERW.Support.Law

open LatticeProb CERW

variable {d : ℕ}

/-- The central difference `D f(y) = Σ_i ((f(y + e_i) - f(y - e_i))/2) e_i`. -/
noncomputable def centralDiff (f : Site d → ℝ) (y : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => (f (y + unit i) - f (y - unit i)) / 2

/-- A simple random walk step averages `f` to `P f(y)`. -/
theorem sum_srwStep_mul (f : Site d → ℝ) (y : Site d) :
    ∑ e ∈ unitSteps d, srwStep d e * f (y + e) = walkOp f y := by
  rw [sum_unitSteps]
  have hpair : ∀ i : Fin d,
      srwStep d (unit i) * f (y + unit i) + srwStep d (-unit i) * f (y + -unit i) =
        (1 / (2 * d)) * (f (y + unit i) + f (y - unit i)) := by
    intro i
    rw [srwStep_unit, srwStep_neg_unit, sub_eq_add_neg]
    ring
  simp_rw [hpair]
  rw [← Finset.mul_sum, walkOp, nbrSum, div_eq_mul_inv]
  ring

/-- The inner product of the direction `u_x` with the central difference `D f(y)` is the
normalized coordinate sum `|x|⁻¹ Σ_i x_i (f(y+e_i)-f(y-e_i))/2`. -/
theorem inner_unitDir_centralDiff (x y : Site d) (f : Site d → ℝ) :
    inner ℝ (unitDir (toSpace x)) (centralDiff f y) =
      (euclidNorm x)⁻¹ * ∑ i : Fin d,
        (((x i : ℤ) : ℝ) * ((f (y + unit i) - f (y - unit i)) / 2)) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, unitDir, PiLp.smul_apply, norm_toSpace, toSpace_apply,
    smul_eq_mul, centralDiff, PiLp.toLp_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A first departure from `x` averages `f` to `P f(y) - ε u_x · D f(y)`. -/
theorem sum_firstStep_mul (ε : ℝ) (x : Site d) (f : Site d → ℝ) (y : Site d) :
    ∑ e ∈ unitSteps d, firstStep d ε x e * f (y + e) =
      walkOp f y - ε * inner ℝ (unitDir (toSpace x)) (centralDiff f y) := by
  rw [inner_unitDir_centralDiff, sum_unitSteps]
  have hpair : ∀ i : Fin d,
      firstStep d ε x (unit i) * f (y + unit i) +
          firstStep d ε x (-unit i) * f (y + -unit i) =
        (1 / (2 * d)) * (f (y + unit i) + f (y - unit i)) -
          ε * (((x i : ℤ) : ℝ) / euclidNorm x) *
            ((f (y + unit i) - f (y - unit i)) / 2) := by
    intro i
    rw [firstStep_unit, firstStep_neg_unit, sub_eq_add_neg]
    ring_nf
  have hA : ∑ i : Fin d, (1 / (2 * d)) * (f (y + unit i) + f (y - unit i)) =
      walkOp f y := by
    rw [← Finset.mul_sum, walkOp, nbrSum, div_eq_mul_inv]
    ring
  have hB : ∑ i : Fin d, ε * (((x i : ℤ) : ℝ) / euclidNorm x) *
        ((f (y + unit i) - f (y - unit i)) / 2) =
      ε * ((euclidNorm x)⁻¹ * ∑ i : Fin d,
        (((x i : ℤ) : ℝ) * ((f (y + unit i) - f (y - unit i)) / 2))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]; ring
  simp_rw [hpair, Finset.sum_sub_distrib, hA, hB]

/-- The mean of `f` after the next step of the path `x` at time `n`: a simple random walk mean,
corrected by `-ε u · D f` at a first departure from a nonzero site. -/
theorem sum_stepProb_mul (ε : ℝ) (x : ℕ → Site d) (n : ℕ) (f : Site d → ℝ) :
    ∑ e ∈ unitSteps d, stepProb d ε x n e * f (x n + e) =
      walkOp f (x n) - (if x n ≠ 0 ∧ x n ∉ (Finset.range n).image x then
        ε * inner ℝ (unitDir (toSpace (x n))) (centralDiff f (x n)) else 0) := by
  unfold stepProb
  split_ifs with h
  · rw [sum_firstStep_mul]
  · rw [sum_srwStep_mul]
    ring

end CERW.Support.Law
