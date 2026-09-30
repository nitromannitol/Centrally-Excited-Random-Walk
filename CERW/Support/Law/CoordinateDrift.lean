import CERW.Support.Law.Dynkin
import CERW.Support.Law.StepMean

/-!
# The drift of a coordinate

A coordinate `x ↦ x_k` is harmonic for the simple random walk, and its central difference is the
unit vector `e_k`. After a step of the walk its mean therefore drops by `ε (u_{X_t})_k` exactly at
a first departure from a nonzero site. This is the compensator of the vector martingale
`Z_t = X_t + ε Σ_{j<t} I_j u_{X_j}` of `eq:vector-def`.
-/

namespace CERW.Support.Law

open LatticeProb CERW

variable {d : ℕ}

/-- The `k`-th coordinate of the unit vector `unit i` is `1` when `i = k` and `0` otherwise. -/
lemma unit_apply_coord (i k : Fin d) : unit i k = if i = k then 1 else 0 := by
  rw [unit, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

/-- A coordinate is harmonic: `P x_k = x_k`. -/
theorem walkOp_coord (hd : 1 ≤ d) (k : Fin d) (y : Site d) :
    walkOp (fun x : Site d => ((x k : ℤ) : ℝ)) y = ((y k : ℤ) : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := by
    have : d ≠ 0 := by omega
    exact_mod_cast this
  have h2d : (2 * (d : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hd'
  have hterm : ∀ i : Fin d,
      (((y + unit i) k : ℤ) : ℝ) + (((y - unit i) k : ℤ) : ℝ) =
        2 * ((y k : ℤ) : ℝ) := by
    intro i
    rw [Pi.add_apply, Pi.sub_apply, unit_apply_coord i k]
    split_ifs <;> push_cast <;> ring
  have hsum : ∑ i : Fin d, 2 * ((y k : ℤ) : ℝ) = (2 * (d : ℝ)) * ((y k : ℤ) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [walkOp, nbrSum]
  simp_rw [hterm]
  rw [hsum, mul_div_cancel_left₀ _ h2d]

/-- The central difference of the `k`-th coordinate is the unit vector `e_k`. -/
theorem centralDiff_coord (k : Fin d) (y : Site d) :
    centralDiff (fun x : Site d => ((x k : ℤ) : ℝ)) y = EuclideanSpace.single k 1 := by
  ext i
  rw [centralDiff, PiLp.toLp_apply, PiLp.single_apply,
    Pi.add_apply, Pi.sub_apply, unit_apply_coord i k]
  split_ifs <;> push_cast <;> ring

/-- The next-step mean of the `k`-th coordinate is `x_k - ε (u_x)_k` at a first departure from
`x ≠ 0`, and `x_k` otherwise. -/
theorem nextMean_coord (hd : 1 ≤ d) (ε : ℝ) (x : ℕ → Site d) (t : ℕ) (k : Fin d) :
    nextMean ε (fun z : Site d => ((z k : ℤ) : ℝ)) x t =
      ((x t k : ℤ) : ℝ) - (if x t ≠ 0 ∧ x t ∉ (Finset.range t).image x then
        ε * unitDir (toSpace (x t)) k else 0) := by
  rw [nextMean, sum_stepProb_mul ε x t (fun z : Site d => ((z k : ℤ) : ℝ)),
    walkOp_coord hd, centralDiff_coord, EuclideanSpace.inner_single_right]
  simp

end CERW.Support.Law
