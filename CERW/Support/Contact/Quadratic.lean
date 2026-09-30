import CERW.Support.Law.Dynkin
import CERW.Support.Law.StepMean
import CERW.Support.Occupation.FreshSum

/-!
# The squared displacement

`eq:quadratic`: `|X_n|² = n - 2ε Σ_{x ∈ A_n} |x| + 𝒬_n`, where `𝒬` is the Dynkin martingale
of `x ↦ |x|²`. The simple random walk raises `|x|²` by exactly `1` in mean. The central
difference of `|x|²` is `2x`, so at a first departure from `x ≠ 0` the drift `-ε u_x` lowers the
mean by `2ε u_x · x = 2ε |x|`. First departures sum over the departure range, and `u_0 = 0`.
-/

namespace CERW.Support.Contact

open LatticeProb Finset CERW CERW.Support.Law CERW.Support.Occupation

variable {d : ℕ}

/-- The square of the Euclidean norm is the sum of the squared coordinates. -/
private theorem euclidNorm_sq_eq_sum (x : Site d) :
    euclidNorm x ^ 2 = ∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2 := by
  rw [euclidNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The Euclidean norm of the origin is zero. -/
private theorem euclidNorm_zero : euclidNorm (0 : Site d) = 0 := by
  simp [euclidNorm]

/-- Shifting by `+unit i` changes only the `i`-th coordinate by `+1`. -/
private theorem euclidNorm_add_unit_sq (x : Site d) (i : Fin d) :
    euclidNorm (x + unit i) ^ 2 = euclidNorm x ^ 2 + 2 * ((x i : ℤ) : ℝ) + 1 := by
  rw [euclidNorm_sq_eq_sum, euclidNorm_sq_eq_sum]
  have hpoint : ∀ j : Fin d,
      (((x + unit i) j : ℤ) : ℝ) ^ 2 =
        (((x j : ℤ) : ℝ)) ^ 2 +
          (if j = i then 2 * ((x i : ℤ) : ℝ) + 1 else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [Pi.add_apply, unit, Pi.single_eq_same]
      simp only [if_true]
      push_cast
      ring
    · rw [Pi.add_apply, unit, Pi.single_eq_of_ne hji, add_zero]
      simp [hji]
  rw [Finset.sum_congr rfl fun j _ => hpoint j, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Shifting by `-unit i` changes only the `i`-th coordinate by `-1`. -/
private theorem euclidNorm_sub_unit_sq (x : Site d) (i : Fin d) :
    euclidNorm (x - unit i) ^ 2 = euclidNorm x ^ 2 - 2 * ((x i : ℤ) : ℝ) + 1 := by
  rw [euclidNorm_sq_eq_sum, euclidNorm_sq_eq_sum]
  have hpoint : ∀ j : Fin d,
      (((x - unit i) j : ℤ) : ℝ) ^ 2 =
        (((x j : ℤ) : ℝ)) ^ 2 +
          (if j = i then -2 * ((x i : ℤ) : ℝ) + 1 else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [Pi.sub_apply, unit, Pi.single_eq_same]
      simp only [if_true]
      push_cast
      ring
    · rw [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
      simp [hji]
  rw [Finset.sum_congr rfl fun j _ => hpoint j, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The inner product of `u_v = v/|v|` with `v` is `|v|`. -/
private theorem inner_unitDir_self (v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (unitDir v) v = ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [unitDir, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    field_simp

/-- The walk operator raises the squared norm by one: `P|·|²(x) = |x|² + 1`. -/
theorem walkOp_sq_euclidNorm (hd : 1 ≤ d) (x : Site d) :
    walkOp (fun z : Site d => euclidNorm z ^ 2) x = euclidNorm x ^ 2 + 1 := by
  rw [walkOp, nbrSum]
  have hpair : ∀ i : Fin d,
      euclidNorm (x + unit i) ^ 2 + euclidNorm (x - unit i) ^ 2 =
        2 * euclidNorm x ^ 2 + 2 := by
    intro i
    rw [euclidNorm_add_unit_sq, euclidNorm_sub_unit_sq]
    ring
  rw [Finset.sum_congr rfl fun i _ => hpair i]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd' : (d : ℝ) ≠ 0 := by
    have : 0 < d := Nat.pos_of_ne_zero (by omega)
    exact_mod_cast ne_of_gt this
  field_simp

/-- The central difference of the squared norm is `2x`. -/
theorem centralDiff_sq_euclidNorm (x : Site d) :
    centralDiff (fun z : Site d => euclidNorm z ^ 2) x = (2 : ℝ) • toSpace x := by
  rw [centralDiff]
  ext i
  rw [PiLp.toLp_apply, euclidNorm_add_unit_sq, euclidNorm_sub_unit_sq]
  simp only [PiLp.smul_apply, toSpace_apply, smul_eq_mul]
  ring

/-- At a nonzero site the inner product of `u_x` with `D|·|²(x) = 2x` is `2|x|`. -/
private theorem inner_unitDir_centralDiff_sq (x : Site d) :
    inner ℝ (unitDir (toSpace x))
        (centralDiff (fun z : Site d => euclidNorm z ^ 2) x) = 2 * euclidNorm x := by
  rw [centralDiff_sq_euclidNorm, inner_smul_right, inner_unitDir_self, norm_toSpace]

/-- The squared-norm increment of the next step is `1` minus `2ε|x_j|` at a first departure
from a nonzero site. -/
private theorem nextMean_sq_sub (hd : 1 ≤ d) (ε : ℝ) (x : ℕ → Site d) (j : ℕ) :
    nextMean ε (fun z : Site d => euclidNorm z ^ 2) x j - euclidNorm (x j) ^ 2 =
      1 - (if x j ≠ 0 ∧ x j ∉ (range j).image x then
        2 * ε * euclidNorm (x j) else 0) := by
  rw [show nextMean ε (fun z : Site d => euclidNorm z ^ 2) x j =
        walkOp (fun z : Site d => euclidNorm z ^ 2) (x j) -
          (if x j ≠ 0 ∧ x j ∉ (range j).image x then
            ε * inner ℝ (unitDir (toSpace (x j)))
              (centralDiff (fun z : Site d => euclidNorm z ^ 2) (x j)) else 0)
      from sum_stepProb_mul ε x j (fun z : Site d => euclidNorm z ^ 2)]
  rw [walkOp_sq_euclidNorm hd, inner_unitDir_centralDiff_sq]
  split_ifs <;> ring

/-- `eq:quadratic`, pathwise: for a path from the origin,
`|X_n|² = n - 2ε Σ_{x ∈ A_n} |x| + 𝒬_n` with `𝒬` the Dynkin martingale of `|·|²`. -/
theorem sq_euclidNorm_eq (hd : 1 ≤ d) (ε : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω)
    (h0 : X 0 ω = 0) (n : ℕ) :
    euclidNorm (X n ω) ^ 2 =
      n - 2 * ε * ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x +
        dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω := by
  have hfresh : ∑ j ∈ range n,
      (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω) then
        euclidNorm (X j ω) else 0) =
      ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x := by
    rw [sum_fresh_ne_zero_eq_sum_departureRange]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z = 0
    · subst hz
      simp
    · simp [hz]
  have hfact : ∑ j ∈ range n,
      (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω) then
        2 * ε * euclidNorm (X j ω) else 0) =
      2 * ε * ∑ j ∈ range n,
        (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω) then
          euclidNorm (X j ω) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω) <;> simp [hc]
  have hsum :
      ∑ j ∈ range n,
          (nextMean ε (fun z : Site d => euclidNorm z ^ 2) (fun i => X i ω) j -
            euclidNorm (X j ω) ^ 2) =
        n - 2 * ε * ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x := by
    simp_rw [nextMean_sq_sub hd ε (fun i => X i ω)]
    rw [Finset.sum_sub_distrib, hfact, hfresh]
    simp
  rw [dynkin, h0, euclidNorm_zero, hsum]
  ring

end CERW.Support.Contact
