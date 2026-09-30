import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The cost of dyadic halving

The number of dyadic levels between `A₀` and a floor `Λ` is `O(log(A₀/Λ))`. The per-level
budgets `(A₀ 2^{-k} + δ)^α` with `0 < α ≤ 1` sum to at most a geometric series in `A₀^α` plus
`δ^α` per level (`eq:halving-cost`).
-/

namespace CERW.Generic.Halving

/-- The reciprocal of a dyadic power raised to `α` is the `k`-th power of `2^{-α}`. -/
lemma inv_pow_two_rpow (α : ℝ) (k : ℕ) :
    (((2 : ℝ) ^ k) ^ α)⁻¹ = ((2 : ℝ) ^ (-α)) ^ k := by
  have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have h2knonneg : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
  rw [← Real.rpow_neg h2knonneg α, ← Real.rpow_natCast (2 : ℝ) k,
    ← Real.rpow_mul h2nonneg (k : ℝ) (-α), mul_comm (k : ℝ) (-α),
    Real.rpow_mul h2nonneg (-α) (k : ℝ), Real.rpow_natCast]

/-- A single dyadic level raised to `α`: `(A / 2^k)^α = A^α * (2^{-α})^k`. -/
lemma div_pow_two_rpow {α A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    (A / 2 ^ k) ^ α = A ^ α * ((2 : ℝ) ^ (-α)) ^ k := by
  have h2kpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [Real.div_rpow hA (le_of_lt h2kpos) α, div_eq_mul_inv, inv_pow_two_rpow]

/-- Summing the halved powers factors out `A^α` against the geometric series of `2^{-α}`. -/
lemma sum_div_pow_two_rpow {α A : ℝ} (hA : 0 ≤ A) (M : ℕ) :
    ∑ k ∈ Finset.range M, (A / 2 ^ k) ^ α
      = A ^ α * ∑ k ∈ Finset.range M, ((2 : ℝ) ^ (-α)) ^ k := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => div_pow_two_rpow hA k

/-- The finite geometric sum `Σ_{k<M} (2^{-α})^k` is at most `1/(1-2^{-α})` for `α > 0`. -/
lemma sum_pow_rpow_neg_le {α : ℝ} (hα0 : 0 < α) (M : ℕ) :
    ∑ k ∈ Finset.range M, ((2 : ℝ) ^ (-α)) ^ k ≤ 1 / (1 - (2 : ℝ) ^ (-α)) := by
  have h2one : (1 : ℝ) < 2 := by norm_num
  have hq0 : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) (-α)
  have hq1 : (2 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg h2one (by linarith)
  have hqne : (2 : ℝ) ^ (-α) ≠ 1 := ne_of_lt hq1
  have hqsub : (2 : ℝ) ^ (-α) - 1 ≠ 0 := by linarith
  have h1qsub : (1 : ℝ) - (2 : ℝ) ^ (-α) ≠ 0 := by linarith
  have hgeom : ∑ k ∈ Finset.range M, ((2 : ℝ) ^ (-α)) ^ k
      = (1 - ((2 : ℝ) ^ (-α)) ^ M) / (1 - (2 : ℝ) ^ (-α)) := by
    rw [geom_sum_eq hqne M, div_eq_div_iff hqsub h1qsub]
    ring
  rw [hgeom]
  apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 1 - (2 : ℝ) ^ (-α))
  linarith [pow_nonneg (le_of_lt hq0) M]

/-- Between `A₀ > 0` and a floor `Λ > 0` there are at most `max 0 (log₂(A₀/Λ)) + 1` dyadic
levels. -/
theorem exists_halvings_le {A₀ Λ : ℝ} (hA₀ : 0 < A₀) (hΛ : 0 < Λ) :
    ∃ M : ℕ, A₀ / 2 ^ M ≤ Λ ∧ (M : ℝ) ≤ max 0 (Real.logb 2 (A₀ / Λ)) + 1 := by
  have hratio : 0 < A₀ / Λ := div_pos hA₀ hΛ
  have h2one : (1 : ℝ) < 2 := by norm_num
  set M : ℕ := ⌈max 0 (Real.logb 2 (A₀ / Λ))⌉₊ with hM
  refine ⟨M, ?_, ?_⟩
  · have hlog : A₀ / Λ ≤ (2 : ℝ) ^ M := by
      calc A₀ / Λ = (2 : ℝ) ^ Real.logb 2 (A₀ / Λ) :=
            (Real.rpow_logb (by norm_num) (by norm_num) hratio).symm
        _ ≤ (2 : ℝ) ^ max 0 (Real.logb 2 (A₀ / Λ)) :=
              Real.rpow_le_rpow_of_exponent_le (le_of_lt h2one) (le_max_right _ _)
        _ ≤ (2 : ℝ) ^ (M : ℝ) := by
              rw [hM]
              exact Real.rpow_le_rpow_of_exponent_le (le_of_lt h2one) (Nat.le_ceil _)
        _ = (2 : ℝ) ^ M := Real.rpow_natCast (2 : ℝ) M
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)]
    have hbound := (div_le_iff₀ hΛ).mp hlog
    linarith
  · rw [hM]
    exact le_of_lt (Nat.ceil_lt_add_one (le_max_left _ _))

/-- For `0 < α ≤ 1`, `Σ_{k < M} (A 2^{-k} + δ)^α ≤ A^α / (1 - 2^{-α}) + M δ^α`. -/
theorem sum_rpow_halvings_le {α A δ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (M : ℕ) :
    ∑ k ∈ Finset.range M, (A / 2 ^ k + δ) ^ α ≤ A ^ α / (1 - (2 : ℝ) ^ (-α)) + M * δ ^ α := by
  calc
    ∑ k ∈ Finset.range M, (A / 2 ^ k + δ) ^ α
        ≤ ∑ k ∈ Finset.range M, ((A / 2 ^ k) ^ α + δ ^ α) :=
          Finset.sum_le_sum fun k _ =>
            Real.rpow_add_le_add_rpow (by positivity) hδ (le_of_lt hα0) hα1
    _ = (∑ k ∈ Finset.range M, (A / 2 ^ k) ^ α) + ∑ k ∈ Finset.range M, δ ^ α := by
          rw [Finset.sum_add_distrib]
    _ = A ^ α * (∑ k ∈ Finset.range M, ((2 : ℝ) ^ (-α)) ^ k)
          + ∑ k ∈ Finset.range M, δ ^ α := by
          rw [sum_div_pow_two_rpow hA M]
    _ ≤ A ^ α * (1 / (1 - (2 : ℝ) ^ (-α))) + M * δ ^ α := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (sum_pow_rpow_neg_le hα0 M) (Real.rpow_nonneg hA α)
          · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            exact le_rfl
    _ = A ^ α / (1 - (2 : ℝ) ^ (-α)) + M * δ ^ α := by
          rw [mul_one_div]

end CERW.Generic.Halving
