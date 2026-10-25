module

public import CERW.LimitShapes.Exit.Bootstrap
public import CERW.LimitShapes.Exit.Probability

@[expose] public section

/-!
# Polynomial horizons for the exit estimate

Deterministic comparisons for the larger horizon used in Proposition `prop:coarse`.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb

/-- A polynomial ceiling has the required size and logarithm for the exit bootstrap. -/
theorem exit_horizon_bounds (d : ℕ) {R B ρ : ℝ}
    (hR : 2 ≤ R) (hB : B + 1 ≤ R) (hρ : ρ ≤ R) :
    let N := ⌈R ^ (d + 2)⌉₊
    2 ≤ N ∧ R ≤ (N : ℝ) ∧ B * R ^ (d + 1) < (N : ℝ) ∧
      ρ * R ≤ 3 * (N : ℝ) ∧ Real.log N ≤ (d + 3 : ℝ) * Real.log R := by
  dsimp only
  let N := ⌈R ^ (d + 2)⌉₊
  have hR1 : 1 ≤ R := by linarith
  have hRp : 0 < R := by linarith
  have hP : 1 ≤ R ^ (d + 2) := one_le_pow₀ hR1
  have hceil : R ^ (d + 2) ≤ (N : ℝ) := Nat.le_ceil _
  have hRN : R ≤ (N : ℝ) :=
    (le_self_pow₀ hR1 (by omega : d + 2 ≠ 0)).trans hceil
  have hN2 : 2 ≤ N := by exact_mod_cast hR.trans hRN
  have hBN : B * R ^ (d + 1) < (N : ℝ) := by
    calc B * R ^ (d + 1) < R * R ^ (d + 1) :=
        mul_lt_mul_of_pos_right (by linarith) (pow_pos hRp _)
      _ = R ^ (d + 2) := by rw [pow_succ]; ring
      _ ≤ (N : ℝ) := hceil
  have hρN : ρ * R ≤ 3 * (N : ℝ) := by
    have hsq : R ^ 2 ≤ R ^ (d + 2) := pow_le_pow_right₀ hR1 (by omega)
    nlinarith [mul_le_mul_of_nonneg_right hρ hRp.le]
  have hupper : (N : ℝ) ≤ R ^ (d + 3) := by
    have hc : (N : ℝ) < R ^ (d + 2) + 1 := Nat.ceil_lt_add_one (by positivity)
    calc (N : ℝ) ≤ R ^ (d + 2) + 1 := hc.le
      _ ≤ R ^ (d + 2) * R := by nlinarith
      _ = R ^ (d + 3) := (pow_succ R (d + 2)).symm
  refine ⟨hN2, hRN, hBN, hρN, ?_⟩
  have hn : (0 : ℝ) < N := lt_of_lt_of_le hRp hRN
  simpa only [Real.log_pow, Nat.cast_add, Nat.cast_ofNat] using
    Real.log_le_log hn hupper

/-- Replacing the horizon logarithm enlarges the Freedman coefficient linearly. -/
theorem freedman_log_comparison {V L l k : ℝ} (hL : 0 ≤ L) (hl : 0 ≤ l)
    (hk : 1 ≤ k) (hLl : L ≤ k * l) :
    Real.sqrt (V * L) + L ≤ k * (Real.sqrt (V * l) + l) := by
  have hs : Real.sqrt (V * L) ≤ k * Real.sqrt (V * l) := by
    by_cases hV : 0 ≤ V
    · calc Real.sqrt (V * L) ≤ Real.sqrt (k ^ 2 * (V * l)) := by
            apply Real.sqrt_le_sqrt
            have hkk : k ≤ k ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_left hLl hV,
              mul_le_mul_of_nonneg_right hkk (mul_nonneg hV hl)]
          _ = k * Real.sqrt (V * l) := by
            rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq (by linarith : 0 ≤ k)]
    · rw [Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hV) hL)]
      positivity
  nlinarith

end CERW.LimitShapes.Exit
