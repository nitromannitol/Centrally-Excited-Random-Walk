module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Error scales for the lower exit bound

The excess potential error in Proposition `prop:coarse` is negligible even after multiplication
by the crossing logarithm.
-/

namespace CERW.LimitShapes.Exit

open Filter Asymptotics

/-- Any fixed logarithmic power times a sublinear power is eventually small relative to `R`. -/
theorem eventually_rpow_mul_log_rpow_le {α β K η : ℝ} (hα : α < 1)
    (hK : 0 ≤ K) (hη : 0 < η) :
    ∀ᶠ R : ℝ in atTop, K * R ^ α * (Real.log R) ^ β ≤ η * R := by
  have he := (isLittleO_log_rpow_rpow_atTop β (sub_pos.mpr hα)).bound
    (show 0 < η / (K + 1) by positivity)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with R hR hR1
  have hR0 : 0 < R := by linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hR1) _),
    Real.norm_of_nonneg (Real.rpow_nonneg hR0.le _)] at hR
  have hp : R ^ α * R ^ (1 - α) = R := by
    rw [← Real.rpow_add hR0, show α + (1 - α) = 1 by ring, Real.rpow_one]
  have hcoef : K * (η / (K + 1)) ≤ η := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (by positivity : 0 < K + 1)).mpr (by nlinarith)
  calc
    K * R ^ α * (Real.log R) ^ β ≤
        K * R ^ α * (η / (K + 1) * R ^ (1 - α)) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = (K * (η / (K + 1))) * (R ^ α * R ^ (1 - α)) := by ring
    _ = (K * (η / (K + 1))) * R := by rw [hp]
    _ ≤ η * R := mul_le_mul_of_nonneg_right hcoef hR0.le

/-- The approximation error and the excess-root error are `o(R / log R)`. -/
theorem eventually_lower_error_small (d : ℕ) {A Cerr C η : ℝ}
    (hA : 0 ≤ A) (hCerr : 0 ≤ Cerr) (hC : 0 ≤ C) (hη : 0 < η) :
    ∀ᶠ R : ℝ in atTop,
      (1 + (Cerr * Real.sqrt R * Real.log R +
        C * (A * R ^ d * (Cerr * Real.sqrt R * Real.log R)) ^
          ((1 : ℝ) / (d + 1)))) * Real.log R ≤ η * R := by
  let p : ℝ := 1 / ((d : ℝ) + 1)
  let α : ℝ := ((d : ℝ) + 1 / 2) * p
  have hp : 0 < p := by dsimp [p]; positivity
  have hα : α < 1 := by
    dsimp [α, p]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  have he₁ := eventually_rpow_mul_log_rpow_le (α := 0) (β := 1) (K := 1)
    (by norm_num) (by norm_num) (show 0 < η / 3 by positivity)
  have he₂ := eventually_rpow_mul_log_rpow_le (α := 1 / 2) (β := 2) (K := Cerr)
    (by norm_num) hCerr (show 0 < η / 3 by positivity)
  have he₃ := eventually_rpow_mul_log_rpow_le (α := α) (β := p + 1)
    (K := C * (A * Cerr) ^ p) hα (by positivity) (show 0 < η / 3 by positivity)
  filter_upwards [he₁, he₂, he₃, eventually_ge_atTop (1 : ℝ)] with R h₁ h₂ h₃ hR
  have hR0 : 0 < R := by linarith
  have hl : 0 ≤ Real.log R := Real.log_nonneg hR
  have hs : (A * R ^ d * (Cerr * Real.sqrt R * Real.log R)) ^ p =
      (A * Cerr) ^ p * R ^ α * (Real.log R) ^ p := by
    rw [Real.sqrt_eq_rpow]
    have heq : A * R ^ d * (Cerr * R ^ (1 / 2 : ℝ) * Real.log R) =
        (A * Cerr) * (R ^ ((d : ℝ) + 1 / 2)) * Real.log R := by
      rw [Real.rpow_add hR0, Real.rpow_natCast]
      ring
    rw [heq, Real.mul_rpow (by positivity) hl,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR0.le]
  have ht : (1 + (Cerr * Real.sqrt R * Real.log R +
      C * (A * R ^ d * (Cerr * Real.sqrt R * Real.log R)) ^ p)) * Real.log R =
      Real.log R + Cerr * R ^ (1 / 2 : ℝ) * (Real.log R) ^ (2 : ℝ) +
        (C * (A * Cerr) ^ p) * R ^ α * (Real.log R) ^ (p + 1) := by
    rw [hs, Real.sqrt_eq_rpow, Real.rpow_add' hl (by positivity : p + 1 ≠ 0),
      Real.rpow_one, Real.rpow_two]
    ring
  change (1 + (Cerr * Real.sqrt R * Real.log R +
    C * (A * R ^ d * (Cerr * Real.sqrt R * Real.log R)) ^ p)) * Real.log R ≤ η * R
  rw [ht]
  simp only [Real.rpow_zero, Real.rpow_one, mul_one, one_mul] at h₁
  linarith

end CERW.LimitShapes.Exit
