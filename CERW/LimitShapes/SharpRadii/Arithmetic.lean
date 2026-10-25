module

public import CERW.LimitShapes.SharpRadii.Deviation

@[expose] public section

/-!
# Deterministic thresholds for the coarse radius argument

These estimates normalize the martingale at scale `r^(5/2)` and absorb the
bounded radius comparison errors in Theorem 1.3(i).
-/

namespace CERW.LimitShapes.SharpRadii

open private sqrt_pow_five from CERW.Support.Lower.SharpRadii

/-- A logarithmic lower bound becomes a square-root lower bound. -/
theorem le_mul_sqrt_of_sq_le {x c L : ℝ} (hc : 0 < c) (hx : 0 ≤ x)
    (h : (x / c) ^ 2 ≤ L) : x ≤ c * Real.sqrt L := by
  have hh : x / c ≤ Real.sqrt L := by
    calc
      _ = Real.sqrt ((x / c) ^ 2) := (Real.sqrt_sq (div_nonneg hx hc.le)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h
  have ht := (div_le_iff₀ hc).mp hh
  linarith

/-- The deterministic increment condition at an arbitrary coarse radius. -/
theorem coarse_increment_scale {r k a c L : ℝ} (hr : 1 ≤ r)
    (ha : 0 < a) (h : (4 * k + 2) * a * Real.sqrt L ≤ c * (r * Real.sqrt r)) :
    a * Real.sqrt L * ((Real.sqrt (r ^ 5))⁻¹ * (2 * (2 * (k * r) + 1))) ≤ c := by
  have hr0 : 0 < r := by linarith
  have hp : 0 < r ^ 2 * Real.sqrt r := by positivity
  rw [sqrt_pow_five r]
  have hinc : 2 * (2 * (k * r) + 1) ≤ (4 * k + 2) * r := by linarith
  have ht := mul_le_mul_of_nonneg_left hinc (by positivity : 0 ≤ a * Real.sqrt L)
  have hh := mul_le_mul_of_nonneg_right h hr0.le
  have he : a * Real.sqrt L * ((r ^ 2 * Real.sqrt r)⁻¹ *
      (2 * (2 * (k * r) + 1))) =
      (a * Real.sqrt L * (2 * (2 * (k * r) + 1))) / (r ^ 2 * Real.sqrt r) := by
    ring
  rw [he, div_le_iff₀ hp]
  nlinarith only [ht, hh]

/-- The quadratic position error is absorbed at large logarithmic threshold. -/
theorem coarse_position_scale {r k a c L : ℝ} (hr : 1 ≤ r)
    (h : 2 * k ^ 2 ≤ c * a * Real.sqrt L) :
    2 * (k * r) ^ 2 ≤ c * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹ := by
  rw [div_inv_eq_mul, sqrt_pow_five r]
  have hsr : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hh : 0 ≤ c * a * Real.sqrt L := (by positivity : 0 ≤ 2 * k ^ 2).trans h
  have h1 := mul_le_mul_of_nonneg_right h (sq_nonneg r)
  have h2 := mul_le_mul_of_nonneg_left hsr (mul_nonneg hh (sq_nonneg r))
  nlinarith only [h1, h2]

/-- The cubic thresholds exceed a common positive multiple of `√(r L)`. -/
theorem coarse_thresholds {ε w c a r L B CS CI : ℝ}
    (hε : 0 < ε) (hw : 0 < w) (hr : 0 < r) (hc : 0 < c) (ha : 0 < a)
    (hD : 1 ≤ B ^ 2 + B + 1)
    (hCS : CS ≤ (c * a / (8 * ε * w * (B ^ 2 + B + 1))) / 2 * Real.sqrt (r * L))
    (hCI : CI ≤ (c * a / (8 * ε * w * (B ^ 2 + B + 1))) / 2 * Real.sqrt (r * L)) :
    (c * a / (8 * ε * w * (B ^ 2 + B + 1))) / 2 * Real.sqrt (r * L) ≤
      3 * (c * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹) /
        (8 * ε * w * (B ^ 2 + B + 1) * r ^ 2) - CS ∧
    (c * a / (8 * ε * w * (B ^ 2 + B + 1))) / 2 * Real.sqrt (r * L) ≤
      (c * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹) / (4 * ε * w * r ^ 2) - CI := by
  have hD0 : 0 < B ^ 2 + B + 1 := by linarith
  have he : c * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹ =
      c * a * Real.sqrt L * (r ^ 2 * Real.sqrt r) := by
    rw [div_inv_eq_mul, sqrt_pow_five r]
    ring
  have h1 : 3 * (c * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹) /
      (8 * ε * w * (B ^ 2 + B + 1) * r ^ 2) =
      3 * (c * a / (8 * ε * w * (B ^ 2 + B + 1))) * Real.sqrt (r * L) := by
    rw [he, Real.sqrt_mul hr.le]
    field_simp
  have h2 : (c * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹) /
      (4 * ε * w * r ^ 2) = c * a / (4 * ε * w) * Real.sqrt (r * L) := by
    rw [he, Real.sqrt_mul hr.le]
    field_simp
  have hcoef : c * a / (8 * ε * w * (B ^ 2 + B + 1)) ≤ c * a / (4 * ε * w) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith only [hD, mul_pos hε hw]
  have ht := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (r * L))
  have hp : 0 ≤ c * a / (8 * ε * w * (B ^ 2 + B + 1)) * Real.sqrt (r * L) := by
    positivity
  rw [h1, h2]
  constructor <;> linarith

end CERW.LimitShapes.SharpRadii
