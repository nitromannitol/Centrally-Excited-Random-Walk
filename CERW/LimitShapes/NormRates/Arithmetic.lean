module

public import CERW.LimitShapes.NormRates.Normalization

@[expose] public section

/-!
# Radius rates from the quadratic radius-volume estimate

The shell bound controls excess volume. The normalized quadratic estimate then
controls the inner radius, as in Proposition `prop:norm-shape`.
-/

open CERW.Support.Norm
open private rateQ
  RateInequalities.rateQ_pos RateInequalities.rateQ_le_one
  RateInequalities.div_le_rateQ RateInequalities.pow_mul_abs_sub_le
  from CERW.Support.Norm.ShapeRates

namespace CERW.LimitShapes.NormRates

/-- The quadratic fluctuation and cell error are bounded by the inner radius rate. -/
theorem quadratic_errors_le_rate {d : ℕ} (hd : 2 ≤ d) {r ℓ : ℝ}
    (hr : 1 ≤ r) (hℓ : 1 ≤ ℓ) (hℓr : ℓ ≤ r) :
    r ^ ((1 - (d : ℝ)) / 2) * Real.sqrt ℓ ≤ rateQ d r ℓ ^ ((1 : ℝ) / 2) ∧
      r⁻¹ ≤ rateQ d r ℓ ^ ((1 : ℝ) / 2) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hq0 := RateInequalities.rateQ_pos d hr0 hℓ0
  have hq1 := RateInequalities.rateQ_le_one d hr0 hℓr
  have hdiv := RateInequalities.div_le_rateQ d hr0 hℓ0 hℓr
  have hhalf : rateQ d r ℓ ≤ rateQ d r ℓ ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt hq0.le hq0.le).2 (pow_le_of_le_one hq0.le hq1 two_ne_zero)
  have hroot : r ^ (-(1 / 2 : ℝ)) * Real.sqrt ℓ = Real.sqrt (ℓ / r) := by
    rw [Real.sqrt_div hℓ0.le, Real.sqrt_eq_rpow r, Real.rpow_neg hr0.le]
    ring
  constructor
  · calc r ^ ((1 - (d : ℝ)) / 2) * Real.sqrt ℓ
        ≤ r ^ (-(1 / 2 : ℝ)) * Real.sqrt ℓ := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          apply Real.rpow_le_rpow_of_exponent_le hr
          have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
          linarith
      _ = Real.sqrt (ℓ / r) := hroot
      _ ≤ rateQ d r ℓ ^ ((1 : ℝ) / 2) := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_sqrt hdiv
  · calc r⁻¹ = 1 / r := (one_div r).symm
      _ ≤ ℓ / r := div_le_div_of_nonneg_right hℓ hr0.le
      _ ≤ rateQ d r ℓ := hdiv
      _ ≤ _ := hhalf

/-- The radius-volume comparison and the shell-volume estimate give the inner radius rate. -/
theorem inner_radius_rate_of_radius_volume {d : ℕ} (hd : 2 ≤ d)
    {r b ℓ Ev C CE : ℝ} (hr : 1 ≤ r) (hb : 0 ≤ b) (hℓ : 1 ≤ ℓ) (hℓr : ℓ ≤ r)
    (hC : 0 ≤ C)
    (hEv : Ev ≤ CE * (r ^ d * rateQ d r ℓ ^ ((1 : ℝ) / 2)))
    (hcmp : |1 - (b / r) ^ (d + 1)| ≤ C *
      (r ^ ((1 - (d : ℝ)) / 2) * Real.sqrt ℓ + r⁻¹ + Ev * r ^ (-(d : ℝ)))) :
    |b - r| ≤ (C * (2 + CE)) * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  obtain ⟨hfluc, hinv⟩ := quadratic_errors_le_rate hd hr hℓ hℓr
  have hE : Ev * r ^ (-(d : ℝ)) ≤ CE * rateQ d r ℓ ^ ((1 : ℝ) / 2) := by
    calc _ ≤ CE * (r ^ d * rateQ d r ℓ ^ ((1 : ℝ) / 2)) * r ^ (-(d : ℝ)) :=
          mul_le_mul_of_nonneg_right hEv (Real.rpow_nonneg hr0.le _)
      _ = _ := by rw [Real.rpow_neg hr0.le, Real.rpow_natCast]; field_simp
  have hnorm := (RateInequalities.pow_mul_abs_sub_le d zero_lt_one (div_nonneg hb hr0.le))
  simp only [one_pow, one_mul] at hnorm
  have hid : |b - r| = r * |1 - b / r| := by
    rw [abs_sub_comm b r, ← abs_of_pos hr0, ← abs_mul]
    congr 1
    rw [abs_of_pos hr0]
    field_simp
  rw [hid]
  calc r * |1 - b / r| ≤ r * |1 - (b / r) ^ (d + 1)| :=
      mul_le_mul_of_nonneg_left hnorm hr0.le
    _ ≤ r * (C * (r ^ ((1 - (d : ℝ)) / 2) * Real.sqrt ℓ + r⁻¹ +
        Ev * r ^ (-(d : ℝ)))) := mul_le_mul_of_nonneg_left hcmp hr0.le
    _ ≤ r * (C * (rateQ d r ℓ ^ ((1 : ℝ) / 2) +
        rateQ d r ℓ ^ ((1 : ℝ) / 2) + CE * rateQ d r ℓ ^ ((1 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hfluc hinv) hE) hC) hr0.le
    _ = _ := by ring

end CERW.LimitShapes.NormRates
