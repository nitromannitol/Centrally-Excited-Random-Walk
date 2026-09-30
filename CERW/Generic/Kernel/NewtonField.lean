import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Newtonian field

The field `K(v) = v/|v|^d` of the proof of `lem:geometry`, with `K(0) = 0`. The potential's
integrand is `u_v · K(v - y)`. Its size is `|v|^{1-d}`, and away from the singularity it is
Lipschitz at scale `|v|`: `|K(a) - K(b)| ≤ C_d |a - b| |b|^{-d}` when `|a - b| ≤ |b|/2`.
This is the far-field estimate behind `eq:kernel-modulus`.
-/

namespace CERW.Generic.Kernel

variable {d : ℕ}

/-- The Newtonian field `K(v) = v/|v|^d`, which is `0` at `v = 0`. -/
noncomputable def newtonField (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (‖v‖ ^ d)⁻¹ • v

/-- The potential's integrand is the inner product with the Newtonian field. -/
theorem inner_newtonField (u a : EuclideanSpace ℝ (Fin d)) :
    inner ℝ u (newtonField a) = inner ℝ u a / ‖a‖ ^ d := by
  rw [newtonField, real_inner_smul_right, div_eq_inv_mul]

/-- For `d ≥ 2`, `|K(v)| = |v|^{1-d}`, including at `v = 0` where both sides vanish. -/
theorem norm_newtonField (hd : 2 ≤ d) (v : EuclideanSpace ℝ (Fin d)) :
    ‖newtonField v‖ = ‖v‖ ^ (1 - (d : ℝ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [newtonField, norm_zero, zero_pow (by omega : d ≠ 0), inv_zero, zero_smul, norm_zero]
    exact (Real.zero_rpow (by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)).symm
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    rw [newtonField, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg v) d))]
    rw [Real.rpow_sub hvpos, Real.rpow_one, Real.rpow_natCast, div_eq_inv_mul, mul_comm]

/-- The first term in the decomposition of `K(a) - K(b)`: since `α ≥ β/2`,
`(α^d)⁻¹ δ ≤ 2^d δ / β^d`. -/
lemma inv_pow_mul_le {α β δ : ℝ} {d : ℕ} (hβ : 0 < β) (hα : β / 2 ≤ α)
    (hδ : 0 ≤ δ) : (α ^ d)⁻¹ * δ ≤ (2 : ℝ) ^ d * δ / β ^ d := by
  have hαpos : 0 < α := by linarith
  have hpow : (β / 2) ^ d ≤ α ^ d :=
    pow_le_pow_left₀ (by positivity) hα d
  have hpowpos : 0 < (β / 2) ^ d := by positivity
  have hinv : (α ^ d)⁻¹ ≤ (2 : ℝ) ^ d / β ^ d := by
    calc (α ^ d)⁻¹ ≤ ((β / 2) ^ d)⁻¹ :=
          (inv_le_inv₀ (pow_pos hαpos d) hpowpos).mpr hpow
      _ = ((β / 2)⁻¹) ^ d := (inv_pow (β / 2) d).symm
      _ = (2 / β) ^ d := by rw [inv_div]
      _ = (2 : ℝ) ^ d / β ^ d := by rw [div_pow]
  calc (α ^ d)⁻¹ * δ ≤ ((2 : ℝ) ^ d / β ^ d) * δ :=
        mul_le_mul_of_nonneg_right hinv hδ
    _ = (2 : ℝ) ^ d * δ / β ^ d := by ring

/-- The second term in the decomposition of `K(a) - K(b)`: the reciprocal-power
difference times `β` is controlled by `2 d 3^{d-1} δ / β^d`. -/
lemma inv_pow_sub_inv_pow_mul_le {α β δ : ℝ} {d : ℕ} (hd : 1 ≤ d) (hβ : 0 < β)
    (hα : β / 2 ≤ α) (hα' : α ≤ 3 * β / 2) (hδ : |α - β| ≤ δ) :
    |(α ^ d)⁻¹ - (β ^ d)⁻¹| * β
      ≤ 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) * δ / β ^ d := by
  have hαpos : 0 < α := by linarith
  have hδnonneg : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hαd_ne : α ^ d ≠ 0 := pow_ne_zero d hαpos.ne'
  have hβd_ne : β ^ d ≠ 0 := pow_ne_zero d hβ.ne'
  have hsub : (α ^ d)⁻¹ - (β ^ d)⁻¹ = (β ^ d - α ^ d) / (α ^ d * β ^ d) :=
    inv_sub_inv hαd_ne hβd_ne
  have hpow : |β ^ d - α ^ d| ≤ δ * (d : ℝ) * (3 * β / 2) ^ (d - 1) := by
    have h1 : |β ^ d - α ^ d| ≤ |β - α| * (d : ℝ) * max |β| |α| ^ (d - 1) :=
      abs_pow_sub_pow_le (a := β) (b := α) (n := d)
    have h2 : |β - α| ≤ δ := by rw [abs_sub_comm]; exact hδ
    have h3 : max |β| |α| = max β α := by rw [abs_of_pos hβ, abs_of_pos hαpos]
    have h4 : max β α ≤ 3 * β / 2 := max_le (by linarith) hα'
    calc |β ^ d - α ^ d|
        ≤ |β - α| * (d : ℝ) * max |β| |α| ^ (d - 1) := h1
      _ = |β - α| * (d : ℝ) * max β α ^ (d - 1) := by rw [h3]
      _ ≤ δ * (d : ℝ) * (3 * β / 2) ^ (d - 1) := by
          gcongr
  rw [hsub, abs_div, abs_of_pos (by positivity : (0 : ℝ) < α ^ d * β ^ d)]
  have hαd : (β / 2) ^ d ≤ α ^ d := pow_le_pow_left₀ (by positivity) hα d
  have hnum : 0 ≤ δ * (d : ℝ) * (3 * β / 2) ^ (d - 1) :=
    mul_nonneg (mul_nonneg hδnonneg (Nat.cast_nonneg d)) (by positivity)
  calc |β ^ d - α ^ d| / (α ^ d * β ^ d) * β
      ≤ (δ * (d : ℝ) * (3 * β / 2) ^ (d - 1)) / (α ^ d * β ^ d) * β := by
        gcongr
    _ ≤ (δ * (d : ℝ) * (3 * β / 2) ^ (d - 1)) / ((β / 2) ^ d * β ^ d) * β := by
        gcongr
    _ = 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) * δ / β ^ d := by
        have hβpow : β ^ d = β ^ (d - 1) * β := by
          conv_lhs => rw [← Nat.sub_add_cancel hd]
          rw [pow_succ]
        have h2pow : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by
          conv_lhs => rw [← Nat.sub_add_cancel hd]
          rw [pow_succ]
        have h3β : (3 * β / 2) = (3 : ℝ) / 2 * β := by ring
        have hβ2 : (β / 2) = (1 : ℝ) / 2 * β := by ring
        rw [h3β, hβ2]
        simp only [mul_pow, div_pow, one_pow]
        rw [hβpow, h2pow]
        field_simp

/-- Scalar form of the far-field bound: for `α` in `[β/2, 3β/2]` and
`|α - β| ≤ δ`, the two terms of the decomposition satisfy the stated bound. -/
lemma scalar_bound {α β δ : ℝ} {d : ℕ} (hβ : 0 < β) (hα : β / 2 ≤ α)
    (hα' : α ≤ 3 * β / 2) (hδ : |α - β| ≤ δ) :
    (α ^ d)⁻¹ * δ + |(α ^ d)⁻¹ - (β ^ d)⁻¹| * β
      ≤ ((2 : ℝ) ^ d + 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * δ / β ^ d := by
  by_cases hd0 : d = 0
  · subst d
    simp
  · have hd : 1 ≤ d := by omega
    have hδnonneg : 0 ≤ δ := (abs_nonneg _).trans hδ
    have hA := inv_pow_mul_le (α := α) (β := β) (δ := δ) (d := d) hβ hα hδnonneg
    have hB := inv_pow_sub_inv_pow_mul_le (α := α) (β := β) (δ := δ) (d := d)
      hd hβ hα hα' hδ
    have hsum : (α ^ d)⁻¹ * δ + |(α ^ d)⁻¹ - (β ^ d)⁻¹| * β
        ≤ (2 : ℝ) ^ d * δ / β ^ d
          + 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) * δ / β ^ d :=
      add_le_add hA hB
    calc (α ^ d)⁻¹ * δ + |(α ^ d)⁻¹ - (β ^ d)⁻¹| * β
        ≤ (2 : ℝ) ^ d * δ / β ^ d
          + 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) * δ / β ^ d := hsum
      _ = ((2 : ℝ) ^ d + 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * δ / β ^ d := by ring

/-- If `|a - b| ≤ |b|/2`, then `|K(a) - K(b)| ≤ (2^d + 2d·3^{d-1}) |a - b| / |b|^d`. -/
theorem norm_newtonField_sub_le {a b : EuclideanSpace ℝ (Fin d)} (h : 2 * ‖a - b‖ ≤ ‖b‖) :
    ‖newtonField a - newtonField b‖
      ≤ (2 ^ d + 2 * d * 3 ^ (d - 1)) * ‖a - b‖ / ‖b‖ ^ d := by
  by_cases hb : b = 0
  · subst b
    have ha : a = 0 := by
      have : ‖a‖ = 0 := by
        have h2 : 2 * ‖a‖ ≤ 0 := by simpa using h
        nlinarith [norm_nonneg a]
      exact norm_eq_zero.mp this
    subst a
    simp [newtonField]
  · have hβpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hδle : ‖a - b‖ ≤ ‖b‖ / 2 := by linarith
    have hαlower : ‖b‖ / 2 ≤ ‖a‖ := by
      have h2 : -‖a - b‖ ≤ ‖a‖ - ‖b‖ := (abs_le.mp (abs_norm_sub_norm_le a b)).1
      linarith
    have hαupper : ‖a‖ ≤ 3 * ‖b‖ / 2 := by
      have h1 : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := (abs_le.mp (abs_norm_sub_norm_le a b)).2
      linarith
    have hdec : newtonField a - newtonField b
        = (‖a‖ ^ d)⁻¹ • (a - b) + ((‖a‖ ^ d)⁻¹ - (‖b‖ ^ d)⁻¹) • b := by
      rw [newtonField]
      simp only [smul_sub, sub_smul]
      abel
    rw [hdec]
    calc ‖(‖a‖ ^ d)⁻¹ • (a - b) + ((‖a‖ ^ d)⁻¹ - (‖b‖ ^ d)⁻¹) • b‖
        ≤ ‖(‖a‖ ^ d)⁻¹ • (a - b)‖
            + ‖((‖a‖ ^ d)⁻¹ - (‖b‖ ^ d)⁻¹) • b‖ :=
          norm_add_le _ _
      _ = (‖a‖ ^ d)⁻¹ * ‖a - b‖
            + |(‖a‖ ^ d)⁻¹ - (‖b‖ ^ d)⁻¹| * ‖b‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg a) d))]
      _ ≤ ((2 : ℝ) ^ d + 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1)) * ‖a - b‖ / ‖b‖ ^ d :=
          scalar_bound hβpos hαlower hαupper (abs_norm_sub_norm_le a b)
      _ = (2 ^ d + 2 * d * 3 ^ (d - 1)) * ‖a - b‖ / ‖b‖ ^ d := by
          ring

end CERW.Generic.Kernel
