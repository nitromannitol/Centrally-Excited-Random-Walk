import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

/-!
# Absorbing a square root and a fractional power

Two real inequalities used to close estimates in which the unknown also appears on the right.
`M ≤ a + b √M` forces `M ≤ 2a + b²`; this is how `lem:local` absorbs the martingale term.
In the crossing estimate `eq:crossing-before-young`, the term `m L B k^{1/d}` is split by
Young's inequality with exponents `2d` and `2d/(2d-1)`, half of `(A k)²` absorbs it, and
`eq:crossing` remains.
-/

namespace CERW.Generic.Young

/-- If `0 ≤ M ≤ a + b √M` with `a, b ≥ 0`, then `M ≤ 2a + b²`. -/
theorem le_two_mul_add_sq_of_le_add_mul_sqrt {M a b : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h : M ≤ a + b * Real.sqrt M) : M ≤ 2 * a + b ^ 2 := by
  have hb_sqrt : 0 ≤ b * Real.sqrt M := mul_nonneg hb (Real.sqrt_nonneg M)
  have ha_two : 0 ≤ 2 * a := by linarith
  nlinarith [sq_nonneg (Real.sqrt M - b), Real.sq_sqrt hM, Real.sqrt_nonneg M, hb_sqrt, ha_two]

/-- If `0 ≤ u` and `0 ≤ c * v`, then `c * u + v ≤ (c + 1) * (u + v)`. -/
private lemma add_le_mul_add_one_mul {c u v : ℝ} (hu : 0 ≤ u) (hcv : 0 ≤ c * v) :
    c * u + v ≤ (c + 1) * (u + v) := by
  have h : (c + 1) * (u + v) = c * u + v + (c * v + u) := by ring
  rw [h]
  linarith

/-- The Young step of `eq:crossing`: for `d ≥ 1`, `A > 0` and `B ≥ 0` there is `C` such that
`(h + A k)² ≤ m L (B k^{1/d} + Λ)` with all quantities nonnegative forces
`h² ≤ C ((m L)^{2d/(2d-1)} + m L Λ)`. -/
theorem sq_le_of_crossing {d : ℕ} (hd : 1 ≤ d) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ h k m L Λ : ℝ, 0 ≤ h → 0 ≤ k → 0 ≤ m → 0 ≤ L → 0 ≤ Λ →
      (h + A * k) ^ 2 ≤ m * L * (B * k ^ ((1 : ℝ) / d) + Λ) →
        h ^ 2 ≤ C * ((m * L) ^ ((2 * d : ℝ) / (2 * d - 1)) + m * L * Λ) := by
  have hd0lt : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0lt
  have hp1 : (1 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hqpos : 0 < (2 * d : ℝ) / (2 * d - 1) := by
    apply div_pos <;> linarith
  let q : ℝ := (2 * d : ℝ) / (2 * d - 1)
  have hpq : Real.HolderConjugate (2 * d : ℝ) q :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).2 rfl
  let α : ℝ := (d * A ^ 2) ^ ((1 : ℝ) / (2 * d))
  have hαpos : 0 < α := by
    dsimp only [α]
    exact Real.rpow_pos_of_pos (mul_pos hd0lt (pow_pos hA 2)) _
  have hαd : α ^ (2 * d : ℝ) = d * A ^ 2 := by
    dsimp only [α]
    rw [← Real.rpow_mul (mul_nonneg hd0lt.le (sq_nonneg A)) ((1 : ℝ) / (2 * d)) (2 * d)]
    have h1 : ((1 : ℝ) / (2 * d)) * (2 * d) = 1 := by
      field_simp
    rw [h1, Real.rpow_one]
  refine ⟨(B / α) ^ q / q + 1, ?_, ?_⟩
  · have h1 : 0 ≤ (B / α) ^ q := Real.rpow_nonneg (div_nonneg hB hαpos.le) q
    have h2 : 0 ≤ (B / α) ^ q / q := div_nonneg h1 hqpos.le
    linarith
  · intro h k m L Λ hh hk hm hL hΛ hcross
    have hsq : h ^ 2 + A ^ 2 * k ^ 2 ≤ (h + A * k) ^ 2 := by
      nlinarith [mul_nonneg hh (mul_nonneg hA.le hk)]
    have hcross' : h ^ 2 + A ^ 2 * k ^ 2 ≤ m * L * (B * k ^ ((1 : ℝ) / d) + Λ) :=
      le_trans hsq hcross
    have hexpand : m * L * (B * k ^ ((1 : ℝ) / d) + Λ)
        = m * L * B * k ^ ((1 : ℝ) / d) + m * L * Λ := by ring
    have ha : 0 ≤ α * k ^ ((1 : ℝ) / d) := mul_nonneg hαpos.le (Real.rpow_nonneg hk _)
    have hb : 0 ≤ m * L * B / α :=
      div_nonneg (mul_nonneg (mul_nonneg hm hL) hB) hαpos.le
    have hyoung := Real.young_inequality_of_nonneg ha hb hpq
    have hkpow : (k ^ ((1 : ℝ) / d)) ^ (2 * d : ℝ) = k ^ 2 := by
      rw [← Real.rpow_mul hk ((1 : ℝ) / d) (2 * d : ℝ)]
      have h1 : ((1 : ℝ) / d) * (2 * d) = 2 := by
        field_simp
      rw [h1, Real.rpow_two]
    have hαmul : (α * k ^ ((1 : ℝ) / d)) ^ (2 * d : ℝ)
        = α ^ (2 * d : ℝ) * (k ^ ((1 : ℝ) / d)) ^ (2 * d : ℝ) :=
      Real.mul_rpow hαpos.le (Real.rpow_nonneg hk _)
    have hfirst : (α * k ^ ((1 : ℝ) / d)) ^ (2 * d : ℝ) / (2 * d : ℝ)
        = A ^ 2 * k ^ 2 / 2 := by
      rw [hαmul, hkpow, hαd]
      field_simp
    have hlhs : (α * k ^ ((1 : ℝ) / d)) * (m * L * B / α)
        = m * L * B * k ^ ((1 : ℝ) / d) := by
      field_simp
    have hml : m * L * B / α = (m * L) * (B / α) := by ring
    have hmlpow : (m * L * B / α) ^ q = (m * L) ^ q * (B / α) ^ q := by
      rw [hml, Real.mul_rpow (mul_nonneg hm hL) (div_nonneg hB hαpos.le)]
    have hsecond : (m * L * B / α) ^ q / q = ((B / α) ^ q / q) * (m * L) ^ q := by
      rw [hmlpow]
      ring
    have hyoung' : m * L * B * k ^ ((1 : ℝ) / d)
        ≤ A ^ 2 * k ^ 2 / 2 + ((B / α) ^ q / q) * (m * L) ^ q := by
      calc
        m * L * B * k ^ ((1 : ℝ) / d)
            = (α * k ^ ((1 : ℝ) / d)) * (m * L * B / α) := hlhs.symm
        _ ≤ (α * k ^ ((1 : ℝ) / d)) ^ (2 * d : ℝ) / (2 * d : ℝ)
              + (m * L * B / α) ^ q / q := hyoung
        _ = A ^ 2 * k ^ 2 / 2 + ((B / α) ^ q / q) * (m * L) ^ q := by
              rw [hfirst, hsecond]
    have hmain : h ^ 2 ≤ ((B / α) ^ q / q) * (m * L) ^ q + m * L * Λ := by
      have hstep : h ^ 2 + A ^ 2 * k ^ 2
          ≤ A ^ 2 * k ^ 2 / 2 + ((B / α) ^ q / q) * (m * L) ^ q + m * L * Λ := by
        calc
          h ^ 2 + A ^ 2 * k ^ 2 ≤ m * L * (B * k ^ ((1 : ℝ) / d) + Λ) := hcross'
          _ = m * L * B * k ^ ((1 : ℝ) / d) + m * L * Λ := hexpand
          _ ≤ A ^ 2 * k ^ 2 / 2 + ((B / α) ^ q / q) * (m * L) ^ q + m * L * Λ := by
                linarith
      have hA2k2 : 0 ≤ A ^ 2 * k ^ 2 := by positivity
      linarith only [hstep, hA2k2]
    have hc0 : 0 ≤ (B / α) ^ q / q :=
      div_nonneg (Real.rpow_nonneg (div_nonneg hB hαpos.le) q) hqpos.le
    have hmlq : 0 ≤ (m * L) ^ q := Real.rpow_nonneg (mul_nonneg hm hL) q
    have hmlL : 0 ≤ m * L * Λ := mul_nonneg (mul_nonneg hm hL) hΛ
    have h4 : 0 ≤ ((B / α) ^ q / q) * (m * L * Λ) := mul_nonneg hc0 hmlL
    have hfinal : ((B / α) ^ q / q) * (m * L) ^ q + m * L * Λ
        ≤ ((B / α) ^ q / q + 1) * ((m * L) ^ q + m * L * Λ) := by
      exact add_le_mul_add_one_mul hmlq h4
    exact le_trans hmain hfinal

end CERW.Generic.Young
