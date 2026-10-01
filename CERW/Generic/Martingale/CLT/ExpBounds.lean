import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic

/-!
# Elementary exponential bounds for the martingale central limit theorem

The third-order Taylor bound for `exp (i y)` valid for every real `y`, and the bound
`|e^a (1 - a) - 1| ≤ a² e^a / 2` for `a ≥ 0`. Both are used to control one step of the
exponential compensator.
-/

namespace CERW.Generic.Martingale.CLT

open Complex

/-- For `|y| ≤ 1`, the Taylor remainder of `exp (i y)` at order two is at most `4 |y|³`. -/
private lemma norm_cexp_I_sub_taylor_le_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp (y * I) - (1 + y * I - (y : ℂ) ^ 2 / 2)‖ ≤ 4 * min (|y| ^ 3) (y ^ 2) := by
  have hx : ‖(y : ℂ) * I‖ ≤ 1 := by simpa using hy
  have hb := Complex.exp_bound hx (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, ((y : ℂ) * I) ^ m / (m.factorial : ℂ)
      = 1 + y * I - (y : ℂ) ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, mul_pow, I_sq]
    push_cast
    ring
  rw [hsum] at hb
  have hnorm : ‖(y : ℂ) * I‖ = |y| := by simp
  rw [hnorm] at hb
  have hmin : min (|y| ^ 3) (y ^ 2) = |y| ^ 3 := by
    refine min_eq_left ?_
    rw [← sq_abs y]
    have h0 : 0 ≤ |y| := abs_nonneg y
    have h2 : 0 ≤ |y| ^ 2 := sq_nonneg _
    calc |y| ^ 3 = |y| ^ 2 * |y| := by ring
      _ ≤ |y| ^ 2 * 1 := mul_le_mul_of_nonneg_left hy h2
      _ = |y| ^ 2 := mul_one _
  rw [hmin]
  refine hb.trans ?_
  have h3 : 0 ≤ |y| ^ 3 := pow_nonneg (abs_nonneg y) 3
  norm_num [Nat.factorial]
  linarith

/-- For `1 < |y|`, the Taylor remainder of `exp (i y)` at order two is at most `4 y²`. -/
private lemma norm_cexp_I_sub_taylor_le_of_one_lt_abs {y : ℝ} (hy : 1 < |y|) :
    ‖cexp (y * I) - (1 + y * I - (y : ℂ) ^ 2 / 2)‖ ≤ 4 * min (|y| ^ 3) (y ^ 2) := by
  have hmin : min (|y| ^ 3) (y ^ 2) = y ^ 2 := by
    refine min_eq_right ?_
    rw [← sq_abs y]
    have h2 : 0 ≤ |y| ^ 2 := sq_nonneg _
    calc |y| ^ 2 = |y| ^ 2 * 1 := (mul_one _).symm
      _ ≤ |y| ^ 2 * |y| := mul_le_mul_of_nonneg_left hy.le h2
      _ = |y| ^ 3 := by ring
  rw [hmin]
  have h1 : ‖cexp (y * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I y
  have h2 : ‖(1 : ℂ) + y * I - (y : ℂ) ^ 2 / 2‖ ≤ 1 + |y| + y ^ 2 / 2 := by
    calc ‖(1 : ℂ) + y * I - (y : ℂ) ^ 2 / 2‖
        ≤ ‖(1 : ℂ) + y * I‖ + ‖(y : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖(y : ℂ) * I‖) + ‖(y : ℂ) ^ 2 / 2‖ := by
          gcongr
          exact norm_add_le _ _
      _ = 1 + |y| + y ^ 2 / 2 := by
          rw [norm_div, norm_mul, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
            norm_one, mul_one, sq_abs]
          norm_num
  have h3 : ‖cexp (y * I) - (1 + y * I - (y : ℂ) ^ 2 / 2)‖
      ≤ 1 + (1 + |y| + y ^ 2 / 2) := by
    calc ‖cexp (y * I) - (1 + y * I - (y : ℂ) ^ 2 / 2)‖
        ≤ ‖cexp (y * I)‖ + ‖(1 : ℂ) + y * I - (y : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + |y| + y ^ 2 / 2) := by rw [h1]; gcongr
  have hsq : |y| ≤ y ^ 2 := by
    rw [← sq_abs y]
    calc |y| = |y| * 1 := (mul_one _).symm
      _ ≤ |y| * |y| := mul_le_mul_of_nonneg_left hy.le (abs_nonneg y)
      _ = |y| ^ 2 := (sq _).symm
  have hone : 1 ≤ y ^ 2 := le_trans hy.le hsq
  linarith

/-- The third-order Taylor remainder of `exp (i y)` is at most `4 min (|y|³, y²)` for all real
`y`. -/
theorem norm_cexp_I_sub_taylor_le :
    ∀ y : ℝ, ‖cexp (y * I) - (1 + y * I - (y : ℂ) ^ 2 / 2)‖ ≤ 4 * min (|y| ^ 3) (y ^ 2) := by
  intro y
  rcases le_or_gt |y| 1 with hy | hy
  · exact norm_cexp_I_sub_taylor_le_of_abs_le_one hy
  · exact norm_cexp_I_sub_taylor_le_of_one_lt_abs hy

/-- For `a ≥ 0`, `|e^a (1 - a) - 1| ≤ (a² / 2) e^a`. -/
theorem abs_exp_mul_one_sub_sub_one_le :
    ∀ a : ℝ, 0 ≤ a → |Real.exp a * (1 - a) - 1| ≤ a ^ 2 / 2 * Real.exp a := by
  intro a ha
  have hup : Real.exp a * (1 - a) - 1 ≤ 0 := by
    have h := Real.one_sub_le_exp_neg a
    have hpos := Real.exp_pos a
    have hexp : Real.exp a * Real.exp (-a) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp a * (1 - a) - 1 ≤ Real.exp a * Real.exp (-a) - 1 := by gcongr
      _ = 0 := by rw [hexp]; ring
  have hq : 0 < 1 - a + a ^ 2 / 2 := by nlinarith [sq_nonneg (a - 1)]
  have hlow : 1 ≤ Real.exp a * (1 - a + a ^ 2 / 2) := by
    have hcube : 1 + a + a ^ 2 / 2 + a ^ 3 / 6 ≤ Real.exp a := by
      have h := Real.sum_le_exp_of_nonneg ha 4
      simpa [Finset.sum_range_succ, Nat.factorial] using h
    have hP : 1 ≤ (1 + a + a ^ 2 / 2 + a ^ 3 / 6) * (1 - a + a ^ 2 / 2) := by
      have e : (1 + a + a ^ 2 / 2 + a ^ 3 / 6) * (1 - a + a ^ 2 / 2)
          = 1 + a ^ 3 / 6 + a ^ 4 / 12 + a ^ 5 / 12 := by ring
      rw [e]
      have h3 : 0 ≤ a ^ 3 := pow_nonneg ha 3
      have h4 : 0 ≤ a ^ 4 := pow_nonneg ha 4
      have h5 : 0 ≤ a ^ 5 := pow_nonneg ha 5
      linarith
    exact hP.trans (mul_le_mul_of_nonneg_right hcube hq.le)
  rw [abs_of_nonpos hup]
  linarith

/-- The real exponential is `e^A`-Lipschitz below `A`. -/
theorem abs_exp_sub_exp_le {x y A : ℝ} (hx : x ≤ A) (hy : y ≤ A) :
    |Real.exp y - Real.exp x| ≤ Real.exp A * |y - x| := by
  have h1 : Real.exp y - Real.exp x ≤ (y - x) * Real.exp y := by
    have h := Real.add_one_le_exp (x - y)
    have hpos := Real.exp_pos y
    have e : Real.exp x = Real.exp (x - y) * Real.exp y := by rw [← Real.exp_add]; ring_nf
    nlinarith
  have h2 : Real.exp x - Real.exp y ≤ (x - y) * Real.exp x := by
    have h := Real.add_one_le_exp (y - x)
    have hpos := Real.exp_pos x
    have e : Real.exp y = Real.exp (y - x) * Real.exp x := by rw [← Real.exp_add]; ring_nf
    nlinarith
  have hxA := Real.exp_le_exp.mpr hx
  have hyA := Real.exp_le_exp.mpr hy
  rw [abs_le]
  constructor
  · rcases le_total y x with h | h
    · rw [abs_of_nonpos (by linarith : y - x ≤ 0)]
      nlinarith [Real.exp_pos A, Real.exp_pos x, Real.exp_pos y]
    · rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
      nlinarith [Real.exp_pos A, Real.exp_pos x, Real.exp_pos y, Real.exp_le_exp.mpr h]
  · rcases le_total y x with h | h
    · rw [abs_of_nonpos (by linarith : y - x ≤ 0)]
      nlinarith [Real.exp_pos A, Real.exp_pos x, Real.exp_pos y]
    · rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
      nlinarith [Real.exp_pos A, Real.exp_pos x, Real.exp_pos y]


end CERW.Generic.Martingale.CLT
