import CERW.Generic.Martingale.Lil.Statements

/-!
# The arithmetic of the blocks

Parameters `θ, ε, η` of the geometric blocks exist for every `δ > 0`, and the functions
`x / log log (x ∨ e^e)` and `y log log y` are monotone.
-/

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- `log` increases by at most the relative increment. -/
theorem lilArith_log_sub_log_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log y - Real.log x ≤ (y - x) / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have : y / x - 1 = (y - x) / x := by field_simp
  linarith

/-- For `e ≤ log x`, the logarithm of `log` increases by at most `y - x` over `x`. -/
theorem lilArith_loglog_sub_le {x y : ℝ} (hx : Real.exp 1 ≤ Real.log x) (hxy : x ≤ y)
    (hx0 : 0 < x) :
    Real.log (Real.log y) - Real.log (Real.log x) ≤ (y - x) / x := by
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have ha : 0 < Real.log x := by linarith
  have hy : 0 < y := lt_of_lt_of_le hx0 hxy
  have hab : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have h1 := lilArith_log_sub_log_le ha hab
  have h2 := lilArith_log_sub_log_le hx0 hxy
  have h3 : (Real.log y - Real.log x) / Real.log x ≤ Real.log y - Real.log x :=
    div_le_self (by linarith) (by linarith)
  linarith

/-- The key inequality `x * L y ≤ y * L x` for `L = log ∘ log` beyond `exp (exp 1)`. -/
theorem lilArith_mul_loglog_le {x y : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) (hxy : x ≤ y) :
    x * Real.log (Real.log y) ≤ y * Real.log (Real.log x) := by
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : Real.exp 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hL : 1 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hlx
  have h := lilArith_loglog_sub_le hlx hxy hx0
  have h2 : x * (Real.log (Real.log y) - Real.log (Real.log x)) ≤ y - x := by
    calc x * (Real.log (Real.log y) - Real.log (Real.log x)) ≤ x * ((y - x) / x) :=
          mul_le_mul_of_nonneg_left h hx0.le
      _ = y - x := by field_simp
  have h3 : x * (Real.log (Real.log x) - 1) ≤ y * (Real.log (Real.log x) - 1) :=
    mul_le_mul_of_nonneg_right hxy (by linarith)
  linarith

theorem lilArith_loglog_exp_exp : Real.log (Real.log (Real.exp (Real.exp 1))) = 1 := by
  rw [Real.log_exp, Real.log_exp]

theorem lilArith_loglog_ge_one {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    1 ≤ Real.log (Real.log x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : Real.exp 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hlx)]
  exact hlx

/-- The function `x / log log (x ∨ e^e)` is monotone on `[0, ∞)`. -/
theorem lilArith_monotoneOn_div_loglog :
    MonotoneOn (fun x : ℝ => x / Real.log (Real.log (max x (Real.exp (Real.exp 1)))))
      (Set.Ici 0) := by
  intro x _ y _ hxy
  simp only
  have hc : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  by_cases hy : y ≤ Real.exp (Real.exp 1)
  · rw [max_eq_right hy, max_eq_right (hxy.trans hy), lilArith_loglog_exp_exp]
    simpa using hxy
  · replace hy := not_le.mp hy
    rw [max_eq_left hy.le]
    have hL := lilArith_loglog_ge_one hy.le
    by_cases hx : x ≤ Real.exp (Real.exp 1)
    · rw [max_eq_right hx, lilArith_loglog_exp_exp, div_one]
      have h1 := lilArith_mul_loglog_le (le_refl (Real.exp (Real.exp 1))) hy.le
      rw [lilArith_loglog_exp_exp] at h1
      rw [le_div_iff₀ (by linarith)]
      calc x * Real.log (Real.log y) ≤ Real.exp (Real.exp 1) * Real.log (Real.log y) :=
            mul_le_mul_of_nonneg_right hx (by linarith)
        _ ≤ y := by linarith
    · replace hx := not_le.mp hx
      rw [max_eq_left hx.le]
      have hLx := lilArith_loglog_ge_one hx.le
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      exact lilArith_mul_loglog_le hx.le hxy

/-- The function `y * log log y` is monotone on `[e, ∞)`. -/
theorem lilArith_monotoneOn_mul_loglog :
    MonotoneOn (fun y : ℝ => y * Real.log (Real.log y)) (Set.Ici (Real.exp 1)) := by
  intro x hx y _ hxy
  simp only
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hx' : Real.exp 1 ≤ x := hx
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hx'
  have hlxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hLx : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlx
  have hLxy : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
    Real.log_le_log (by linarith) hlxy
  exact mul_le_mul hxy hLxy hLx (by linarith)

/-- Parameters of the blocks exist for every `δ > 0`. -/
theorem lilArith_lilParams_exists (δ : ℝ) (hδ : 0 < δ) :
    ∃ θ ε η : ℝ, LilParams θ ε δ η := by
  have h1 : (0 : ℝ) < 1 + δ := by linarith
  have hε : 0 < δ / (1 + δ) ^ 3 := by positivity
  have hεd : δ / (1 + δ) ^ 3 * (1 + δ) ^ 3 = δ := by field_simp
  refine ⟨1 + δ / 2, δ / (1 + δ) ^ 3, δ / 2, by linarith, hε, hδ, by linarith, ?_⟩
  set ε := δ / (1 + δ) ^ 3 with hεdef
  have hs : Real.sqrt (2 * (1 + δ / 2)) ≤ 2 * (1 + δ) := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have h2 : ε * (1 + δ) * Real.sqrt (2 * (1 + δ / 2)) ≤ ε * (1 + δ) * (2 * (1 + δ)) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h3 : ε * (1 + δ) * (2 * (1 + δ)) ≤ 2 * δ := by
    have : ε * (1 + δ) ^ 2 ≤ ε * (1 + δ) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by norm_num)) hε.le
    nlinarith
  have h4 : ε * (1 + δ) * Real.sqrt (2 * (1 + δ / 2)) / 3 ≤ 2 * δ / 3 := by linarith
  have h5 : 1 + δ / 2 + ε * (1 + δ) * Real.sqrt (2 * (1 + δ / 2)) / 3
      ≤ 1 + δ / 2 + 2 * δ / 3 := by linarith
  calc (1 + δ / 2) * (1 + δ / 2 + ε * (1 + δ) * Real.sqrt (2 * (1 + δ / 2)) / 3)
      ≤ (1 + δ / 2) * (1 + δ / 2 + 2 * δ / 3) := mul_le_mul_of_nonneg_left h5 (by linarith)
    _ ≤ (1 + δ) ^ 2 := by nlinarith

/-- The arithmetic of the blocks. -/
theorem lil_arith : LilArith := by
  exact ⟨lilArith_lilParams_exists, lilArith_monotoneOn_div_loglog,
      lilArith_monotoneOn_mul_loglog⟩

end CERW.Generic.Martingale.Lil
