import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The increment bound inside a block

Inside block `k`, between the passage times over the levels `x ≥ e^e` and `x'`, the value of the
bracket at the next time lies in `[x, x')`. The bound on the increment of the padded martingale,
`max 1 (εg √(V/ log log (V ∨ e^e)))`, is then at most `max 1 (ε √(x' / log log x))` for
`εg ≤ ε`, since `V ≥ x ≥ e^e` makes `log log (V ∨ e^e) ≥ log log x > 0` and `V < x'`.
-/

namespace CERW.Generic.Martingale.LilLower

/-- The increment bound at a bracket value `v ∈ [x, x')` with `x ≥ e^e` is at most
`max 1 (ε √(x' / log log x))` once `0 ≤ εg ≤ ε`. -/
theorem sqrt_scale_le {x x' v εg ε : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) (hxv : x ≤ v)
    (hvx' : v < x') (hεg : 0 ≤ εg) (hεgε : εg ≤ ε) :
    max 1 (εg * Real.sqrt (v / Real.log (Real.log (max v (Real.exp (Real.exp 1)))))) ≤
      max 1 (ε * Real.sqrt (x' / Real.log (Real.log x))) := by
  have hepos : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  have hxpos : 0 < x := hepos.trans_le hx
  have hvpos : 0 < v := hxpos.trans_le hxv
  have hone : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  have hlogx : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hx
  have hlogxpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlogx
  have hL : 0 < Real.log (Real.log x) :=
    Real.log_pos (hone.trans_le hlogx)
  have hmax : max v (Real.exp (Real.exp 1)) = v := max_eq_left (hx.trans hxv)
  have hlogv : Real.log x ≤ Real.log v := Real.log_le_log hxpos hxv
  have hloglogv : Real.log (Real.log x) ≤ Real.log (Real.log v) := Real.log_le_log hlogxpos hlogv
  have hdiv : v / Real.log (Real.log (max v (Real.exp (Real.exp 1)))) ≤
      x' / Real.log (Real.log x) := by
    rw [hmax]
    exact div_le_div₀ (hvpos.trans hvx').le hvx'.le hL hloglogv
  have hε : 0 ≤ ε := hεg.trans hεgε
  exact max_le_max le_rfl
    (mul_le_mul hεgε (Real.sqrt_le_sqrt hdiv) (Real.sqrt_nonneg _) hε)

end CERW.Generic.Martingale.LilLower
