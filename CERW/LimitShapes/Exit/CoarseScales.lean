module

public import CERW.LimitShapes.Exit.CoarseAux

@[expose] public section

/-!
# Scale changes for the coarse exit argument

The radius in Proposition `prop:coarse` converts polynomial exit tails to polynomial
tails in time. All constants here are chosen before the path.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.CoarseVolume

/-- A fixed multiple of the coarse scale forces the lower exit-time bound past `n`. -/
theorem time_lt_exit_scale {d : ℕ} {κ c r : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hr : 0 < r) :
    κ * r ^ (d + 1) < c * ((κ / c + 1) * r) ^ (d + 1) := by
  have hA : 1 ≤ κ / c + 1 := by linarith [div_pos hκ hc]
  have hp : κ / c + 1 ≤ (κ / c + 1) ^ (d + 1) :=
    calc
      _ = (κ / c + 1) * 1 := (mul_one _).symm
      _ ≤ (κ / c + 1) * (κ / c + 1) ^ d :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hA) (by linarith)
      _ = _ := by rw [pow_succ]; ring
  have hb : κ < c * (κ / c + 1) := by
    rw [mul_add, mul_div_cancel₀ _ hc.ne']
    linarith
  rw [mul_pow, ← mul_assoc]
  exact mul_lt_mul_of_pos_right
    (hb.trans_le (mul_le_mul_of_nonneg_left hp hc.le)) (pow_pos hr _)

/-- The exit-tail scale is exactly a fixed multiple of the time-tail scale. -/
theorem exit_tail_scale {d : ℕ} {κ A r : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hr : 0 < r) (p : ℝ) :
    (A * r) ^ (-((d + 1 : ℝ) * p)) =
      (A ^ (-((d + 1 : ℝ) * p)) * κ ^ p) *
        (κ * r ^ (d + 1)) ^ (-p) := by
  rw [Real.mul_rpow hA.le hr.le, Real.mul_rpow hκ.le (pow_nonneg hr.le _)]
  have he : r ^ (-((d + 1 : ℝ) * p)) = (r ^ (d + 1)) ^ (-p) := by
    rw [show -((d + 1 : ℝ) * p) = ((d + 1 : ℕ) : ℝ) * (-p) by push_cast; ring]
    exact Real.rpow_natCast_mul hr.le _ _
  rw [he]
  have hk : κ ^ p * κ ^ (-p) = 1 := by
    rw [← Real.rpow_add hκ, add_neg_cancel, Real.rpow_zero]
  calc
    _ = A ^ (-((d + 1 : ℝ) * p)) * (κ ^ p * κ ^ (-p)) *
        (r ^ (d + 1)) ^ (-p) := by rw [hk, mul_one]
    _ = _ := by ring

/-- Any fixed positive lower threshold for the coarse scale holds eventually. -/
theorem eventually_le_coarseScale {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hV : 0 < normBallVolume Ψ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ n : ℕ in Filter.atTop, K ≤ coarseScale Ψ ε n := by
  simpa only [pow_zero, mul_one] using
    eventually_mul_log_pow_le_coarseScale hd hε hV hK 0

end CERW.LimitShapes.Exit
