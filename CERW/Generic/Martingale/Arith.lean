import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Arithmetic of Freedman's bound at a logarithmic threshold

At the threshold `t = c (√(vL) + BL)`, Freedman's exponent `t² / (2(v + Bt))` is at least
`cL/2`, so a constant `c ≥ 2K` makes the tail at most `2 e^{-KL}`. With `L = log(n+2)` that is
at most `2 n^{-K}`. A union over at most `(n+1)^m` events costs a factor `2^m n^m`. These are the
dyadic-level and union-bound steps behind `eq:interval-mart`, `eq:localmart`, `eq:radialmart`,
`eq:vector` and `eq:quadraticerror`.
-/

namespace CERW.Generic.Martingale

/-- For `K ≥ 0` there is `c ≥ 1` such that, for `v ≥ 0` and `B, L > 0`, the threshold
`t = c (√(vL) + BL)` makes Freedman's exponent `t² / (2(v + Bt))` at least `K L`. -/
theorem le_freedman_exponent {K : ℝ} (hK : 0 ≤ K) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ v B L : ℝ, 0 ≤ v → 0 < B → 0 < L →
      K * L ≤ (c * (Real.sqrt (v * L) + B * L)) ^ 2 /
        (2 * (v + B * (c * (Real.sqrt (v * L) + B * L)))) := by
  refine ⟨max 1 (2 * K), le_max_left 1 (2 * K), ?_⟩
  intro v B L hv hB hL
  set c : ℝ := max 1 (2 * K) with hc
  have hc1 : 1 ≤ c := le_max_left 1 (2 * K)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hcK : 2 * K ≤ c := le_max_right 1 (2 * K)
  set a : ℝ := Real.sqrt (v * L) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = v * L := Real.sq_sqrt (mul_nonneg hv hL.le)
  set b : ℝ := B * L with hb
  have hb0 : 0 ≤ b := mul_nonneg hB.le hL.le
  have hbpos : 0 < b := mul_pos hB hL
  have hkey : a ^ 2 + c * b * (a + b) ≤ c * (a + b) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg a),
      mul_nonneg (mul_nonneg hc0.le ha0) hb0]
  have hK0 : 0 ≤ K := hK
  have hKL : K * L ≤ c * L / 2 := by nlinarith [hcK, hL, hK0]
  have hden : 0 < 2 * (v + B * (c * (a + b))) := by
    have hab : 0 < a + b := by linarith
    have h1 : 0 < B * (c * (a + b)) := mul_pos hB (mul_pos hc0 hab)
    linarith
  have hmid : c * L / 2 ≤ (c * (a + b)) ^ 2 / (2 * (v + B * (c * (a + b)))) := by
    rw [le_div_iff₀ hden]
    nlinarith [hkey, hc0, ha2, hb]
  exact le_trans hKL hmid

/-- For `n ≥ 1` and `K ≥ 0`, `2 e^{-K log(n+2)} ≤ 2 n^{-K}`. -/
theorem two_mul_exp_neg_mul_log_le {K : ℝ} (hK : 0 ≤ K) {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.exp (-(K * Real.log (n + 2))) ≤ 2 * (n : ℝ) ^ (-K) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hle : ((n : ℝ) + 2) ^ (-K) ≤ (n : ℝ) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos hnpos (by linarith) (by linarith)
  have hkey : Real.exp (-(K * Real.log ((n : ℝ) + 2))) = ((n : ℝ) + 2) ^ (-K) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + 2)]
    congr 1
    ring
  rw [hkey]
  linarith

/-- A union over at most `(n+1)^m` events of probability at most `n^{-(p+m)}` costs at most
`2^m n^{-p}`: `(n+1)^m n^{-(p+m)} ≤ 2^m n^{-p}` for `n ≥ 1`. -/
theorem pow_mul_rpow_neg_le {n : ℕ} (hn : 1 ≤ n) (m : ℕ) (p : ℝ) :
    ((n : ℝ) + 1) ^ m * (n : ℝ) ^ (-(p + m)) ≤ 2 ^ m * (n : ℝ) ^ (-p) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnn : 0 ≤ (n : ℝ) + 1 := by linarith
  have hle : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have hpow : ((n : ℝ) + 1) ^ m ≤ 2 ^ m * (n : ℝ) ^ m := by
    calc ((n : ℝ) + 1) ^ m ≤ (2 * (n : ℝ)) ^ m := pow_le_pow_left₀ hnn hle m
      _ = 2 ^ m * (n : ℝ) ^ m := by rw [mul_pow]
  have hrpow : (n : ℝ) ^ m * (n : ℝ) ^ (-(p + m)) = (n : ℝ) ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
    congr 1
    ring
  calc ((n : ℝ) + 1) ^ m * (n : ℝ) ^ (-(p + m))
      ≤ (2 ^ m * (n : ℝ) ^ m) * (n : ℝ) ^ (-(p + m)) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hnpos.le _)
    _ = 2 ^ m * ((n : ℝ) ^ m * (n : ℝ) ^ (-(p + m))) := by ring
    _ = 2 ^ m * (n : ℝ) ^ (-p) := by rw [hrpow]

end CERW.Generic.Martingale
