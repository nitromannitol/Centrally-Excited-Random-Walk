import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The paper's scales tend to zero

With `N = n^{1/(d+1)}` and `L = log(n + 2)`, every power of `L` is negligible against every
positive power of `n`. Hence the rate `Q = (L/N)^{1/2}` (`d = 2`) or `(L/N)^{d/(2d-1)}`
(`d ≥ 3`) tends to zero, and so does `Q^{1/d} L`. These limits turn the quantitative bounds of
`thm:fluctuations` into the limits of `thm:shape`.
-/

namespace CERW.Support.Main

open Filter Topology

/-- For `n ≥ 1`, the `a`-th power of the rate `L / n^{1/(d+1)}` is `L^a / n^{a/(d+1)}`. -/
lemma rpow_div_rpow_eq (a : ℝ) (d n : ℕ) (hn : 1 ≤ n) :
    (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ a =
      Real.log (n + 2) ^ a / (n : ℝ) ^ (a * ((1 : ℝ) / (d + 1))) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : 0 ≤ Real.log (n + 2) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
  have hN : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hn0 _
  rw [Real.div_rpow hlog hN, ← Real.rpow_mul hn0 ((1 : ℝ) / (d + 1)) a,
    mul_comm ((1 : ℝ) / (d + 1)) a]

/-- For `n ≥ 1`, a power of the rate `L / n^{1/(d+1)}` scaled by `L` is a power of `L`
over a power of `n`. -/
lemma rpow_div_rpow_mul_log_eq (a : ℝ) (d n : ℕ) (hn : 1 ≤ n) :
    ((Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ a) ^ ((1 : ℝ) / d)
        * Real.log (n + 2) =
      Real.log (n + 2) ^ (1 + a * ((1 : ℝ) / d))
        / (n : ℝ) ^ (a * ((1 : ℝ) / d) * ((1 : ℝ) / (d + 1))) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hlog : 0 ≤ Real.log (n + 2) := Real.log_nonneg hlog1
  have hlogpos : 0 < Real.log (n + 2) := Real.log_pos (by linarith)
  have hN : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hn0 _
  have hX : 0 ≤ Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
    div_nonneg hlog hN
  calc
    ((Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ a) ^ ((1 : ℝ) / d)
        * Real.log (n + 2)
        = (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
            ^ (a * ((1 : ℝ) / d)) * Real.log (n + 2) := by
          rw [← Real.rpow_mul hX a ((1 : ℝ) / d)]
      _ = (Real.log (n + 2) ^ (a * ((1 : ℝ) / d))
            / ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ (a * ((1 : ℝ) / d)))
            * Real.log (n + 2) := by
          rw [Real.div_rpow hlog hN]
      _ = (Real.log (n + 2) ^ (a * ((1 : ℝ) / d))
            / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * (a * ((1 : ℝ) / d))))
            * Real.log (n + 2) := by
          rw [← Real.rpow_mul hn0 ((1 : ℝ) / (d + 1)) (a * ((1 : ℝ) / d))]
      _ = (Real.log (n + 2) ^ (a * ((1 : ℝ) / d))
            * Real.log (n + 2))
            / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * (a * ((1 : ℝ) / d))) := by
          ring
      _ = Real.log (n + 2) ^ (a * ((1 : ℝ) / d) + 1)
            / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * (a * ((1 : ℝ) / d))) := by
          rw [← Real.rpow_add_one hlogpos.ne' (a * ((1 : ℝ) / d))]
      _ = Real.log (n + 2) ^ (1 + a * ((1 : ℝ) / d))
            / (n : ℝ) ^ (a * ((1 : ℝ) / d) * ((1 : ℝ) / (d + 1))) := by
          rw [show a * ((1 : ℝ) / d) + 1 = 1 + a * ((1 : ℝ) / d) by ring,
            show ((1 : ℝ) / (d + 1)) * (a * ((1 : ℝ) / d)) =
              a * ((1 : ℝ) / d) * ((1 : ℝ) / (d + 1)) by ring]

/-- Every real power of `log(n + 2)` is negligible against every positive power of `n`. -/
theorem tendsto_log_rpow_div_rpow (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (n + 2) ^ a / (n : ℝ) ^ c) atTop (𝓝 0) := by
  have htend : Tendsto (fun x : ℝ => Real.log x ^ a / x ^ c) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop a hc).tendsto_div_nhds_zero
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hcomp : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2) ^ a / ((n : ℝ) + 2) ^ c)
      atTop (𝓝 0) := htend.comp hshift
  have hg : Tendsto (fun n : ℕ =>
      Real.log ((n : ℝ) + 2) ^ a / ((n : ℝ) + 2) ^ c * 3 ^ c) atTop (𝓝 0) := by
    simpa using hcomp.mul_const (3 ^ c)
  refine squeeze_zero' (t₀ := atTop) ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith [show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn])
    exact div_nonneg (Real.rpow_nonneg hlog a) (Real.rpow_nonneg hn0 c)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    have hnum : 0 ≤ Real.log ((n : ℝ) + 2) ^ a := Real.rpow_nonneg hlog a
    have hAp : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos (by linarith) c
    have hBp : 0 < ((n : ℝ) + 2) ^ c := Real.rpow_pos_of_pos (by linarith) c
    have hBA : ((n : ℝ) + 2) ^ c ≤ 3 ^ c * (n : ℝ) ^ c := by
      calc ((n : ℝ) + 2) ^ c ≤ (3 * (n : ℝ)) ^ c :=
            Real.rpow_le_rpow (by linarith) (by linarith) (le_of_lt hc)
        _ = 3 ^ c * (n : ℝ) ^ c := Real.mul_rpow (by norm_num) hn0
    have hmain : Real.log ((n : ℝ) + 2) ^ a / (n : ℝ) ^ c ≤
        Real.log ((n : ℝ) + 2) ^ a * 3 ^ c / ((n : ℝ) + 2) ^ c := by
      rw [div_le_div_iff₀ hAp hBp]
      calc Real.log ((n : ℝ) + 2) ^ a * ((n : ℝ) + 2) ^ c
          ≤ Real.log ((n : ℝ) + 2) ^ a * (3 ^ c * (n : ℝ) ^ c) :=
            mul_le_mul_of_nonneg_left hBA hnum
        _ = Real.log ((n : ℝ) + 2) ^ a * 3 ^ c * (n : ℝ) ^ c := by ring
    calc Real.log ((n : ℝ) + 2) ^ a / (n : ℝ) ^ c
        ≤ Real.log ((n : ℝ) + 2) ^ a * 3 ^ c / ((n : ℝ) + 2) ^ c := hmain
      _ = Real.log ((n : ℝ) + 2) ^ a / ((n : ℝ) + 2) ^ c * 3 ^ c := by ring

/-- The rate `Q` of `eq:rates` tends to zero. -/
theorem tendsto_rate_zero {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => if d = 2
      then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
      else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
      atTop (𝓝 0) := by
  by_cases h2 : d = 2
  · subst d
    simp only [reduceIte]
    refine Tendsto.congr' ?_ (tendsto_log_rpow_div_rpow ((1 : ℝ) / 2) (c := 1 / 6) (by norm_num))
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [rpow_div_rpow_eq ((1 : ℝ) / 2) 2 n hn]
    norm_num
  · simp only [if_neg h2]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h2d1pos : (0 : ℝ) < 2 * (d : ℝ) - 1 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
      linarith
    have hc : 0 < (d : ℝ) / (2 * d - 1) * ((1 : ℝ) / (d + 1)) := by
      apply mul_pos
      · exact div_pos hdpos h2d1pos
      · exact div_pos zero_lt_one (by positivity)
    refine Tendsto.congr' ?_
      (tendsto_log_rpow_div_rpow ((d : ℝ) / (2 * d - 1)) hc)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [rpow_div_rpow_eq ((d : ℝ) / (2 * d - 1)) d n hn]

/-- The outer excess `Q^{1/d} L` of `eq:sandwich` tends to zero. -/
theorem tendsto_rate_rpow_mul_log_zero {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => (if d = 2
      then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
      else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        ^ ((1 : ℝ) / d) * Real.log (n + 2)) atTop (𝓝 0) := by
  by_cases h2 : d = 2
  · subst d
    simp only [reduceIte]
    have hc : 0 < (1 / 2 : ℝ) * ((1 : ℝ) / 2) * ((1 : ℝ) / ((2 : ℕ) + 1)) := by
      norm_num
    refine Tendsto.congr' ?_
      (tendsto_log_rpow_div_rpow (1 + (1 / 2 : ℝ) * ((1 : ℝ) / 2)) hc)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [rpow_div_rpow_mul_log_eq ((1 : ℝ) / 2) 2 n hn]
    rfl
  · simp only [if_neg h2]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h2d1pos : (0 : ℝ) < 2 * (d : ℝ) - 1 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
      linarith
    have hc : 0 < (d : ℝ) / (2 * d - 1) * ((1 : ℝ) / d) * ((1 : ℝ) / (d + 1)) := by
      apply mul_pos
      · apply mul_pos
        · exact div_pos hdpos h2d1pos
        · exact div_pos zero_lt_one (by positivity)
      · exact div_pos zero_lt_one (by positivity)
    refine Tendsto.congr' ?_
      (tendsto_log_rpow_div_rpow (1 + (d : ℝ) / (2 * d - 1) * ((1 : ℝ) / d)) hc)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [rpow_div_rpow_mul_log_eq ((d : ℝ) / (2 * d - 1)) d n hn]

end CERW.Support.Main
