import CERW.Support.Coarse.SstarArith
import CERW.Support.Main.ScaleLimits

/-!
# The first mass scale and the preconditions

`eq:sstar-lower` and `eq:preconditions`, deterministically. Let `s = R_n^{1/d}`. From
`n ≤ M_n R_n` and `eq:M` in the form `M_n ≤ C_d s + C L²`, we get `n ≤ C_d s^{d+1} + C L² s^d`. This
forces `s ≥ cN` for large `n`. Then `L² = o(s)`, so `M_n ≤ C' s`, and `e_n(M_n) ≤ C'' √s L`.
-/

namespace CERW.Support.Coarse

open Filter

/-- `eq:sstar-lower` and `eq:preconditions`: for `C_d, C ≥ 0` there are `c > 0` and `C' > 0` such
that, for all large `n`, whenever `n ≤ M s^d` and `M ≤ C_d s + C L²` with `M, s ≥ 0`, we have
`cN ≤ s`, `M ≤ C' s` and `√M L + L ≤ C' √s L`. -/
theorem exists_sstar_bounds {d : ℕ} (hd : 1 ≤ d) {Cd C : ℝ} (hCd : 0 ≤ Cd) (hC : 0 ≤ C) :
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∀ᶠ n : ℕ in atTop, ∀ M s : ℝ, 0 ≤ M → 0 ≤ s →
      (n : ℝ) ≤ M * s ^ d → M ≤ Cd * s + C * Real.log (n + 2) ^ 2 →
        c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ s ∧ M ≤ C' * s ∧
          Real.sqrt M * Real.log (n + 2) + Real.log (n + 2) ≤
            C' * Real.sqrt s * Real.log (n + 2) := by
  let K : ℝ := max (max Cd C) 1
  have hKpos : 0 < K := by
    dsimp only [K]
    exact lt_of_lt_of_le zero_lt_one (le_max_right (max Cd C) 1)
  have hCdK : Cd ≤ K := by
    dsimp only [K]
    exact le_trans (le_max_left Cd C) (le_max_left (max Cd C) 1)
  have hCK : C ≤ K := by
    dsimp only [K]
    exact le_trans (le_max_right Cd C) (le_max_left (max Cd C) 1)
  obtain ⟨c, hcpos, hscale⟩ := exists_scale_lower hd hKpos
  let C' : ℝ := Cd + C + Real.sqrt (Cd + C) + 1
  have hC'pos : 0 < C' := by
    dsimp only [C']
    linarith [hCd, hC, Real.sqrt_nonneg (Cd + C)]
  refine ⟨c, C', hcpos, hC'pos, ?_⟩
  have hlim := CERW.Support.Main.tendsto_log_rpow_div_rpow (2 : ℝ)
    (c := (1 : ℝ) / (d + 1)) (by positivity)
  have hL2le : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) ^ 2 ≤ c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    have hle := hlim.eventually_le_const hcpos
    filter_upwards [hle, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
      Real.rpow_pos_of_pos hnpos _
    rw [Real.rpow_two, div_le_iff₀ hNpos] at hn
    exact hn
  have hcN : ∀ᶠ n : ℕ in atTop,
      1 ≤ c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
        atTop atTop :=
      (tendsto_rpow_atTop (show 0 < (1 : ℝ) / (d + 1) by positivity)).comp
        tendsto_natCast_atTop_atTop
    have hge := htend.eventually_ge_atTop c⁻¹
    filter_upwards [hge] with n hn
    have hmul := mul_le_mul_of_nonneg_left hn hcpos.le
    rw [mul_inv_cancel₀ hcpos.ne'] at hmul
    exact hmul
  filter_upwards [hscale, hL2le, hcN] with n hscale_n hL2le_n hcN_n
  intro M s _hM hs hnMsd hMbound
  have hcN_le_s : c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ s := by
    by_contra hnot
    have hsl : s < c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := lt_of_not_ge hnot
    have hcontr := hscale_n s hs hsl
    have hMsd : M * s ^ d ≤ (Cd * s + C * Real.log (n + 2) ^ 2) * s ^ d :=
      mul_le_mul_of_nonneg_right hMbound (pow_nonneg hs d)
    have hn_le1 : (n : ℝ) ≤
        (Cd * s + C * Real.log (n + 2) ^ 2) * s ^ d :=
      le_trans hnMsd hMsd
    have hexpand : (Cd * s + C * Real.log (n + 2) ^ 2) * s ^ d =
        Cd * s ^ (d + 1) + C * Real.log (n + 2) ^ 2 * s ^ d := by
      rw [add_mul, mul_assoc, ← pow_succ']
    have hle : Cd * s ^ (d + 1) + C * Real.log (n + 2) ^ 2 * s ^ d ≤
        K * s ^ (d + 1) + K * Real.log (n + 2) ^ 2 * s ^ d := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hCdK (pow_nonneg hs (d + 1))
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCK (sq_nonneg _)) (pow_nonneg hs d)
    have hn_le_upper : (n : ℝ) ≤
        K * s ^ (d + 1) + K * Real.log (n + 2) ^ 2 * s ^ d :=
      le_trans hn_le1 (le_trans (le_of_eq hexpand) hle)
    linarith
  have hs1 : 1 ≤ s := le_trans hcN_n hcN_le_s
  have hL2_le_s : Real.log (n + 2) ^ 2 ≤ s := le_trans hL2le_n hcN_le_s
  have hM_le : M ≤ (Cd + C) * s := by
    have hCL2 : C * Real.log (n + 2) ^ 2 ≤ C * s :=
      mul_le_mul_of_nonneg_left hL2_le_s hC
    calc
      M ≤ Cd * s + C * Real.log (n + 2) ^ 2 := hMbound
      _ ≤ Cd * s + C * s := by linarith [hCL2]
      _ = (Cd + C) * s := by ring
  have hCdC_le_C' : Cd + C ≤ C' := by
    dsimp only [C']
    linarith [Real.sqrt_nonneg (Cd + C)]
  refine ⟨hcN_le_s, le_trans hM_le (mul_le_mul_of_nonneg_right hCdC_le_C' hs), ?_⟩
  have hLnn : 0 ≤ Real.log (n + 2) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
  have hCdC_nonneg : 0 ≤ Cd + C := add_nonneg hCd hC
  have hsqrtM_le : Real.sqrt M ≤ Real.sqrt (Cd + C) * Real.sqrt s := by
    rw [← Real.sqrt_mul hCdC_nonneg s]
    exact Real.sqrt_le_sqrt hM_le
  have hsqrts_ge_one : 1 ≤ Real.sqrt s := Real.one_le_sqrt.mpr hs1
  have hstep3 : (Real.sqrt (Cd + C) * Real.sqrt s + 1) * Real.log (n + 2) ≤
      (Real.sqrt (Cd + C) + 1) * Real.sqrt s * Real.log (n + 2) := by
    have hfac : Real.sqrt (Cd + C) * Real.sqrt s + 1 ≤
        (Real.sqrt (Cd + C) + 1) * Real.sqrt s := by
      rw [add_mul, one_mul]
      linarith [hsqrts_ge_one]
    exact mul_le_mul_of_nonneg_right hfac hLnn
  have hsqrt_le_C' : Real.sqrt (Cd + C) + 1 ≤ C' := by
    dsimp only [C']
    linarith [Real.sqrt_nonneg (Cd + C)]
  have hstep4 : (Real.sqrt (Cd + C) + 1) * Real.sqrt s * Real.log (n + 2) ≤
      C' * Real.sqrt s * Real.log (n + 2) := by
    apply mul_le_mul_of_nonneg_right _ hLnn
    exact mul_le_mul_of_nonneg_right hsqrt_le_C' (Real.sqrt_nonneg s)
  calc
    Real.sqrt M * Real.log (n + 2) + Real.log (n + 2)
        = (Real.sqrt M + 1) * Real.log (n + 2) := by ring
    _ ≤ (Real.sqrt (Cd + C) * Real.sqrt s + 1) * Real.log (n + 2) := by
          apply mul_le_mul_of_nonneg_right _ hLnn
          linarith [hsqrtM_le]
    _ ≤ (Real.sqrt (Cd + C) + 1) * Real.sqrt s * Real.log (n + 2) := hstep3
    _ ≤ C' * Real.sqrt s * Real.log (n + 2) := hstep4

end CERW.Support.Coarse
