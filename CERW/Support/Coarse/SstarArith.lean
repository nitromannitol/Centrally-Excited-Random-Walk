import CERW.Support.Main.ScaleLimits

/-!
# The first mass scale is at least of order `N`

`eq:sstar-lower`: from `n ≤ C s^{d+1} + C λ_n s^d` with `λ_n ≤ L²`, it follows `s ≥ cN`
for large `n`. If `s < cN` with `c^{d+1} ≤ 1/(2C)`, the first term is below `n/2`. The second is
at most `C c^d L² n^{d/(d+1)} = o(n)`.
-/

namespace CERW.Support.Coarse

open Filter

/-- Raising `x^{1/(d+1)}` to the natural power `d + 1` recovers `x`. -/
private lemma rpow_unit_frac_nat_pow {x : ℝ} (hx : 0 < x) (d : ℕ) :
    (x ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) = x := by
  have hbase : 0 ≤ x := le_of_lt hx
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
  have hexp : ((1 : ℝ) / (d + 1)) * (((d + 1 : ℕ) : ℝ)) = 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  rw [hexp, Real.rpow_one]

/-- Raising `x^{1/(d+1)}` to the natural power `d` gives `x / x^{1/(d+1)}`. -/
private lemma rpow_unit_frac_nat_pow_div {x : ℝ} (hx : 0 < x) (d : ℕ) :
    (x ^ ((1 : ℝ) / (d + 1))) ^ d = x / x ^ ((1 : ℝ) / (d + 1)) := by
  have hN : 0 < x ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hx _
  rw [eq_div_iff hN.ne']
  rw [← pow_succ]
  exact rpow_unit_frac_nat_pow hx d

/-- For `C > 0` there is `c > 0` such that, for all large `n`, every `s ∈ [0, cN)` has
`C s^{d+1} + C L² s^d < n`, where `N = n^{1/(d+1)}` and `L = log(n + 2)`. -/
theorem exists_scale_lower {d : ℕ} (hd : 1 ≤ d) {C : ℝ} (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, 0 ≤ s →
      s < c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) →
        C * s ^ (d + 1) + C * Real.log (n + 2) ^ 2 * s ^ d < n := by
  let c : ℝ := (4 * C)⁻¹ ^ ((1 : ℝ) / (d + 1))
  have hCpos : 0 < 4 * C := mul_pos (by norm_num) hC
  have hc : 0 < c := by
    dsimp only [c]
    exact Real.rpow_pos_of_pos (inv_pos.mpr hCpos) _
  refine ⟨c, hc, ?_⟩
  have hcpow : c ^ (d + 1) = (4 * C)⁻¹ := by
    dsimp only [c]
    exact rpow_unit_frac_nat_pow (inv_pos.mpr hCpos) d
  have hB : 0 < (4 * C * c ^ d)⁻¹ := by
    rw [inv_pos]
    exact mul_pos hCpos (pow_pos hc d)
  have hlim := CERW.Support.Main.tendsto_log_rpow_div_rpow (2 : ℝ)
    (c := (1 : ℝ) / (d + 1)) (by positivity)
  filter_upwards [hlim.eventually_lt_const hB, Filter.eventually_ge_atTop (1 : ℕ)]
    with n hLn hn1
  intro s hs hsl
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
  have hs_le : s ≤ c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := le_of_lt hsl
  have hC4 : C * (4 * C)⁻¹ = 1 / 4 := by
    field_simp
  have hLn2 : Real.log (n + 2) ^ 2 / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) <
      (4 * C * c ^ d)⁻¹ := by
    rw [Real.rpow_two] at hLn
    exact hLn
  have h1 : C * s ^ (d + 1) ≤ n / 4 := by
    calc C * s ^ (d + 1)
        ≤ C * (c * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hs_le (d + 1)) hC.le
      _ = C * (c ^ (d + 1) * (n : ℝ)) := by
          rw [mul_pow, rpow_unit_frac_nat_pow hnpos d]
      _ = n / 4 := by
          rw [hcpow, ← mul_assoc, hC4]
          ring
  have h2 : C * Real.log (n + 2) ^ 2 * s ^ d ≤ n / 4 := by
    have hLnn : 0 ≤ Real.log (n + 2) ^ 2 := sq_nonneg _
    have hCd : 0 ≤ C * c ^ d := mul_nonneg hC.le (pow_nonneg hc.le d)
    calc C * Real.log (n + 2) ^ 2 * s ^ d
        ≤ C * Real.log (n + 2) ^ 2 *
            (c ^ d * ((n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))) :=
          mul_le_mul_of_nonneg_left
            (by
              calc s ^ d
                  ≤ (c * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d :=
                    pow_le_pow_left₀ hs hs_le d
                _ = c ^ d * ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d := by rw [mul_pow]
                _ = c ^ d * ((n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) := by
                    rw [rpow_unit_frac_nat_pow_div hnpos d])
            (mul_nonneg hC.le hLnn)
      _ = C * c ^ d * (n : ℝ) *
            (Real.log (n + 2) ^ 2 / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) := by
          ring
      _ ≤ C * c ^ d * (n : ℝ) * (4 * C * c ^ d)⁻¹ := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hLn2)
            (mul_nonneg hCd hnpos.le)
      _ = n / 4 := by
          field_simp
  linarith [h1, h2, hnpos]

end CERW.Support.Coarse
