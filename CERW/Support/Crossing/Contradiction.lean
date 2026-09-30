import CERW.Support.Main.ScaleLimits

/-!
# The crossing bound is eventually contradictory

The crossing estimate forces `s² ≤ C (s^γ L^{2γ} + s L⁴)` with `γ < 2`, on a scale `s ≥ c N`
(`eq:coarse-contradiction`). Since every power of `L = log(n+2)` is negligible against every
positive power of `n`, this inequality fails for all large `n`, uniformly in `s ≥ c N`.
-/

namespace CERW.Support.Crossing

open Filter Topology

/-- For positive `s` and real `γ`, `s^2 * s^(γ-2) = s^γ`. -/
lemma sq_mul_rpow_sub_two {s γ : ℝ} (hs : 0 < s) :
    s ^ 2 * s ^ (γ - 2) = s ^ γ := by
  rw [← Real.rpow_two, ← Real.rpow_add hs]
  ring_nf

/-- For positive `s`, `s^2 * s^(-1) = s`. -/
lemma sq_mul_rpow_neg_one {s : ℝ} (hs : 0 < s) :
    s ^ 2 * s ^ (-1 : ℝ) = s := by
  rw [← Real.rpow_two, ← Real.rpow_add hs]
  rw [show (2 : ℝ) + (-1) = 1 by norm_num, Real.rpow_one]

/-- For positive `c` and real `γ`, `c^(γ-2) * c^(2-γ) = 1`. -/
lemma rpow_sub_two_mul_rpow_two_sub {c γ : ℝ} (hc : 0 < c) :
    c ^ (γ - 2) * c ^ (2 - γ) = 1 := by
  rw [← Real.rpow_add hc, show γ - 2 + (2 - γ) = 0 by ring, Real.rpow_zero]

/-- For positive `c`, `c^(-1) * c = 1`. -/
lemma rpow_neg_one_mul_self {c : ℝ} (hc : 0 < c) : c ^ (-1 : ℝ) * c = 1 := by
  rw [Real.rpow_neg (le_of_lt hc) 1, Real.rpow_one, inv_mul_cancel₀ hc.ne']

/-- For `γ < 2` and `C, c > 0` there is `n₁` such that for `n ≥ n₁` and every
`s ≥ c n^{1/(d+1)}`, `C (s^γ L^{2γ} + s L⁴) < s²`, where `L = log(n+2)`. -/
theorem eventually_lt_sq {d : ℕ} {γ : ℝ} (hγ : γ < 2) {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ s : ℝ, c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ s →
      C * (s ^ γ * Real.log (n + 2) ^ (2 * γ) + s * Real.log (n + 2) ^ (4 : ℝ)) < s ^ 2 := by
  set c1 : ℝ := (2 - γ) / ((d : ℝ) + 1) with hc1def
  set B1 : ℝ := c ^ (2 - γ) / (2 * C) with hB1def
  set c2 : ℝ := 1 / ((d : ℝ) + 1) with hc2def
  set B2 : ℝ := c / (2 * C) with hB2def
  have hc1 : 0 < c1 := by
    rw [hc1def]
    exact div_pos (by linarith) (by positivity)
  have hB1pos : 0 < B1 := by
    rw [hB1def]
    exact div_pos (Real.rpow_pos_of_pos hc _) (by linarith)
  have hc2 : 0 < c2 := by
    rw [hc2def]
    exact div_pos zero_lt_one (by positivity)
  have hB2pos : 0 < B2 := by
    rw [hB2def]
    exact div_pos hc (by linarith)
  have hev1 : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) ^ (2 * γ) / (n : ℝ) ^ c1 < B1 :=
    (CERW.Support.Main.tendsto_log_rpow_div_rpow (2 * γ) hc1).eventually_lt_const hB1pos
  have hev2 : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) ^ (4 : ℝ) / (n : ℝ) ^ c2 < B2 :=
    (CERW.Support.Main.tendsto_log_rpow_div_rpow (4 : ℝ) hc2).eventually_lt_const hB2pos
  obtain ⟨n1, hn1⟩ := Filter.eventually_atTop.1 hev1
  obtain ⟨n2, hn2⟩ := Filter.eventually_atTop.1 hev2
  refine ⟨max 1 (max n1 n2), ?_⟩
  intro n hn s hs
  have h1n : 1 ≤ n := le_trans (le_max_left 1 (max n1 n2)) hn
  have hn1n : n1 ≤ n :=
    le_trans (le_trans (le_max_left n1 n2) (le_max_right 1 (max n1 n2))) hn
  have hn2n : n2 ≤ n :=
    le_trans (le_trans (le_max_right n1 n2) (le_max_right 1 (max n1 n2))) hn
  have hsmall1 := hn1 n hn1n
  have hsmall2 := hn2 n hn2n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)) := Real.rpow_pos_of_pos hnpos _
  have hLpos : 0 < Real.log (n + 2) :=
    Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega))
  have hcNpos : 0 < c * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)) := mul_pos hc hNpos
  have hspos : 0 < s := lt_of_lt_of_le hcNpos hs
  have hNm : ((n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))) ^ (γ - 2) = (n : ℝ) ^ (-c1) := by
    rw [← Real.rpow_mul (le_of_lt hnpos)]
    congr 1
    rw [hc1def]
    ring
  have hNm2 : ((n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))) ^ (-1 : ℝ) = (n : ℝ) ^ (-c2) := by
    rw [← Real.rpow_mul (le_of_lt hnpos)]
    congr 1
    rw [hc2def]
    ring
  have hsγ2_le : s ^ (γ - 2) ≤ c ^ (γ - 2) / (n : ℝ) ^ c1 := by
    calc
      s ^ (γ - 2) ≤ (c * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))) ^ (γ - 2) :=
        Real.rpow_le_rpow_of_nonpos hcNpos hs (by linarith)
      _ = c ^ (γ - 2) * ((n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))) ^ (γ - 2) :=
        Real.mul_rpow (le_of_lt hc) (le_of_lt hNpos)
      _ = c ^ (γ - 2) * (n : ℝ) ^ (-c1) := by rw [hNm]
      _ = c ^ (γ - 2) / (n : ℝ) ^ c1 := by
        rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hnpos) c1]
  have hsinv_le : s ^ (-1 : ℝ) ≤ c ^ (-1 : ℝ) * (n : ℝ) ^ (-c2) := by
    have hbase : s ^ (-1 : ℝ) ≤
        (c * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hcNpos hs (by norm_num)
    rw [Real.mul_rpow (le_of_lt hc) (le_of_lt hNpos)] at hbase
    rwa [hNm2] at hbase
  have hB1id : c ^ (γ - 2) * B1 = 1 / (2 * C) := by
    rw [hB1def, ← mul_div_assoc, rpow_sub_two_mul_rpow_two_sub hc]
  have hB2id : c ^ (-1 : ℝ) * B2 = 1 / (2 * C) := by
    rw [hB2def, ← mul_div_assoc, rpow_neg_one_mul_self hc]
  have hterm1 : C * (s ^ γ * Real.log (n + 2) ^ (2 * γ)) < s ^ 2 / 2 := by
    calc
      C * (s ^ γ * Real.log (n + 2) ^ (2 * γ))
          = C * s ^ 2 * (s ^ (γ - 2) * Real.log (n + 2) ^ (2 * γ)) := by
            rw [← sq_mul_rpow_sub_two hspos]
            ring
        _ ≤ C * s ^ 2 * ((c ^ (γ - 2) / (n : ℝ) ^ c1)
              * Real.log (n + 2) ^ (2 * γ)) := by
            gcongr
        _ = C * s ^ 2 * c ^ (γ - 2)
              * (Real.log (n + 2) ^ (2 * γ) / (n : ℝ) ^ c1) := by ring
        _ < C * s ^ 2 * c ^ (γ - 2) * B1 := by
            gcongr
        _ = C * s ^ 2 * (c ^ (γ - 2) * B1) := by ring
        _ = C * s ^ 2 * (1 / (2 * C)) := by rw [hB1id]
        _ = s ^ 2 / 2 := by
            rw [mul_one_div]
            field_simp
  have hterm2 : C * (s * Real.log (n + 2) ^ (4 : ℝ)) < s ^ 2 / 2 := by
    have hs_mul : s * Real.log (n + 2) ^ (4 : ℝ)
        = s ^ 2 * (s ^ (-1 : ℝ) * Real.log (n + 2) ^ (4 : ℝ)) := by
      rw [← mul_assoc, sq_mul_rpow_neg_one hspos]
    calc
      C * (s * Real.log (n + 2) ^ (4 : ℝ))
          = C * s ^ 2 * (s ^ (-1 : ℝ) * Real.log (n + 2) ^ (4 : ℝ)) := by
            rw [hs_mul]
            ring
        _ ≤ C * s ^ 2 * ((c ^ (-1 : ℝ) * (n : ℝ) ^ (-c2))
              * Real.log (n + 2) ^ (4 : ℝ)) := by
            gcongr
        _ = C * s ^ 2 * c ^ (-1 : ℝ)
              * (Real.log (n + 2) ^ (4 : ℝ) / (n : ℝ) ^ c2) := by
            rw [Real.rpow_neg (le_of_lt hnpos) c2]
            ring
        _ < C * s ^ 2 * c ^ (-1 : ℝ) * B2 := by
            gcongr
        _ = C * s ^ 2 * (c ^ (-1 : ℝ) * B2) := by ring
        _ = C * s ^ 2 * (1 / (2 * C)) := by rw [hB2id]
        _ = s ^ 2 / 2 := by
            rw [mul_one_div]
            field_simp
  calc
    C * (s ^ γ * Real.log (n + 2) ^ (2 * γ)
          + s * Real.log (n + 2) ^ (4 : ℝ))
        = C * (s ^ γ * Real.log (n + 2) ^ (2 * γ))
          + C * (s * Real.log (n + 2) ^ (4 : ℝ)) := by ring
      _ < s ^ 2 / 2 + s ^ 2 / 2 := add_lt_add hterm1 hterm2
      _ = s ^ 2 := by ring

end CERW.Support.Crossing
