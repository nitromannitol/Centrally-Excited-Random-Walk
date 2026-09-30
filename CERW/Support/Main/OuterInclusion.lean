import CERW.Model.Occupation
import CERW.Support.Main.ScaleLimits

/-!
# The outer inclusion from the radius bound

For all large `n`: if `|b/N - a| ≤ C₂ Q` and `H_n ≤ b + C₂ W L` with `W = N Q^{1/d}`, then
every visited site has `|x| ≤ H_n ≤ aN + C₂ N Q + C₂ N Q^{1/d} L`. This is less than
`(a + C Q^{1/d} L) N` for `C = 2 C₂ + 1`, because `Q ≤ 1`, `L ≥ 1`, `Q ≤ Q^{1/d}` and
`N Q^{1/d} L > 0`.
-/

namespace CERW.Support.Main

open LatticeProb CERW

variable {d : ℕ}

/-- For `0 < Q ≤ 1` and `1 ≤ d`, the rate is at most its `1/d`-th power. -/
private lemma rpow_self_le_rpow_inv (hd : 1 ≤ d) {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    Q ≤ Q ^ ((1 : ℝ) / d) := by
  have hpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hle : (1 : ℝ) / d ≤ 1 := by
    rw [div_le_iff₀ hpos]
    linarith [show (1 : ℝ) ≤ (d : ℝ) by exact_mod_cast hd]
  have h := Real.rpow_le_rpow_of_exponent_ge hQ0 hQ1 hle
  rwa [Real.rpow_one] at h

/-- The radius bound and the inradius estimate give the strict outer bound
`b + C₂ N Q^{1/d} L < (a + (2C₂+1) Q^{1/d} L) N`. -/
private lemma radius_bound_lt {a C₂ N L Q b : ℝ} {d : ℕ}
    (hC₂ : 0 ≤ C₂) (hN : 0 < N) (hL : 1 ≤ L) (hQ : 0 < Q)
    (hQle : Q ≤ Q ^ ((1 : ℝ) / d))
    (hb : |b / N - a| ≤ C₂ * Q) :
    b + C₂ * (N * Q ^ ((1 : ℝ) / d)) * L <
      (a + (2 * C₂ + 1) * Q ^ ((1 : ℝ) / d) * L) * N := by
  have hb' : b ≤ (a + C₂ * Q) * N := by
    have h1 : b / N - a ≤ C₂ * Q := (abs_le.mp hb).2
    have h2 : b / N ≤ a + C₂ * Q := by linarith
    rw [div_le_iff₀ hN] at h2
    linarith
  have hkey : C₂ * Q * N + C₂ * (N * Q ^ ((1 : ℝ) / d)) * L <
      (2 * C₂ + 1) * Q ^ ((1 : ℝ) / d) * L * N := by
    have h1 : C₂ * Q * N ≤ C₂ * Q ^ ((1 : ℝ) / d) * N := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hN)
      exact mul_le_mul_of_nonneg_left hQle hC₂
    have h2 : (1 : ℝ) + L ≤ 2 * L := by linarith
    have h3 : C₂ * Q ^ ((1 : ℝ) / d) * N * ((1 : ℝ) + L) ≤
        C₂ * Q ^ ((1 : ℝ) / d) * N * (2 * L) := by
      apply mul_le_mul_of_nonneg_left h2
      positivity
    have hstrict : 2 * C₂ * Q ^ ((1 : ℝ) / d) * L * N <
        (2 * C₂ + 1) * Q ^ ((1 : ℝ) / d) * L * N := by
      have hp : 0 < Q ^ ((1 : ℝ) / d) * L * N := by positivity
      nlinarith [hp]
    calc C₂ * Q * N + C₂ * (N * Q ^ ((1 : ℝ) / d)) * L
        ≤ C₂ * Q ^ ((1 : ℝ) / d) * N + C₂ * (N * Q ^ ((1 : ℝ) / d)) * L := by
          linarith
      _ = C₂ * Q ^ ((1 : ℝ) / d) * N * ((1 : ℝ) + L) := by ring
      _ ≤ C₂ * Q ^ ((1 : ℝ) / d) * N * (2 * L) := h3
      _ = 2 * C₂ * Q ^ ((1 : ℝ) / d) * L * N := by ring
      _ < (2 * C₂ + 1) * Q ^ ((1 : ℝ) / d) * L * N := hstrict
  calc b + C₂ * (N * Q ^ ((1 : ℝ) / d)) * L
      ≤ (a + C₂ * Q) * N + C₂ * (N * Q ^ ((1 : ℝ) / d)) * L := by linarith
    _ = a * N + (C₂ * Q * N + C₂ * (N * Q ^ ((1 : ℝ) / d)) * L) := by ring
    _ < a * N + (2 * C₂ + 1) * Q ^ ((1 : ℝ) / d) * L * N := by linarith
    _ = (a + (2 * C₂ + 1) * Q ^ ((1 : ℝ) / d) * L) * N := by ring

/-- The outer inclusion of `eq:sandwich` from the inradius estimate and the radius bound. -/
theorem exists_outer_inclusion (hd : 2 ≤ d) {a C₂ : ℝ} (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ) (b : ℝ), n₀ ≤ n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      |b / N - a| ≤ C₂ * Q → maxRadius Y n ≤ b + C₂ * (N * Q ^ ((1 : ℝ) / d)) * L →
        (↑(visitedRange Y n) : Set (Site d)) ⊆
          {x | euclidNorm x < (a + C * Q ^ ((1 : ℝ) / d) * L) * N} := by
  have hQev : ∀ᶠ n : ℕ in Filter.atTop,
      (if d = 2 then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
       else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
         ^ ((d : ℝ) / (2 * d - 1))) < 1 :=
    (tendsto_rate_zero hd).eventually_lt_const (by norm_num)
  obtain ⟨n₁, hQbound⟩ := Filter.eventually_atTop.mp hQev
  refine ⟨2 * C₂ + 1, by linarith, max n₁ 1, ?_⟩
  intro Y n b hn N L Q hb hH x hx
  have hn1 : 1 ≤ n := le_trans (le_max_right n₁ 1) hn
  have hn₁ : n₁ ≤ n := le_trans (le_max_left n₁ 1) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < N := Real.rpow_pos_of_pos hnpos _
  have hL1 : 1 ≤ L := by
    have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h3 : (3 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have hlog : Real.log 3 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by norm_num) h3
    have hlt : (1 : ℝ) < Real.log 3 := lt_trans (by norm_num) Real.log_three_gt_d9
    linarith
  have hQpos : 0 < Q := by
    have hLN : 0 < L / N := div_pos (by linarith) hNpos
    change 0 < (if d = 2 then (L / N) ^ ((1 : ℝ) / 2)
      else (L / N) ^ ((d : ℝ) / (2 * (d : ℝ) - 1)))
    split_ifs
    · exact Real.rpow_pos_of_pos hLN _
    · exact Real.rpow_pos_of_pos hLN _
  have hQle1 : Q ≤ 1 := le_of_lt (hQbound n hn₁)
  have hQle : Q ≤ Q ^ ((1 : ℝ) / d) :=
    rpow_self_le_rpow_inv (show 1 ≤ d by omega) hQpos hQle1
  have hlt := radius_bound_lt hC₂ hNpos hL1 hQpos hQle hb
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hxnorm : euclidNorm x ≤ maxRadius Y n := by
    rw [← hjx]
    exact euclidNorm_le_maxRadius Y hjle
  exact lt_of_le_of_lt (le_trans hxnorm hH) hlt

end CERW.Support.Main
