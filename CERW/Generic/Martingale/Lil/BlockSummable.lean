import CERW.Generic.Martingale.Lil.Statements

/-!
# The block bounds are summable

For block `k` the exponent of Freedman's bound is at least `(1 + η) log log θ^k`, so the bound
is at most `(k log θ)^{-(1+η)}`, which is summable.
-/

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- A number above `e` is above `1`. -/
theorem one_lt_of_exp_one_lt {x : ℝ} (hx : Real.exp 1 < x) : 1 < x := by
  have h : (1 : ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp one_ne_zero
  linarith

/-- Past `θ^k > e`, the exponent of block `k` is at least `(1 + η) log log θ^k`. -/
theorem block_exponent_ge {θ ε δ η : ℝ} (hp : LilParams θ ε δ η) {k : ℕ}
    (hk : Real.exp 1 < θ ^ k) :
    (1 + η) * Real.log (Real.log (θ ^ k)) ≤ blockRadius θ δ k ^ 2 /
      (2 * (θ ^ (k + 1) + blockTrunc θ ε k * blockRadius θ δ k / 3)) := by
  obtain ⟨hθ, hε, hδ, hη, hkey⟩ := hp
  have hx1 : 1 < θ ^ k := one_lt_of_exp_one_lt hk
  have hx0 : 0 < θ ^ k := by linarith
  have hlogx : 1 < Real.log (θ ^ k) := by
    rw [Real.lt_log_iff_exp_lt hx0]; exact hk
  have hL : 0 < Real.log (Real.log (θ ^ k)) := Real.log_pos hlogx
  generalize hxdef : θ ^ k = x at hx0 hL
  generalize hLdef : Real.log (Real.log x) = L at hL
  have hθ0 : 0 < θ := by linarith
  have hR2 : blockRadius θ δ k ^ 2 = (1 + δ) ^ 2 * (2 * x * L) := by
    unfold blockRadius
    rw [hxdef, hLdef, mul_pow, Real.sq_sqrt (by positivity)]
  have hbR : blockTrunc θ ε k * blockRadius θ δ k = ε * (1 + δ) * x * Real.sqrt (2 * θ) := by
    unfold blockRadius blockTrunc
    rw [pow_succ, hxdef, hLdef]
    have h1 : Real.sqrt (x * θ / L) * Real.sqrt (2 * x * L) = x * Real.sqrt (2 * θ) := by
      rw [← Real.sqrt_mul (by positivity)]
      have : x * θ / L * (2 * x * L) = (x * x) * (2 * θ) := by field_simp
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hx0.le]
    calc ε * Real.sqrt (x * θ / L) * ((1 + δ) * Real.sqrt (2 * x * L))
        = ε * (1 + δ) * (Real.sqrt (x * θ / L) * Real.sqrt (2 * x * L)) := by ring
      _ = _ := by rw [h1]; ring
  have hD : 0 < θ + ε * (1 + δ) * Real.sqrt (2 * θ) / 3 := by positivity
  have hden : 2 * (θ ^ (k + 1) + blockTrunc θ ε k * blockRadius θ δ k / 3) =
      2 * x * (θ + ε * (1 + δ) * Real.sqrt (2 * θ) / 3) := by
    rw [hbR, pow_succ, hxdef]; ring
  rw [hR2, hden, le_div_iff₀ (by positivity)]
  have h2 : (1 + η) * (θ + ε * (1 + δ) * Real.sqrt (2 * θ) / 3) * L ≤ (1 + δ) ^ 2 * L :=
    mul_le_mul_of_nonneg_right hkey hL.le
  have h3 : 0 ≤ x := hx0.le
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg h3 (by norm_num : (0 : ℝ) ≤ 2))]

/-- Past `θ^k > e`, the term of block `k` is at most `(log θ)^{-(1+η)} (k^{1+η})⁻¹`. -/
theorem block_term_le {θ ε δ η : ℝ} (hp : LilParams θ ε δ η) {k : ℕ} (hk : Real.exp 1 < θ ^ k) :
    Real.exp (-(blockRadius θ δ k ^ 2 /
      (2 * (θ ^ (k + 1) + blockTrunc θ ε k * blockRadius θ δ k / 3)))) ≤
      Real.log θ ^ (-(1 + η)) * (((k : ℝ) ^ (1 + η))⁻¹) := by
  have hge := block_exponent_ge hp hk
  have hθ : 1 < θ := hp.1
  have hlθ : 0 < Real.log θ := Real.log_pos hθ
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have h1 := one_lt_of_exp_one_lt hk
      simp at h1
    · exact h
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  calc Real.exp (-(blockRadius θ δ k ^ 2 /
        (2 * (θ ^ (k + 1) + blockTrunc θ ε k * blockRadius θ δ k / 3))))
      ≤ Real.exp (-((1 + η) * Real.log (Real.log (θ ^ k)))) :=
        Real.exp_le_exp.mpr (neg_le_neg hge)
    _ = ((k : ℝ) * Real.log θ) ^ (-(1 + η)) := by
        rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
        congr 1; ring
    _ = _ := by
        rw [Real.mul_rpow hkr.le hlθ.le, Real.rpow_neg hkr.le, mul_comm]

/-- The truncation levels are eventually positive, and the block bounds are summable. -/
theorem block_summable : BlockSummable := by
  intro θ ε δ η hp
  have hθ : 1 < θ := hp.1
  have hε : 0 < ε := hp.2.1
  have hη : 0 < η := hp.2.2.2.1
  have hev : ∀ᶠ k : ℕ in atTop, Real.exp 1 < θ ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt hθ).eventually_gt_atTop _
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with k hk
    have hx1 : 1 < θ ^ k := one_lt_of_exp_one_lt hk
    have hlogx : 1 < Real.log (θ ^ k) := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]; exact hk
    have hL : 0 < Real.log (Real.log (θ ^ k)) := Real.log_pos hlogx
    unfold blockTrunc
    have : 0 < θ ^ (k + 1) := by positivity
    positivity
  · set f : ℕ → ℝ := fun k => Real.exp (-(blockRadius θ δ k ^ 2 /
      (2 * (θ ^ (k + 1) + blockTrunc θ ε k * blockRadius θ δ k / 3)))) with hf
    have hsum : Summable f := by
      refine Summable.of_norm_bounded_eventually_nat
        ((Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + η)).mul_left
          (Real.log θ ^ (-(1 + η)))) ?_
      filter_upwards [hev] with k hk
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact block_term_le hp hk
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) hsum]
    exact ENNReal.ofReal_ne_top

end CERW.Generic.Martingale.Lil
