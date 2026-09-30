import CERW.Support.Main.ScaleLimits

/-!
# Absorbing the mass error

The last step of `prop:coarse`: `eq:radial-packing` and `eq:coarse-masserror` give
`c s^{d+1} ≤ n + C s^{d+1/2} L`, with `s = R_n^{1/d} ≥ c₀ N`. Since `L = o(√s)`, half of the
left side absorbs the error, so `s^{d+1} ≤ (2/c) n` and `s ≤ C' N`.
-/

namespace CERW.Support.Coarse

open Filter Topology

/-- For `c, c₀ > 0` and `C ≥ 0` there is `C'` such that, for all large `n`, every
`s ≥ c₀ N` with `c s^{d+1} ≤ n + C s^{d+1/2} L` satisfies `s ≤ C' N`. -/
theorem exists_le_of_mass {d : ℕ} {c c₀ C : ℝ} (hc : 0 < c) (hc₀ : 0 < c₀) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, c₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ s →
      c * s ^ (d + 1) ≤ n + C * s ^ ((d : ℝ) + 1 / 2) * Real.log (n + 2) →
        s ≤ C' * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  let C' : ℝ := (2 / c) ^ ((1 : ℝ) / (d + 1))
  have hC'pos : 0 < C' := by
    dsimp only [C']
    exact Real.rpow_pos_of_pos (div_pos two_pos hc) _
  refine ⟨C', hC'pos, ?_⟩
  let θ : ℝ := c * Real.sqrt c₀ / (2 * C + 1)
  have hθpos : 0 < θ := by
    dsimp only [θ]
    apply div_pos
    · exact mul_pos hc (Real.sqrt_pos.mpr hc₀)
    · linarith
  have hlim : Tendsto (fun n : ℕ => Real.log (n + 2) ^ (1 : ℝ) /
      (n : ℝ) ^ ((1 : ℝ) / (2 * (d + 1)))) atTop (𝓝 0) :=
    CERW.Support.Main.tendsto_log_rpow_div_rpow (1 : ℝ) (by positivity)
  have hbound : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (2 * (d + 1))) ≤ θ := by
    filter_upwards [hlim.eventually_le_const hθpos] with n hn
    simpa [Real.rpow_one] using hn
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with n hbound_n hn1
  intro s hs hineq
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Real.rpow_pos_of_pos hnpos _
  have hc0Npos : 0 < c₀ * N := mul_pos hc₀ hNpos
  have hspos : 0 < s := lt_of_lt_of_le hc0Npos hs
  have hL_nonneg : 0 ≤ Real.log (n + 2) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hNhalf : N ^ (1 / 2 : ℝ) = (n : ℝ) ^ ((1 : ℝ) / (2 * (d + 1))) := by
    dsimp only [N]
    rw [← Real.rpow_mul (Nat.cast_nonneg n) ((1 : ℝ) / (d + 1)) (1 / 2)]
    congr 1
    field_simp
  have hLN : Real.log (n + 2) * N ^ (-(1 / 2) : ℝ) ≤ θ := by
    have h := hbound_n
    rw [div_eq_mul_inv, ← hNhalf, ← Real.rpow_neg hNpos.le] at h
    exact h
  have hs_decomp : s ^ ((d : ℝ) + 1 / 2) =
      s ^ (d + 1) * s ^ (-(1 / 2) : ℝ) := by
    calc s ^ ((d : ℝ) + 1 / 2)
        = s ^ (((d + 1 : ℕ) : ℝ) + (-(1 / 2) : ℝ)) := by
          congr 1
          push_cast
          ring
      _ = s ^ ((d + 1 : ℕ) : ℝ) * s ^ (-(1 / 2) : ℝ) := Real.rpow_add hspos _ _
      _ = s ^ (d + 1) * s ^ (-(1 / 2) : ℝ) := by rw [Real.rpow_natCast]
  have hs_inv_le : s ^ (-(1 / 2) : ℝ) ≤
      c₀ ^ (-(1 / 2) : ℝ) * N ^ (-(1 / 2) : ℝ) := by
    calc s ^ (-(1 / 2) : ℝ) ≤ (c₀ * N) ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hc0Npos hs (by norm_num)
      _ = c₀ ^ (-(1 / 2) : ℝ) * N ^ (-(1 / 2) : ℝ) := Real.mul_rpow hc₀.le hNpos.le
  have hA_nonneg : 0 ≤ s ^ (d + 1) := pow_nonneg hspos.le _
  have hK_nonneg : 0 ≤ C * c₀ ^ (-(1 / 2) : ℝ) :=
    mul_nonneg hC (Real.rpow_nonneg hc₀.le _)
  have hinv : c₀ ^ (-(1 / 2) : ℝ) * Real.sqrt c₀ = 1 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hc₀.le,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hc₀ _).ne']
  have hKθ : C * c₀ ^ (-(1 / 2) : ℝ) * θ ≤ c / 2 := by
    have hdenpos : 0 < 2 * C + 1 := by linarith
    dsimp only [θ]
    calc C * c₀ ^ (-(1 / 2) : ℝ) * (c * Real.sqrt c₀ / (2 * C + 1))
        = (C * c) * (c₀ ^ (-(1 / 2) : ℝ) * Real.sqrt c₀) / (2 * C + 1) := by ring
      _ = (C * c) / (2 * C + 1) := by rw [hinv, mul_one]
      _ ≤ c / 2 := by
          rw [div_le_iff₀ hdenpos]
          nlinarith [hc]
  have hmassL : C * s ^ ((d : ℝ) + 1 / 2) * Real.log (n + 2) ≤
      (c / 2) * s ^ (d + 1) := by
    calc C * s ^ ((d : ℝ) + 1 / 2) * Real.log (n + 2)
        = (C * Real.log (n + 2) * s ^ (d + 1)) * s ^ (-(1 / 2) : ℝ) := by
          rw [hs_decomp]
          ring
      _ ≤ (C * Real.log (n + 2) * s ^ (d + 1)) *
            (c₀ ^ (-(1 / 2) : ℝ) * N ^ (-(1 / 2) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hs_inv_le
          exact mul_nonneg (mul_nonneg hC hL_nonneg) hA_nonneg
      _ = (C * c₀ ^ (-(1 / 2) : ℝ)) * (Real.log (n + 2) * N ^ (-(1 / 2) : ℝ)) *
            s ^ (d + 1) := by ring
      _ ≤ (C * c₀ ^ (-(1 / 2) : ℝ)) * θ * s ^ (d + 1) := by
          apply mul_le_mul_of_nonneg_right _ hA_nonneg
          exact mul_le_mul_of_nonneg_left hLN hK_nonneg
      _ ≤ (c / 2) * s ^ (d + 1) := mul_le_mul_of_nonneg_right hKθ hA_nonneg
  have hhalf : (c / 2) * s ^ (d + 1) ≤ (n : ℝ) := by
    have h1 : c * s ^ (d + 1) = 2 * ((c / 2) * s ^ (d + 1)) := by ring
    have h2 : c * s ^ (d + 1) ≤ (n : ℝ) + (c / 2) * s ^ (d + 1) :=
      by linarith [hineq, hmassL]
    rw [h1] at h2
    linarith
  have hc_half_pos : 0 < c / 2 := by linarith
  have hpow : s ^ (d + 1) ≤ (2 / c) * (n : ℝ) := by
    have hX : s ^ (d + 1) * (c / 2) ≤ (n : ℝ) := by
      rw [mul_comm]
      exact hhalf
    calc s ^ (d + 1) ≤ (n : ℝ) / (c / 2) := (le_div_iff₀ hc_half_pos).mpr hX
      _ = (2 / c) * (n : ℝ) := by field_simp
  have hroot_s : (s ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) = s := by
    have hd1 : d + 1 ≠ 0 := by omega
    simpa [one_div] using Real.pow_rpow_inv_natCast hspos.le hd1
  have hroot : (s ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) ≤
      ((2 / c) * (n : ℝ)) ^ ((1 : ℝ) / (d + 1)) :=
    Real.rpow_le_rpow hA_nonneg hpow (by positivity)
  have hroot_rhs : ((2 / c) * (n : ℝ)) ^ ((1 : ℝ) / (d + 1)) = C' * N := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / c) (Nat.cast_nonneg n)]
  calc s = (s ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) := hroot_s.symm
    _ ≤ ((2 / c) * (n : ℝ)) ^ ((1 : ℝ) / (d + 1)) := hroot
    _ = C' * N := hroot_rhs

end CERW.Support.Coarse
