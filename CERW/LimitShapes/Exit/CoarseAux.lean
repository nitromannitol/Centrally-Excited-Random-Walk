module

public import CERW.Support.Norm.CoarseVolume

@[expose] public section

/-!
# Deterministic consequences of a two-sided exit estimate

Occupation and lattice packing turn the exit control in Proposition `prop:coarse`
into bounds for paths stopped before the exit.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.CoarseVolume

/-- Before an exit whose lower time bound exceeds `n`, the radius and occupation
maximum obey the upper bounds used in Proposition `prop:coarse`. -/
theorem maxima_le_of_exit {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (x : ℕ → Site d) {n τ : ℕ} {c C R : ℝ}
    (hn : (n : ℝ) < c * R ^ (d + 1))
    (ht : c * R ^ (d + 1) ≤ (τ : ℝ))
    (hi : ∀ j : ℕ, j < τ → Ψ (toSpace (x j)) < R)
    (hl : ∀ y : Site d, (localTime x τ y : ℝ) ≤ C * R) :
    maxRadius x n ≤ R / normMin Ψ ∧ (maxLocalTime x n : ℝ) ≤ C * R := by
  have hnt : n < τ := by exact_mod_cast hn.trans_le ht
  obtain ⟨hm, hc⟩ := Generic.Norm.normMin_pos_mul_le hΨ hd
  constructor
  · apply Finset.sup'_le
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    apply (le_div_iff₀ hm).mpr
    have h := hc (toSpace (x j))
    rw [norm_toSpace] at h
    have h' : euclidNorm (x j) * normMin Ψ ≤ Ψ (toSpace (x j)) := by
      simpa only [mul_comm] using h
    exact h'.trans (hi j (by omega)).le
  · have hmono : ∀ y, localTime x n y ≤ localTime x τ y := by
      intro y
      exact Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.range_subset_range.mpr hnt.le))
    have hCR : 0 ≤ C * R := (Nat.cast_nonneg (localTime x τ 0)).trans (hl 0)
    have hb : maxLocalTime x n ≤ ⌊C * R⌋₊ := by
      apply Finset.sup_le
      intro y _
      exact (Nat.le_floor_iff hCR).mpr
        ((Nat.cast_le.mpr (hmono y)).trans (hl y))
    exact (Nat.cast_le.mpr hb).trans (Nat.floor_le hCR)

/-- Lattice packing and the mass identity bound the number of sites and occupation
maximum from below once both upper bounds at scale `r` are available. -/
theorem occupation_bounds_of_maxima {d : ℕ} (x : ℕ → Site d) (n : ℕ)
    {κ r H L : ℝ} (hr : 1 ≤ r) (hH : 0 ≤ H) (hL : 0 < L)
    (_hκ : 0 < κ) (ht : (n : ℝ) = κ * r ^ (d + 1))
    (hh : maxRadius x n ≤ H * r) (hl : (maxLocalTime x n : ℝ) ≤ L * r) :
    κ / L * r ^ d ≤ ((departureRange x n).card : ℝ) ∧
    ((departureRange x n).card : ℝ) ≤ (2 * H + 1) ^ d * r ^ d ∧
    κ / (2 * H + 1) ^ d * r ≤ (maxLocalTime x n : ℝ) := by
  have hr0 : 0 < r := by linarith
  have hmass : (n : ℝ) ≤ (maxLocalTime x n : ℝ) * (departureRange x n).card := by
    exact_mod_cast Support.Occupation.le_maxLocalTime_mul_card x n
  have hcard : ((departureRange x n).card : ℝ) ≤ (2 * H + 1) ^ d * r ^ d := by
    calc
      _ ≤ (2 * maxRadius x n + 1) ^ d := card_le_pow_maxRadius x n
      _ ≤ ((2 * H + 1) * r) ^ d := by
        apply pow_le_pow_left₀
        · have hnon := (euclidNorm_nonneg (x 0)).trans
            (euclidNorm_le_maxRadius x (Nat.zero_le n))
          positivity
        · nlinarith
      _ = _ := mul_pow _ _ _
  have hU : 0 < (2 * H + 1) ^ d := pow_pos (by positivity) _
  refine ⟨?_, hcard, ?_⟩
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL).mpr
    have hb := hmass.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _))
    rw [ht, pow_succ] at hb
    have hb' : κ * r ^ d ≤ L * (departureRange x n).card := by
      apply (mul_le_mul_iff_right₀ hr0).mp
      nlinarith only [hb]
    nlinarith only [hb']
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hU).mpr
    have hb := hmass.trans (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _))
    rw [ht, pow_succ] at hb
    have hb' : κ * r ≤ (maxLocalTime x n : ℝ) * (2 * H + 1) ^ d := by
      apply (mul_le_mul_iff_right₀ (pow_pos hr0 d)).mp
      nlinarith only [hb]
    nlinarith only [hb']

/-- A lower bound for the number of sites forces a lower radius by lattice packing. -/
theorem radius_lower_of_card {d : ℕ} (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ)
    {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r)
    (hlarge : 2 ≤ a ^ ((1 : ℝ) / d) * r)
    (hcard : a * r ^ d ≤ ((departureRange x n).card : ℝ)) :
    a ^ ((1 : ℝ) / d) / 4 * r ≤ maxRadius x n := by
  have hroot : a ^ ((1 : ℝ) / d) * r ≤
      ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) := by
    calc
      _ = (a * r ^ d) ^ ((1 : ℝ) / d) := by
        rw [Real.mul_rpow ha.le (pow_nonneg hr _)]
        rw [one_div, Real.pow_rpow_inv_natCast hr (by omega : d ≠ 0)]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hcard (by positivity)
  have hb := hroot.trans (rpow_card_le hd x n)
  linarith

end CERW.LimitShapes.Exit
