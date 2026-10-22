import CERW.LimitShapes.Crossing.Projection
import CERW.LimitShapes.Event

/-!
# Extending distance crossings from integer to real norm levels

Radial contraction moves a point in a norm ball to a smaller norm ball at
controlled Euclidean cost. Rounding a nonnegative radius up to an integer
therefore preserves the crossing estimate after a fixed logarithmic error.
-/

open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.Crossing.Levels

open CERW CERW.Support.Norm.Section5Localization

/-- Radial contraction by at most one unit in the norm changes the Euclidean
competitor by at most the reciprocal of the norm's minimum on the unit sphere. -/
theorem infDist_le_norm_sub_add {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {a m : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (ham : a ≤ m) (hma : m ≤ a + 1)
    (y z : EuclideanSpace ℝ (Fin d)) (hz : Ψ z ≤ m) :
    Metric.infDist y {v | Ψ v ≤ a} ≤ ‖y - z‖ + 1 / normMin Ψ := by
  obtain ⟨hc, hcz⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have ht : 0 ≤ a / m := div_nonneg ha hm.le
  have ht1 : a / m ≤ 1 := (div_le_one hm).mpr ham
  have hmem : Ψ ((a / m) • z) ≤ a := by
    rw [hΨ.smul, abs_of_nonneg ht]
    calc a / m * Ψ z ≤ a / m * m := mul_le_mul_of_nonneg_left hz ht
      _ = a := div_mul_cancel₀ _ hm.ne'
  have hzbound : ‖z‖ ≤ m / normMin Ψ :=
    (le_div_iff₀ hc).mpr (by nlinarith [hcz z])
  have hmove : ‖z - (a / m) • z‖ ≤ 1 / normMin Ψ := by
    have heq : z - (a / m) • z = (1 - a / m) • z := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - a / m)]
    calc (1 - a / m) * ‖z‖ ≤ (1 - a / m) * (m / normMin Ψ) :=
        mul_le_mul_of_nonneg_left hzbound (by linarith)
      _ = (m - a) / normMin Ψ := by field_simp
      _ ≤ 1 / normMin Ψ := div_le_div_of_nonneg_right (by linarith) hc.le
  calc Metric.infDist y {v | Ψ v ≤ a} ≤ dist y ((a / m) • z) :=
      Metric.infDist_le_dist_of_mem hmem
    _ ≤ dist y z + dist z ((a / m) • z) := dist_triangle _ _ _
    _ ≤ ‖y - z‖ + 1 / normMin Ψ := by rw [dist_eq_norm, dist_eq_norm]; linarith

/-- Increasing the norm level decreases the largest exterior local time. -/
theorem exteriorLocalTime_antitone {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (X : ℕ → Site d) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    exteriorLocalTime Ψ X n b ≤ exteriorLocalTime Ψ X n a := by
  unfold exteriorLocalTime
  refine Finset.sup_le fun z hz => ?_
  obtain ⟨hz, hzb⟩ := Finset.mem_filter.mp hz
  exact Finset.le_sup (f := localTime X n) (Finset.mem_filter.mpr ⟨hz, hab.trans hzb⟩)

/-- Distance bounds at positive integer norm levels imply the simultaneous bound
at all nonnegative real levels, with a constant independent of the path and horizon. -/
theorem distanceCrossingBound_of_integer_levels {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d), X 0 = 0 →
      (∀ j, X (j + 1) - X j ∈ unitSteps d) → ∀ N : ℕ, 2 ≤ N →
      (∀ m : ℕ, 1 ≤ m → m ≤ ⌈normMax Ψ * N⌉₊ →
        ∀ t : ℕ, t ≤ N → ∀ j : ℕ, j ≤ t →
          ‖toSpace (X j) - canonicalProjection Ψ m (toSpace (X j))‖ ≤
            C₀ * (1 + (exteriorLocalTime Ψ X t m : ℝ)) * Real.log N) →
      DistanceCrossingBound Ψ C X N := by
  obtain ⟨hc, hcv⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc
    (CERW.Support.Norm.ProjectionGeometry.normMin_le_normMax hΨ hd)
  refine ⟨C₀ + 2 / normMin Ψ, by positivity, ?_⟩
  intro X hX0 hstep N hN hint t ht a ha j hj
  have hlog : 1 / 2 ≤ Real.log N := by
    have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≤ N by exact_mod_cast hN)
    norm_num at h2
    linarith
  have hL : 0 ≤ (exteriorLocalTime Ψ X t a : ℝ) := Nat.cast_nonneg _
  by_cases hlarge : normMax Ψ * N ≤ a
  · have hnorm := CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hstep j
    have hjN : (j : ℝ) ≤ N := Nat.cast_le.mpr (hj.trans ht)
    have hmem : Ψ (toSpace (X j)) ≤ a := by
      have h := CERW.Generic.Norm.le_normMax_mul hΨ (toSpace (X j))
      rw [norm_toSpace] at h
      exact h.trans ((mul_le_mul_of_nonneg_left (hnorm.trans hjN) hΛ.le).trans hlarge)
    rw [Metric.infDist_zero_of_mem
      (show toSpace (X j) ∈ {v | Ψ v ≤ a} from hmem)]
    positivity
  · let m := max 1 ⌈a⌉₊
    have hm1 : 1 ≤ m := le_max_left _ _
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hceil : 1 ≤ ⌈normMax Ψ * N⌉₊ := by
      apply Nat.succ_le_of_lt
      exact Nat.ceil_pos.mpr (mul_pos hΛ (by exact_mod_cast (by omega : 0 < N)))
    have hmN : m ≤ ⌈normMax Ψ * N⌉₊ :=
      max_le hceil (Nat.ceil_le_ceil (not_le.mp hlarge).le)
    have ham : a ≤ m := (Nat.le_ceil a).trans (Nat.cast_le.mpr (le_max_right _ _))
    have hma : (m : ℝ) ≤ a + 1 := by
      dsimp [m]
      rcases le_total 1 ⌈a⌉₊ with h | h
      · rw [max_eq_right h]
        exact (Nat.ceil_lt_add_one ha).le
      · rw [max_eq_left h]
        norm_num
        linarith
    have hPm := (canonicalProjection_spec hΨ (by positivity : (0 : ℝ) ≤ m)
      (toSpace (X j))).1
    have hdist := infDist_le_norm_sub_add hd hΨ ha hm0 ham hma (toSpace (X j))
      (canonicalProjection Ψ m (toSpace (X j))) hPm
    have hInt := hint m hm1 hmN t ht j hj
    have hlocal : (exteriorLocalTime Ψ X t m : ℝ) ≤ exteriorLocalTime Ψ X t a :=
      Nat.cast_le.mpr (exteriorLocalTime_antitone Ψ X t ham)
    have hbound : C₀ * (1 + (exteriorLocalTime Ψ X t m : ℝ)) * Real.log N ≤
        C₀ * (1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hC₀) (by linarith)
    have herr : 1 / normMin Ψ ≤
        (2 / normMin Ψ) * (1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N := by
      have hprod : 1 / 2 ≤ (1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N := by
        nlinarith
      have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 / normMin Ψ by positivity)
      have heq : (2 / normMin Ψ) * (1 / 2) = 1 / normMin Ψ := by ring
      rw [heq] at h
      calc 1 / normMin Ψ ≤ (2 / normMin Ψ) *
            ((1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N) := h
        _ = (2 / normMin Ψ) * (1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N := by
          ring
    calc Metric.infDist (toSpace (X j)) {v | Ψ v ≤ a}
        ≤ ‖toSpace (X j) - canonicalProjection Ψ m (toSpace (X j))‖ +
            1 / normMin Ψ := hdist
      _ ≤ C₀ * (1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N +
          (2 / normMin Ψ) * (1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N :=
        add_le_add (hInt.trans hbound) herr
      _ = (C₀ + 2 / normMin Ψ) * (1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N := by
        ring

end CERW.LimitShapes.Crossing.Levels
