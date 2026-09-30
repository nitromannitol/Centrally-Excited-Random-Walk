import CERW.Model.DriftKernel
import CERW.Support.Law.Moments

/-!
# The moments of the drift first-departure kernel

The drift kernel is nonnegative when `ε |w_i| ≤ 1/d` for every coordinate, sums to one over the
unit steps, and has mean `-ε w`.
-/

namespace CERW.Support.Drift

open LatticeProb CERW CERW.Support.Law

variable {d : ℕ}

/-- The drift kernel at `e_i` is `1/(2d) - (ε/2) w_i`. -/
private theorem driftFirstStep_unit_value (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    driftFirstStep d ε w (unit i) = 1 / (2 * d) - ε / 2 * w i := by
  unfold driftFirstStep
  rw [Finset.sum_eq_single i]
  · simp [unit_ne_neg_unit i]
  · intro j _ hj
    have h1 : unit i ≠ unit j := fun h => hj (unit_injective h).symm
    have h2 : unit i ≠ -unit j := unit_ne_neg_unit' i j
    simp [h1, h2]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The drift kernel at `-e_i` is `1/(2d) + (ε/2) w_i`. -/
private theorem driftFirstStep_neg_unit_value (ε : ℝ) (w : EuclideanSpace ℝ (Fin d))
    (i : Fin d) :
    driftFirstStep d ε w (-unit i) = 1 / (2 * d) + ε / 2 * w i := by
  unfold driftFirstStep
  rw [Finset.sum_eq_single i]
  · simp [(unit_ne_neg_unit i).symm]
  · intro j _ hj
    have h1 : -unit i ≠ unit j := by
      intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj)] at this
    have h2 : -unit i ≠ -unit j := by
      intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj)] at this
    simp [h1, h2]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- An arbitrary vector is the sum of its coordinates times the embedded unit steps. -/
private theorem eq_sum_coord_smul_unit (w : EuclideanSpace ℝ (Fin d)) :
    w = ∑ i : Fin d, w i • toSpace (unit i) := by
  apply PiLp.ext
  intro j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.smul_apply, toSpace_apply]
  rw [Finset.sum_eq_single j]
  · simp [unit, Pi.single_eq_same]
  · intro i _ hi
    simp [unit, Pi.single_eq_of_ne (Ne.symm hi)]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- The drift kernel is nonnegative when `0 ≤ ε` and `ε |w_i| ≤ 1/d` for every `i`. -/
theorem driftFirstStep_nonneg {ε : ℝ} (hε : 0 ≤ ε) {w : EuclideanSpace ℝ (Fin d)}
    (hw : ∀ i, ε * |w i| ≤ 1 / (d : ℝ)) (e : Site d) : 0 ≤ driftFirstStep d ε w e := by
  unfold driftFirstStep
  apply Finset.sum_nonneg
  intro i _
  have hε2 : (0 : ℝ) ≤ ε / 2 := by linarith
  have hw' : ε / 2 * |w i| ≤ 1 / (2 * d) := by
    have h : (ε * |w i|) / 2 ≤ (1 / (d : ℝ)) / 2 := by linarith [hw i]
    have h1 : ε / 2 * |w i| = (ε * |w i|) / 2 := by ring
    have h2 : (1 / (d : ℝ)) / 2 = 1 / (2 * d) := by ring
    linarith
  have hle : ε / 2 * w i ≤ 1 / (2 * d) :=
    calc ε / 2 * w i ≤ ε / 2 * |w i| := mul_le_mul_of_nonneg_left (le_abs_self _) hε2
      _ ≤ 1 / (2 * d) := hw'
  have hge : -(1 / (2 * d)) ≤ ε / 2 * w i := by
    have h : ε / 2 * (-|w i|) ≤ ε / 2 * w i :=
      mul_le_mul_of_nonneg_left (neg_abs_le (w i)) hε2
    have hneg : ε / 2 * (-|w i|) = -(ε / 2 * |w i|) := by ring
    rw [hneg] at h
    linarith
  apply add_nonneg
  · split_ifs with h
    · linarith
    · exact le_refl 0
  · split_ifs with h
    · linarith
    · exact le_refl 0

/-- The drift kernel sums to one over the unit steps. -/
theorem sum_driftFirstStep (hd : 1 ≤ d) (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ∑ e ∈ unitSteps d, driftFirstStep d ε w e = 1 := by
  rw [sum_unitSteps]
  have hpair : ∀ i : Fin d,
      driftFirstStep d ε w (unit i) + driftFirstStep d ε w (-unit i) = 1 / (d : ℝ) := by
    intro i
    rw [driftFirstStep_unit_value, driftFirstStep_neg_unit_value]
    ring
  simp_rw [hpair]
  have hdne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
  exact div_self hdne

/-- The mean of the drift kernel is `-ε w`. -/
theorem sum_driftFirstStep_smul (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ∑ e ∈ unitSteps d, driftFirstStep d ε w e • toSpace e = -(ε • w) := by
  rw [sum_unitSteps]
  have hpair : ∀ i : Fin d,
      driftFirstStep d ε w (unit i) • toSpace (unit i) +
        driftFirstStep d ε w (-unit i) • toSpace (-unit i) =
      (-ε * w i) • toSpace (unit i) := by
    intro i
    rw [driftFirstStep_unit_value, driftFirstStep_neg_unit_value, toSpace_neg, smul_neg,
        ← sub_eq_add_neg, ← sub_smul]
    congr 1
    ring
  simp_rw [hpair]
  calc ∑ i : Fin d, (-ε * w i) • toSpace (unit i)
      = ∑ i : Fin d, (-ε) • (w i • toSpace (unit i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul]
    _ = (-ε) • ∑ i : Fin d, w i • toSpace (unit i) := by rw [Finset.smul_sum]
    _ = (-ε) • w := by rw [← eq_sum_coord_smul_unit]
    _ = -(ε • w) := by rw [neg_smul]

end CERW.Support.Drift
