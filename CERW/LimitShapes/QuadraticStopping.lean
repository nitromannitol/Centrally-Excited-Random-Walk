import CERW.LimitShapes.Event
import CERW.Support.Norm.ProjectionGeometry

/-!
# Increments of the stopped quadratic martingale

The pre-exit indicator gives the exact increment of the stopped quadratic process
in `sec:norm-event`. Cauchy–Schwarz bounds this increment using only the step
length, the drift size, and the stopping radius.
-/

namespace CERW.LimitShapes.QuadraticStopping

open CERW

/-- The stopped quadratic increment is the quadratic summand on the pre-exit event. -/
theorem stoppedQuadratic_succ_sub {d : ℕ} (ε : ℝ)
    (ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (X : ℕ → LatticeProb.Site d) (n : ℕ) :
    CERW.LimitShapes.stoppedQuadratic ε ξ R X (n + 1) -
        CERW.LimitShapes.stoppedQuadratic ε ξ R X n =
      if ∀ k ≤ n, LatticeProb.euclidNorm (X k) < R then
        2 * inner ℝ (CERW.toSpace (X n))
          (CERW.toSpace (X (n + 1)) - CERW.toSpace (X n) +
            ε • (if X n ∉ CERW.departureRange X n then ξ (X n) else 0))
      else 0 := by
  classical
  simp only [CERW.LimitShapes.stoppedQuadratic, Finset.sum_range_succ, add_sub_cancel_left]

/-- A unit step and bounded drift give a uniform bound on each stopped increment. -/
theorem abs_stoppedQuadratic_increment_le {d : ℕ} {ε R Λ : ℝ}
    (hε : 0 ≤ ε) (hR : 0 ≤ R) (hΛ : 0 ≤ Λ)
    {ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d)}
    {X : ℕ → LatticeProb.Site d} {n : ℕ}
    (hstep : ‖CERW.toSpace (X (n + 1)) - CERW.toSpace (X n)‖ ≤ 1)
    (hξ : ‖ξ (X n)‖ ≤ Λ) :
    |CERW.LimitShapes.stoppedQuadratic ε ξ R X (n + 1) -
        CERW.LimitShapes.stoppedQuadratic ε ξ R X n| ≤ 2 * R * (1 + ε * Λ) := by
  classical
  rw [stoppedQuadratic_succ_sub]
  by_cases hstay : ∀ k ≤ n, LatticeProb.euclidNorm (X k) < R
  · rw [if_pos hstay]
    have hpos : ‖toSpace (X n)‖ ≤ R := by
      rw [norm_toSpace]
      exact (hstay n le_rfl).le
    have hdrift : ‖if X n ∉ departureRange X n then ξ (X n) else 0‖ ≤ Λ := by
      by_cases hnew : X n ∉ departureRange X n
      · simpa only [if_pos hnew] using hξ
      · simpa only [if_neg hnew, norm_zero] using hΛ
    have hsum : ‖toSpace (X (n + 1)) - toSpace (X n) +
        ε • (if X n ∉ departureRange X n then ξ (X n) else 0)‖ ≤ 1 + ε * Λ := by
      calc
        _ ≤ ‖toSpace (X (n + 1)) - toSpace (X n)‖ +
            ‖ε • (if X n ∉ departureRange X n then ξ (X n) else 0)‖ := norm_add_le _ _
        _ ≤ 1 + ε * Λ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
          exact add_le_add hstep (mul_le_mul_of_nonneg_left hdrift hε)
    calc
      _ = 2 * |inner ℝ (toSpace (X n))
          (toSpace (X (n + 1)) - toSpace (X n) +
            ε • (if X n ∉ departureRange X n then ξ (X n) else 0))| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (‖toSpace (X n)‖ * ‖toSpace (X (n + 1)) - toSpace (X n) +
          ε • (if X n ∉ departureRange X n then ξ (X n) else 0)‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ 2 * (R * (1 + ε * Λ)) := by
        gcongr
      _ = 2 * R * (1 + ε * Λ) := by ring
  · rw [if_neg hstay, abs_zero]
    positivity

/-- A subgradient drift vanishing at the origin gives the norm-dependent increment bound. -/
theorem abs_stoppedQuadratic_increment_le_normMax {d : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 ≤ R)
    {ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : LatticeProb.Site d, x ≠ 0 →
      CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {X : ℕ → LatticeProb.Site d} {n : ℕ}
    (hstep : ‖CERW.toSpace (X (n + 1)) - CERW.toSpace (X n)‖ ≤ 1) :
    |CERW.LimitShapes.stoppedQuadratic ε ξ R X (n + 1) -
        CERW.LimitShapes.stoppedQuadratic ε ξ R X n| ≤
      2 * R * (1 + ε * CERW.normMax Ψ) := by
  have hΛ : 0 ≤ normMax Ψ := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨u, -, rfl⟩
    exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 u
  apply abs_stoppedQuadratic_increment_le hε hR hΛ hstep
  by_cases hx : X n = 0
  · simpa only [hx, hξ0, norm_zero] using hΛ
  · exact CERW.Support.Norm.ProjectionGeometry.norm_subgradient_le_normMax hΨ (hξ _ hx)

end CERW.LimitShapes.QuadraticStopping
