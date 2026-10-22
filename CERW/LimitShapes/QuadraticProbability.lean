import CERW.LimitShapes.StoppedQuadraticMartingale
import CERW.LimitShapes.QuadraticStopping
import CERW.Generic.Martingale.Clamp

/-!
# Fixed-radius tails for the stopped quadratic process

The actual stopped process of Section `sec:norm-event` has almost surely bounded increments.
Normalization and the martingale clamp give a bounded representative to which the existing
logarithmic martingale estimate applies. Its tail transfers to the unchanged stopped sum.
-/

universe u

open MeasureTheory Filter LatticeProb

namespace CERW.LimitShapes.QuadraticProbability

open CERW CERW.Support.Law CERW.Support.Drift
open private exists_interval_bound_log from CERW.Support.Norm.VectorBound

/-- The stopped quadratic process has a polynomial tail with constants independent
of the field, probability law, stopping radius and terminal horizon. -/
theorem exists_stopped_quadratic_tail
    {d : ℕ} (hd : 1 ≤ d) {ε Λ : ℝ} (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ)
    (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d),
        (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) → ξ 0 = 0 →
        (∀ z, ‖ξ z‖ ≤ Λ) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (X : ℕ → Ω → LatticeProb.Site d),
        CERW.IsDriftCERW μ ε ξ X → ∀ R : ℝ, 0 < R → ∀ n : ℕ, 2 ≤ n →
        μ {ω | C * R * Real.sqrt (n * Real.log n) <
            |CERW.LimitShapes.stoppedQuadratic ε ξ R (X · ω) n|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨c, hc, htail⟩ := exists_interval_bound_log (K := p + 1) (by linarith)
  let B := 2 * (1 + ε * Λ)
  have hB : 0 < B := by dsimp [B]; positivity
  let C := c * B + 4
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hξ0 hnorm Ω _ μ _ X hX R hR n hn
  let b := B * R
  have hb : 0 < b := mul_pos hB hR
  let Z : ℕ → Ω → ℝ := fun j ω => stoppedQuadratic ε ξ R (X · ω) j / b
  have hZ : Martingale Z (pathFiltration hX.measurable) μ := by
    have h := (StoppedQuadraticMartingale.martingale_stoppedQuadratic
      hd hε hξ hξ0 R hX).smul b⁻¹
    convert h using 1
    funext j ω
    change stoppedQuadratic ε ξ R (X · ω) j / b =
      b⁻¹ * stoppedQuadratic ε ξ R (X · ω) j
    ring
  have hinc : ∀ j, ∀ᵐ ω ∂μ, |Z (j + 1) ω - Z j ω| ≤ 1 := by
    intro j
    filter_upwards [ae_sub_mem_unitSteps_drift hd hε hξ hX j] with ω hstep
    have hunit : ‖toSpace (X (j + 1) ω) - toSpace (X j ω)‖ ≤ 1 := by
      have heq := CERW.Support.Occupation.toSpace_sub (X (j + 1) ω) (X j ω)
      rw [← heq, norm_toSpace]
      exact (euclidNorm_of_mem_unitSteps hstep).le
    have hbound := QuadraticStopping.abs_stoppedQuadratic_increment_le
      (X := (X · ω)) (n := j) (ξ := ξ) hε hR.le hΛ hunit (hnorm (X j ω))
    have hbound' : |stoppedQuadratic ε ξ R (X · ω) (j + 1) -
        stoppedQuadratic ε ξ R (X · ω) j| ≤ b := by
      calc
        _ ≤ 2 * R * (1 + ε * Λ) := hbound
        _ = b := by dsimp [b, B]; ring
    dsimp [Z]
    rw [← sub_div, abs_div, abs_of_pos hb, div_le_one hb]
    exact hbound'
  obtain ⟨M, hM, hMb, hM0, hae⟩ :=
    CERW.Generic.Martingale.exists_martingale_clamp hZ (by norm_num : (0 : ℝ) ≤ 1) hinc
  have hzero (ω : Ω) : M 0 ω = 0 := by
    rw [hM0]
    simp only [Z, stoppedQuadratic, Finset.range_zero, Finset.sum_empty, zero_div]
  have hvar : ∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 |
      pathFiltration hX.measurable j] ≤ᵐ[μ] fun _ => 1 := by
    intro j
    have hsq (ω : Ω) : (M (j + 1) ω - M j ω) ^ 2 ≤ 1 := by
      calc
        _ = |M (j + 1) ω - M j ω| ^ 2 := (sq_abs _).symm
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMb j ω) 2
        _ = 1 := one_pow 2
    have hint : Integrable (fun ω => (M (j + 1) ω - M j ω) ^ 2) μ := by
      apply Integrable.of_bound (C := 1)
      · have hmeas := (((hM.stronglyMeasurable (j + 1)).mono
          ((pathFiltration hX.measurable).le (j + 1))).sub
          ((hM.stronglyMeasurable j).mono ((pathFiltration hX.measurable).le j))).measurable
        exact (hmeas.pow_const 2).aestronglyMeasurable
      · exact Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hsq ω
    have hmono := condExp_mono (m := pathFiltration hX.measurable j)
      hint (integrable_const (1 : ℝ)) (Eventually.of_forall hsq)
    simpa only [condExp_const ((pathFiltration hX.measurable).le j)] using hmono
  have hprob := htail hM (fun j ω => (hMb j ω).trans (by norm_num)) hvar n hn 0 n
    (by omega) le_rfl
  simp only [Nat.cast_zero, sub_zero] at hprob
  have hsub : {ω | C * R * Real.sqrt (n * Real.log n) <
      |stoppedQuadratic ε ξ R (X · ω) n|} ≤ᵐ[μ]
      {ω | c * Real.sqrt ((n : ℝ) * Real.log n) < |M n ω - M 0 ω|} := by
    filter_upwards [hae] with ω heq hbad
    change c * Real.sqrt ((n : ℝ) * Real.log n) < |M n ω - M 0 ω|
    simp only [hzero, sub_zero, heq n, Z]
    rw [abs_div, abs_of_pos hb, lt_div_iff₀ hb]
    have hscale : c * Real.sqrt (n * Real.log n) * b ≤
        C * R * Real.sqrt (n * Real.log n) := by
      calc
        _ = (c * B) * R * Real.sqrt (n * Real.log n) := by dsimp [b]; ring
        _ ≤ C * R * Real.sqrt (n * Real.log n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hR.le)
            (Real.sqrt_nonneg _)
    exact hscale.trans_lt hbad
  refine (measure_mono_ae hsub).trans (hprob.trans (ENNReal.ofReal_le_ofReal ?_))
  have hpow := CERW.Generic.Martingale.pow_mul_rpow_neg_le
    (by omega : 1 ≤ n) 1 p
  have hpoly : ((n : ℝ) + 1) * (2 * (n : ℝ) ^ (-(p + 1))) ≤
      4 * (n : ℝ) ^ (-p) := by
    have h := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2)
    norm_num only [pow_one, Nat.cast_one] at h
    nlinarith
  exact hpoly.trans (mul_le_mul_of_nonneg_right
    (by dsimp [C]; linarith [mul_pos hc hB] : (4 : ℝ) ≤ C) (by positivity))

end CERW.LimitShapes.QuadraticProbability
