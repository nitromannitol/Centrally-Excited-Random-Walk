module

public import CERW.LimitShapes.Event

@[expose] public section

/-!
# The predictable bracket and the kernel weight

The gradient bound for the lattice kernel controls its actual predictable bracket
by the occupation-weighted sum used in the convolution proof.
-/

open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes

open CERW

/-- The bracket of a translated test function is bounded by the weighted local times. -/
theorem dynkinBracket_translate_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e : Site d, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (X : ℕ → Site d) (n : ℕ) (y : Site d) :
    dynkinBracket (driftStepProb d ε ξ) (fun z => b (z - y)) (fun z => b (z - y)) X n ≤
      Cg ^ 2 * ∑ z ∈ departureRange X n,
        (localTime X n z : ℝ) * (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) := by
  have hCg : 0 ≤ Cg := CERW.Support.Law.cg_nonneg hd hgrad
  rw [← CERW.Support.LocalTime.sum_range_eq_sum_localTime X n
    (fun z => (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ))), Finset.mul_sum]
  unfold dynkinBracket
  refine Finset.sum_le_sum fun j _ => ?_
  have hbase : 0 ≤ 1 + euclidNorm (X j - y) := by
    linarith [LatticeProb.euclidNorm_nonneg (X j - y)]
  have hpow : ((1 + euclidNorm (X j - y)) ^ (1 - (d : ℝ))) ^ 2 =
      (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    congr 1
    push_cast
    ring
  have hsum : ∑ e ∈ unitSteps d, driftStepProb d ε ξ X j e *
        (b (X j + e - y) - b (X j - y)) ^ 2 ≤
      (Cg * (1 + euclidNorm (X j - y)) ^ (1 - (d : ℝ))) ^ 2 := by
    calc
      _ ≤ ∑ e ∈ unitSteps d, driftStepProb d ε ξ X j e *
          (Cg * (1 + euclidNorm (X j - y)) ^ (1 - (d : ℝ))) ^ 2 := by
        refine Finset.sum_le_sum fun e he => ?_
        apply mul_le_mul_of_nonneg_left _
          (CERW.Support.Drift.driftStepProb_nonneg hε hξ X j e)
        rw [add_sub_right_comm, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hgrad (X j - y) e he) 2
      _ = _ := by
        rw [← Finset.sum_mul, CERW.Support.Drift.sum_driftStepProb hd ε ξ X j, one_mul]
  rw [mul_pow, hpow] at hsum
  dsimp only
  simp only [← pow_two]
  nlinarith [sq_nonneg (stepMean (driftStepProb d ε ξ) (fun z => b (z - y)) X j)]

/-- A local Freedman estimate with the actual bracket implies the occupation-weighted
martingale estimate, uniformly in the field of subgradients. -/
theorem localMartingaleBound_to_weight {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → LocalMartingaleBound ε ξ C X n →
        CERW.Support.Norm.ContactEvent.LocalMartEstimate d ε ξ Cw X n := by
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  have hCg := CERW.Support.Law.cg_nonneg (by omega : 1 ≤ d) hgrad
  refine ⟨C * (Cg + 1), by positivity, ?_⟩
  intro ξ hξ hξ0 X n hn h y hy
  have hξ' := CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
  have hbr := dynkinBracket_translate_le (by omega : 1 ≤ d) hε.le hξ' hgrad X n y
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hW : 0 ≤ ∑ z ∈ departureRange X n,
      (localTime X n z : ℝ) * (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) :=
    Finset.sum_nonneg fun z _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (z - y)]) _)
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hbr hlog)
  rw [mul_assoc, Real.sqrt_mul (sq_nonneg Cg), Real.sqrt_sq hCg] at hsq
  have hmain := (h y hy).trans (mul_le_mul_of_nonneg_left (add_le_add hsq le_rfl) hC)
  calc _ ≤ C * (Cg * Real.sqrt ((∑ z ∈ departureRange X n,
          (localTime X n z : ℝ) * (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ))) *
            Real.log n) + Real.log n) := hmain
    _ ≤ _ := by
      rw [mul_assoc C (Cg + 1)]
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith [mul_nonneg hCg hlog, Real.sqrt_nonneg ((∑ z ∈ departureRange X n,
        (localTime X n z : ℝ) * (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n)]

end CERW.LimitShapes
