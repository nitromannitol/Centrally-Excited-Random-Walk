import CERW.LimitShapes.LocalBracket
import CERW.Generic.Lattice.Centered

/-!
# Kernel brackets before the first exit

The gradient estimate and finite lattice weight sums give the bracket estimate used in
Proposition `prop:coarse`, whenever the departure range and local times are bounded.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb

/-- The kernel bracket is controlled by the maximal local time and the lattice weight
sum, as used in Proposition `prop:coarse`. -/
theorem exists_kernel_bracket_le_localTime_log {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (X : ℕ → Site d) (n : ℕ) (y : Site d) (R L : ℝ), 1 ≤ R → 0 ≤ L →
        (∀ z ∈ CERW.departureRange X n, euclidNorm (z - y) ≤ R) →
        (∀ z ∈ CERW.departureRange X n, (CERW.localTime X n z : ℝ) ≤ L) →
        CERW.dynkinBracket (CERW.driftStepProb d ε ξ)
          (fun z => CERW.latticeKernel d (z - y))
          (fun z => CERW.latticeKernel d (z - y)) X n ≤
            C * L * (if d = 2 then Real.log (R + 2) else 1) := by
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  have hweight : ∃ A : ℝ, 0 < A ∧
      ∀ (E : Finset (Site d)) (y : Site d) (R : ℝ), 1 ≤ R →
        (∀ z ∈ E, euclidNorm (z - y) ≤ R) →
        ∑ z ∈ E, (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) ≤
          A * (if d = 2 then Real.log (R + 2) else 1) := by
    by_cases hd2 : d = 2
    · obtain ⟨A, hA, hsum⟩ :=
        CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega)
      refine ⟨A, hA, ?_⟩
      intro E y R hR hE
      have hexp : 2 - 2 * (d : ℝ) = -(d : ℝ) := by rw [hd2]; norm_num
      simpa only [hexp, if_pos hd2] using hsum E y R hR hE
    · obtain ⟨A, hA, hsum⟩ :=
        CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le (d := d) (by omega)
      refine ⟨A, hA, ?_⟩
      intro E y R _ _
      simpa only [if_neg hd2, mul_one] using hsum E y
  obtain ⟨A, hA, hsum⟩ := hweight
  refine ⟨(Cg ^ 2 + 1) * A, by positivity, ?_⟩
  intro ε hε ξ hξ X n y R L hR hL hrange htime
  have hfactor : 0 ≤ (if d = 2 then Real.log (R + 2) else 1) := by
    split_ifs
    · exact Real.log_nonneg (by linarith)
    · norm_num
  have hocc : ∑ z ∈ departureRange X n,
      (localTime X n z : ℝ) * (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) ≤
      L * (A * (if d = 2 then Real.log (R + 2) else 1)) := by
    calc
      _ ≤ ∑ z ∈ departureRange X n,
          L * (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) := by
        refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (htime z hz) ?_
        exact Real.rpow_nonneg (by linarith [euclidNorm_nonneg (z - y)]) _
      _ = L * ∑ z ∈ departureRange X n,
          (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsum _ y R hR hrange) hL
  calc
    _ ≤ Cg ^ 2 * ∑ z ∈ departureRange X n,
        (localTime X n z : ℝ) * (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) :=
      CERW.LimitShapes.dynkinBracket_translate_le (by omega) hε hξ hgrad X n y
    _ ≤ Cg ^ 2 * (L * (A * (if d = 2 then Real.log (R + 2) else 1))) :=
      mul_le_mul_of_nonneg_left hocc (sq_nonneg Cg)
    _ ≤ _ := by
      nlinarith [mul_nonneg (mul_nonneg hL hA.le) hfactor]

end CERW.LimitShapes.Exit
