import CERW.LimitShapes.LocalBracket
import CERW.Generic.Lattice.Centered
import CERW.Support.Norm.LocalTime

/-!
# Final-time occupation weights

The bracket weights in Lemma `lem:local` sum logarithmically in dimension two
and uniformly in higher dimensions.
-/

open LatticeProb CERW Finset

namespace CERW.LimitShapes.LocalApproximationProof

open private euclidNorm_sub_le_add from CERW.Support.Norm.LocalTime

/-- The unweighted bracket sum over visited sites has the dimensional bound. -/
theorem exists_weight_sum_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (x : ℕ → Site d) (n : ℕ), 1 ≤ n → (∀ j, euclidNorm (x j) ≤ j) →
      ∀ y : Site d, euclidNorm y ≤ 3 * n →
        ∑ z ∈ departureRange x n, (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) ≤
          D * (if d = 2 then Real.log (n + 2) else 1) := by
  by_cases h2 : d = 2
  · obtain ⟨C, hC0, hC⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega)
    refine ⟨2 * C, by positivity, ?_⟩
    intro x n hn hx y hy
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hR : ∀ z ∈ departureRange x n, euclidNorm (z - y) ≤ 4 * n := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast (mem_range.mp hj).le
      linarith [euclidNorm_sub_le_add (x j) y, hx j]
    have hexp : (2 - 2 * (d : ℝ)) = -(d : ℝ) := by subst h2; norm_num
    simp only [hexp]
    have h1 := hC (departureRange x n) y (4 * n) (by linarith) hR
    have h3 : Real.log (4 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) := by
      have h4 := Real.log_le_log (by linarith : (0 : ℝ) < 4 * n + 2)
        (by nlinarith : 4 * (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2)
      rw [Real.log_pow] at h4
      simpa using h4
    rw [if_pos h2]
    calc _ ≤ C * Real.log (4 * (n : ℝ) + 2) := h1
      _ ≤ C * (2 * Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_left h3 hC0.le
      _ = 2 * C * Real.log ((n : ℝ) + 2) := by ring
  · obtain ⟨C, hC0, hC⟩ :=
      CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le (d := d) (by omega)
    refine ⟨C, hC0, ?_⟩
    intro x n _ _ y _
    rw [if_neg h2, mul_one]
    exact hC _ y

/-- The actual predictable bracket is bounded by maximum local time and the lattice sum. -/
theorem exists_bracket_max_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      0 ≤ ε → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → (∀ j, euclidNorm (X j) ≤ j) →
      ∀ y : Site d, euclidNorm y ≤ 3 * n →
        dynkinBracket (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y))
          (fun z => latticeKernel d (z - y)) X n ≤
          B * (maxLocalTime X n : ℝ) * (if d = 2 then Real.log n else 1) := by
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨D, hD, hsum⟩ := exists_weight_sum_bound hd
  refine ⟨2 * (Cg ^ 2 * D), by positivity, ?_⟩
  intro ε ξ hε hξ X n hn hx y hy
  have hw := hsum X n (by omega) hx y hy
  have hbr := dynkinBracket_translate_le (by omega : 1 ≤ d) hε hξ hgrad X n y
  have hocc : ∑ z ∈ departureRange X n,
      (localTime X n z : ℝ) * (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) ≤
      (maxLocalTime X n : ℝ) * ∑ z ∈ departureRange X n,
        (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (CERW.localTime_le_maxLocalTime X n z))
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (z - y)]) _)
  have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    calc _ ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hdim : (if d = 2 then Real.log ((n : ℝ) + 2) else 1) ≤
      2 * (if d = 2 then Real.log n else 1) := by
    split_ifs
    · exact hlog
    · norm_num
  calc _ ≤ Cg ^ 2 * ((maxLocalTime X n : ℝ) *
        ∑ z ∈ departureRange X n,
          (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ))) :=
        hbr.trans (mul_le_mul_of_nonneg_left hocc (sq_nonneg Cg))
    _ ≤ Cg ^ 2 * ((maxLocalTime X n : ℝ) *
        (D * (2 * (if d = 2 then Real.log n else 1)))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg Cg)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact hw.trans (mul_le_mul_of_nonneg_left hdim hD.le)
    _ = _ := by ring

end CERW.LimitShapes.LocalApproximationProof
