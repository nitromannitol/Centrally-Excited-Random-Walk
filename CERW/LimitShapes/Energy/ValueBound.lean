module

public import CERW.LimitShapes.Energy.KernelEnvelope
public import CERW.LimitShapes.ShiftedSquare

@[expose] public section

/-!
# Kernel values at the dimensional centering scale

The value estimate used in `lem:contact` holds throughout radius `4n + 1`.
The extra unit includes nearest neighbors of path sites.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb

/-- The centered kernel on the contact region has logarithmic size in dimension two
and bounded size in transient dimensions, as used in `lem:contact`. -/
theorem exists_centered_kernel_value_bound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ n : ℕ, 3 ≤ n →
      ∀ x : Site d, euclidNorm x ≤ 4 * (n : ℝ) + 1 →
        |CERW.latticeKernel d x - CERW.LimitShapes.kernelShift d Ψ ε n| ≤
          G * (if d = 2 then Real.log n else 1) := by
  by_cases hd2 : d = 2
  · subst d
    obtain ⟨h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
    obtain ⟨Cb, hgrowth⟩ := hK.growth
    obtain ⟨C, hC, hshift⟩ :=
      CERW.LimitShapes.ShiftedSquare.exists_kernelShift_le_log (by omega) hΨ hε
    refine ⟨3 * |Cb| + C + 1, by linarith [abs_nonneg Cb], ?_⟩
    intro n hn x hx
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hr : 0 < euclidNorm x + 2 := by linarith [euclidNorm_nonneg x]
    have hcube : euclidNorm x + 2 ≤ (n : ℝ) ^ 3 := by
      have hs : (9 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hlogs : Real.log (euclidNorm x + 2) ≤ 3 * Real.log n := by
      calc Real.log (euclidNorm x + 2) ≤ Real.log ((n : ℝ) ^ 3) :=
            Real.log_le_log hr hcube
        _ = 3 * Real.log n := by rw [Real.log_pow]; norm_num
    have hg : |latticeKernel 2 x| ≤ 3 * |Cb| * Real.log n := by
      calc |latticeKernel 2 x| ≤ Cb * Real.log (euclidNorm x + 2) := hgrowth x
        _ ≤ |Cb| * Real.log (euclidNorm x + 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by
            linarith [euclidNorm_nonneg x]))
        _ ≤ |Cb| * (3 * Real.log n) :=
          mul_le_mul_of_nonneg_left hlogs (abs_nonneg _)
        _ = 3 * |Cb| * Real.log n := by ring
    have hs := hshift n (by omega)
    simp only [if_true]
    calc |latticeKernel 2 x - CERW.LimitShapes.kernelShift 2 Ψ ε n|
        ≤ |latticeKernel 2 x| + |CERW.LimitShapes.kernelShift 2 Ψ ε n| := abs_sub _ _
      _ ≤ (3 * |Cb| + C + 1) * Real.log n := by nlinarith
  · obtain ⟨B, hB, hb⟩ := exists_transient_kernel_bound (by omega : 3 ≤ d)
    refine ⟨B + 1, by linarith, ?_⟩
    intro n hn x hx
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast (by omega : 3 ≤ d)
    have hp : (1 + euclidNorm x) ^ (2 - (d : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [euclidNorm_nonneg x])
        (by linarith)
    rw [CERW.LimitShapes.kernelShift, if_neg hd2, sub_zero, if_neg hd2, mul_one]
    exact (hb x).trans ((mul_le_mul_of_nonneg_left hp hB.le).trans (by linarith))

end CERW.LimitShapes.Energy
