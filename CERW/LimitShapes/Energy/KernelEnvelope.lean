import CERW.Support.LocalTime.LatticeKernelFacts

/-!
# Kernel value envelopes

The asymptotics in `eq:kernel-asymptotics` give global value bounds after absorbing the
finitely many sites in a fixed ball. These retain the planar logarithmic centering.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb

/-- The planar kernel differs from the logarithm of the regularized radius by a bounded
amount, by `eq:kernel-asymptotics`. -/
theorem exists_planar_kernel_log_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ x : Site 2,
      |latticeKernel 2 x - (2 / Real.pi) * Real.log (1 + euclidNorm x)| ≤ B := by
  obtain ⟨b, hb, κ, C, R, hR, hA⟩ :=
    (External.potentialKernelAsymptotics_holds 2).1 rfl
  have heq : latticeKernel 2 = b := by
    funext x
    simpa only [latticeKernel, if_true] using (hb x).limUnder_eq
  rw [heq]
  let a : ℝ := 2 / Real.pi
  let K := ∑ z ∈ ballFinset 2 R, |b z - a * Real.log (1 + euclidNorm z)|
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨K + |C| + |κ| + 2 * a + 1, by positivity, fun x => ?_⟩
  change |b x - a * Real.log (1 + euclidNorm x)| ≤ _
  by_cases hx : euclidNorm x ≤ R
  · have hs : |b x - a * Real.log (1 + euclidNorm x)| ≤ K :=
      Finset.single_le_sum (fun z _ => abs_nonneg (b z - a *
        Real.log (1 + euclidNorm z))) (mem_ballFinset_iff.mpr hx)
    linarith [abs_nonneg C, abs_nonneg κ]
  · have hn : 1 ≤ euclidNorm x := hR.trans (le_of_not_ge hx)
    have hn0 : 0 < euclidNorm x := by linarith
    have hu0 : 0 < 1 + euclidNorm x := by linarith
    have hlog0 : 0 ≤ Real.log (1 + euclidNorm x) - Real.log (euclidNorm x) :=
      sub_nonneg.mpr (Real.log_le_log hn0 (by linarith))
    have hlog2 : Real.log (1 + euclidNorm x) - Real.log (euclidNorm x) ≤ 2 := by
      have hm := Real.log_le_log hu0 (show 1 + euclidNorm x ≤ 2 * euclidNorm x by
        linarith)
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne'] at hm
      linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)]
    have hp : euclidNorm x ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
    have hCa : C * euclidNorm x ^ (-2 : ℝ) ≤ |C| := by
      calc C * euclidNorm x ^ (-2 : ℝ)
          ≤ |C| * euclidNorm x ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hn0.le _)
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
        _ = |C| := mul_one _
    have htri : |b x - a * Real.log (1 + euclidNorm x)| ≤
        |b x - (a * Real.log (euclidNorm x) + κ)| +
          |κ - a * (Real.log (1 + euclidNorm x) - Real.log (euclidNorm x))| := by
      have he : b x - a * Real.log (1 + euclidNorm x) =
          (b x - (a * Real.log (euclidNorm x) + κ)) +
          (κ - a * (Real.log (1 + euclidNorm x) - Real.log (euclidNorm x))) := by ring
      rw [he]
      exact abs_add_le _ _
    have ht := abs_sub κ (a * (Real.log (1 + euclidNorm x) -
      Real.log (euclidNorm x)))
    rw [abs_mul, abs_of_nonneg ha, abs_of_nonneg hlog0] at ht
    have hA' := (hA x (le_of_not_ge hx)).trans hCa
    change |b x - (a * Real.log (euclidNorm x) + κ)| ≤ |C| at hA'
    nlinarith

/-- Planar centering at any positive radius retains the logarithm of the radius ratio. -/
theorem exists_planar_kernel_shift_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ R : ℝ, 0 < R → ∀ x : Site 2,
      |latticeKernel 2 x - (2 / Real.pi) * Real.log R| ≤
        B * (1 + |Real.log ((1 + euclidNorm x) / R)|) := by
  obtain ⟨B, hB, hb⟩ := exists_planar_kernel_log_bound
  let a : ℝ := 2 / Real.pi
  have ha : 0 ≤ a := by dsimp [a]; positivity
  refine ⟨B + a, by positivity, fun R hR x => ?_⟩
  have hu : (1 + euclidNorm x) ≠ 0 := ne_of_gt (by linarith [euclidNorm_nonneg x])
  have ht := abs_add_le (latticeKernel 2 x - a * Real.log (1 + euclidNorm x))
    (a * Real.log ((1 + euclidNorm x) / R))
  rw [Real.log_div hu hR.ne'] at ht ⊢
  have he : latticeKernel 2 x - a * Real.log (1 + euclidNorm x) +
      a * (Real.log (1 + euclidNorm x) - Real.log R) =
      latticeKernel 2 x - a * Real.log R := by ring
  rw [he, abs_mul, abs_of_nonneg ha] at ht
  have hh := hb x
  change |latticeKernel 2 x - a * Real.log (1 + euclidNorm x)| ≤ B at hh
  change |latticeKernel 2 x - a * Real.log R| ≤ _
  nlinarith [abs_nonneg (Real.log (1 + euclidNorm x) - Real.log R)]

/-- In transient dimensions the kernel has the global decay from `eq:kernel-asymptotics`. -/
theorem exists_transient_kernel_bound {d : ℕ} (hd : 3 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : Site d,
      |latticeKernel d x| ≤ B * (1 + euclidNorm x) ^ (2 - (d : ℝ)) := by
  obtain ⟨C, R, hR, hA⟩ := (External.potentialKernelAsymptotics_holds d).2 hd
  let p : ℝ := 2 - (d : ℝ)
  let a : ℝ := 2 / (((d : ℝ) - 2) * unitBallVolume d)
  let K := ∑ z ∈ ballFinset d R,
    |latticeKernel d z| / (1 + euclidNorm z) ^ p
  have hp : p ≤ 0 := by
    dsimp [p]
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hterm : ∀ z : Site d, 0 ≤ |latticeKernel d z| / (1 + euclidNorm z) ^ p := by
    intro z
    exact div_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _)
  have hK : 0 ≤ K := Finset.sum_nonneg fun z _ => hterm z
  have ha : 0 ≤ a := by
    dsimp [a]
    have : (0 : ℝ) < (d : ℝ) - 2 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    exact div_nonneg (by norm_num) (mul_nonneg this.le (unitBallVolume_pos d).le)
  let B := (a + |C|) * (2 : ℝ) ^ (-p)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨K + B + 1, by positivity, fun x => ?_⟩
  have hu : 0 < 1 + euclidNorm x := by linarith [euclidNorm_nonneg x]
  have hup : 0 < (1 + euclidNorm x) ^ p := Real.rpow_pos_of_pos hu _
  change |latticeKernel d x| ≤ (K + B + 1) * (1 + euclidNorm x) ^ p
  by_cases hx : euclidNorm x ≤ R
  · have hs : |latticeKernel d x| / (1 + euclidNorm x) ^ p ≤ K :=
      Finset.single_le_sum (fun z _ => hterm z) (mem_ballFinset_iff.mpr hx)
    have hs' := (div_le_iff₀ hup).mp hs
    nlinarith
  · have hn : 1 ≤ euclidNorm x := hR.trans (le_of_not_ge hx)
    have hn0 : 0 < euclidNorm x := by linarith
    have hpow : euclidNorm x ^ (-(d : ℝ)) ≤ euclidNorm x ^ p :=
      Real.rpow_le_rpow_of_exponent_le hn (by dsimp [p]; linarith)
    have hraw : srwGreenInf d x ≤ (a + |C|) * euclidNorm x ^ p := by
      have hh := (abs_le.mp (hA x (le_of_not_ge hx))).2
      change srwGreenInf d x - a * euclidNorm x ^ p ≤
        C * euclidNorm x ^ (-(d : ℝ)) at hh
      have hc : C * euclidNorm x ^ (-(d : ℝ)) ≤ |C| * euclidNorm x ^ p :=
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hn0.le _)).trans
          (mul_le_mul_of_nonneg_left hpow (abs_nonneg C))
      nlinarith
    have hcomp : euclidNorm x ^ p ≤ (2 : ℝ) ^ (-p) * (1 + euclidNorm x) ^ p := by
      have hh := Real.rpow_le_rpow_of_nonpos (show 0 < (1 + euclidNorm x) / 2 by
        positivity) (show (1 + euclidNorm x) / 2 ≤ euclidNorm x by linarith) hp
      rw [Real.div_rpow hu.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hh
      simpa only [mul_comm] using hh
    have he : |latticeKernel d x| = srwGreenInf d x := by
      rw [latticeKernel, if_neg (by omega), abs_neg,
        abs_of_nonneg (srwGreenInf_nonneg x)]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hcomp (add_nonneg ha (abs_nonneg C))
    dsimp [B]
    nlinarith

end CERW.LimitShapes.Energy
