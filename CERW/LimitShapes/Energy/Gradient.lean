module

public import CERW.LimitShapes.Energy.KernelEnvelope
public import CERW.Support.Occupation.SiteArith

@[expose] public section

/-!
# Pointwise drift envelope of the shifted-square kernel

The value asymptotics and the gradient bound give the pointwise central-difference
estimate used in Lemma `lem:contact`. Planar centering preserves the logarithm of the
ratio of the spatial and centering radii.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb

/-- A local increment estimate controls the norm of the central difference. -/
lemma norm_centralDiff_le_of_local_steps {d : ℕ} {f : Site d → ℝ}
    {x : Site d} {M : ℝ} (hstep : ∀ e ∈ unitSteps d, |f (x + e) - f x| ≤ M) :
    ‖CERW.Support.Law.centralDiff f x‖ ≤ (d : ℝ) * M := by
  have hc : ∀ i : Fin d, |(CERW.Support.Law.centralDiff f x) i| ≤ M := by
    intro i
    have hp := hstep (unit i) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)
    have hn := hstep (-unit i) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)
    rw [← sub_eq_add_neg] at hn
    have ht : |f (x + unit i) - f (x - unit i)| ≤ 2 * M := by
      calc |f (x + unit i) - f (x - unit i)|
          = |(f (x + unit i) - f x) + (f x - f (x - unit i))| := by
            congr 1
            ring
        _ ≤ |f (x + unit i) - f x| + |f x - f (x - unit i)| := abs_add_le _ _
        _ ≤ M + M := by rw [abs_sub_comm (f x)]; exact add_le_add hp hn
        _ = 2 * M := by ring
    change |(f (x + unit i) - f (x - unit i)) / 2| ≤ M
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  calc ‖CERW.Support.Law.centralDiff f x‖
      ≤ ∑ i : Fin d, |(CERW.Support.Law.centralDiff f x) i| :=
        CERW.Support.Occupation.norm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hc i
    _ = (d : ℝ) * M := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]

/-- Factoring a difference of squares uses only a value and an increment at the base site. -/
lemma square_sub_step_le_of_local_bounds {d : ℕ} {b : Site d → ℝ}
    {x e : Site d} {γ A B : ℝ} (hA : 0 ≤ A)
    (hb : |b x - γ| ≤ B) (hg : |b (x + e) - b x| ≤ A) :
    |(b (x + e) - γ) ^ 2 - (b x - γ) ^ 2| ≤ A * (2 * B + A) := by
  have hs : |2 * (b x - γ) + (b (x + e) - b x)| ≤ 2 * B + A := by
    calc |2 * (b x - γ) + (b (x + e) - b x)|
        ≤ |2 * (b x - γ)| + |b (x + e) - b x| := abs_add_le _ _
      _ = 2 * |b x - γ| + |b (x + e) - b x| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * B + A := by linarith
  have he : (b (x + e) - γ) ^ 2 - (b x - γ) ^ 2 =
      (b (x + e) - b x) * (2 * (b x - γ) + (b (x + e) - b x)) := by ring
  rw [he, abs_mul]
  exact mul_le_mul hg hs (abs_nonneg _) hA

/-- The shifted-square kernel has the pointwise central-difference envelope of
Lemma `lem:contact`, using `eq:kernel-asymptotics` and `eq:gradient`. -/
theorem exists_shifted_square_centralDiff_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ x : Site d,
      ‖CERW.Support.Law.centralDiff
        (fun z => (CERW.latticeKernel d z -
          (if d = 2 then (2 / Real.pi) * Real.log R else 0)) ^ 2) x‖ ≤
        C * (if d = 2 then
          (1 + euclidNorm x)⁻¹ *
            (1 + |Real.log ((1 + euclidNorm x) / R)|)
          else (1 + euclidNorm x) ^ ((3 : ℝ) - 2 * d)) := by
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hg⟩ := hK.gradBound
  let G := max Cg 0 + 1
  have hG : 0 < G := by dsimp [G]; positivity
  have hg' : ∀ x e : Site d, e ∈ unitSteps d →
      |latticeKernel d (x + e) - latticeKernel d x| ≤
        G * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
    intro x e he
    refine (hg x e he).trans (mul_le_mul_of_nonneg_right ?_
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _))
    dsimp [G]
    linarith [le_max_left Cg 0]
  by_cases hd2 : d = 2
  · subst d
    obtain ⟨B, hB, hb⟩ := exists_planar_kernel_shift_bound
    let D := G * (2 * B + G)
    have hD : 0 < D := by dsimp [D]; positivity
    refine ⟨2 * D, by positivity, fun R hR x => ?_⟩
    simp only [if_true]
    let u := 1 + euclidNorm x
    let L := 1 + |Real.log (u / R)|
    have hu : 1 ≤ u := by dsimp [u]; linarith [euclidNorm_nonneg x]
    have hu0 : 0 < u := by linarith
    have hL : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg (Real.log (u / R))]
    have hi : u⁻¹ ≤ 1 := (inv_le_one₀ hu0).mpr hu
    have hsteps : ∀ e ∈ unitSteps 2,
        |(latticeKernel 2 (x + e) - (2 / Real.pi) * Real.log R) ^ 2 -
          (latticeKernel 2 x - (2 / Real.pi) * Real.log R) ^ 2| ≤ D * (u⁻¹ * L) := by
      intro e he
      have hgrad : |latticeKernel 2 (x + e) - latticeKernel 2 x| ≤ G * u⁻¹ := by
        simpa only [Nat.cast_ofNat, show (1 : ℝ) - 2 = -1 by norm_num,
          Real.rpow_neg_one] using hg' x e he
      have hv : |latticeKernel 2 x - (2 / Real.pi) * Real.log R| ≤ B * L :=
        hb R (by linarith) x
      have hs := square_sub_step_le_of_local_bounds
        (show 0 ≤ G * u⁻¹ by positivity) hv hgrad
      have hiL : G * u⁻¹ ≤ G * L :=
        mul_le_mul_of_nonneg_left (hi.trans hL) hG.le
      calc _ ≤ (G * u⁻¹) * (2 * (B * L) + G * u⁻¹) := hs
        _ ≤ (G * u⁻¹) * (2 * (B * L) + G * L) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = D * (u⁻¹ * L) := by dsimp [D]; ring
    have hn := norm_centralDiff_le_of_local_steps
      (f := fun z => (latticeKernel 2 z - (2 / Real.pi) * Real.log R) ^ 2)
      (x := x) hsteps
    simpa only [Nat.cast_ofNat, mul_assoc] using hn
  · obtain ⟨B, hB, hb⟩ := exists_transient_kernel_bound (by omega : 3 ≤ d)
    let D := G * (2 * B + G)
    have hD : 0 < D := by dsimp [D]; positivity
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    refine ⟨(d : ℝ) * D, by positivity, fun R _hR x => ?_⟩
    simp only [if_neg hd2, sub_zero]
    let u := 1 + euclidNorm x
    let p : ℝ := 2 - (d : ℝ)
    let q : ℝ := 1 - (d : ℝ)
    have hu : 1 ≤ u := by dsimp [u]; linarith [euclidNorm_nonneg x]
    have hu0 : 0 < u := by linarith
    have hq : 0 ≤ u ^ q := Real.rpow_nonneg hu0.le _
    have hqp : u ^ q ≤ u ^ p := Real.rpow_le_rpow_of_exponent_le hu (by
      dsimp [p, q]; linarith)
    have hsteps : ∀ e ∈ unitSteps d,
        |latticeKernel d (x + e) ^ 2 - latticeKernel d x ^ 2| ≤
          D * u ^ ((3 : ℝ) - 2 * d) := by
      intro e he
      have hs := square_sub_step_le_of_local_bounds
        (mul_nonneg hG.le hq)
        (show |latticeKernel d x - 0| ≤ B * u ^ p by simpa only [sub_zero] using hb x)
        (hg' x e he)
      simp only [sub_zero] at hs
      calc _ ≤ (G * u ^ q) * (2 * (B * u ^ p) + G * u ^ q) := hs
        _ ≤ (G * u ^ q) * (2 * (B * u ^ p) + G * u ^ p) :=
          mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left hqp hG.le))
            (mul_nonneg hG.le hq)
        _ = D * (u ^ q * u ^ p) := by dsimp [D]; ring
        _ = D * u ^ ((3 : ℝ) - 2 * d) := by
          rw [← Real.rpow_add hu0]
          congr 2
          dsimp [p, q]
          ring
    have hn := norm_centralDiff_le_of_local_steps
      (f := fun z => latticeKernel d z ^ 2) (x := x) hsteps
    simpa only [mul_assoc] using hn

end CERW.LimitShapes.Energy
