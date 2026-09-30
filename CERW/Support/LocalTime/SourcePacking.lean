import CERW.Support.Law.StepMean
import CERW.Generic.Lattice.Packing

/-!
# The source sum over a set of `k` sites is `O(k^{1/d})`

In the proof of `eq:interval`, the new sites of an interval enter through
`ε Σ_{x ∈ F} u_x · Db(x - y)`. By the one-step bound, `|Db(z)| ≤ √d C_g (1 + |z|)^{1-d}`. Filling
concentric shells (`eq:packing-lattice`) bounds the sum of `(1 + |x - y|)^{1-d}` over any `k` sites
by `C_d k^{1/d}`, uniformly in `y`.
-/

namespace CERW.Support.LocalTime

open LatticeProb CERW CERW.Support.Law CERW.Generic.Lattice

variable {d : ℕ}

/-- Each coordinate of the central difference is at most `C (1 + |z|)^{1-d}` once every one-step
increment is at most `Cg (1 + |z|)^{1-d}` and `Cg ≤ C`. -/
private lemma abs_centralDiff_coord_le {b : Site d → ℝ} {Cg C : ℝ} (hCgC : Cg ≤ C)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) (z : Site d) (i : Fin d) :
    ‖(centralDiff b z) i‖ ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
  have hX : 0 ≤ (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
  have h1 : |b (z + unit i) - b z| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    (hgrad z (unit i) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)).trans
      (mul_le_mul_of_nonneg_right hCgC hX)
  have h2 : |b (z - unit i) - b z| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
    have h : |b (z + -unit i) - b z| ≤ Cg * (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
      hgrad z (-unit i) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)
    rw [sub_eq_add_neg z (unit i)]
    exact h.trans (mul_le_mul_of_nonneg_right hCgC hX)
  have h2sym : |b z - b (z - unit i)| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
    rw [abs_sub_comm]
    exact h2
  have htri : |b (z + unit i) - b (z - unit i)| ≤
      2 * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
    have h := abs_sub_le (b (z + unit i)) (b z) (b (z - unit i))
    linarith
  have hcoord : (centralDiff b z) i = (b (z + unit i) - b (z - unit i)) / 2 := by
    simp only [centralDiff, PiLp.toLp_apply]
  rw [hcoord, Real.norm_eq_abs, abs_div]
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  rw [h2abs]
  linarith

/-- The Euclidean norm of the central difference is at most `√d (C (1 + |z|)^{1-d})` once every
coordinate is. -/
private lemma norm_centralDiff_le {b : Site d → ℝ} {Cg C : ℝ} (hCnonneg : 0 ≤ C)
    (hCgC : Cg ≤ C)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) (z : Site d) :
    ‖centralDiff b z‖ ≤ Real.sqrt d * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
  have hX : 0 ≤ (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
  have hc : 0 ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := mul_nonneg hCnonneg hX
  have hcoord := abs_centralDiff_coord_le hCgC hgrad z
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i : Fin d, ‖(centralDiff b z) i‖ ^ 2)
      ≤ √(∑ _i : Fin d, (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
    _ = √((d : ℝ) * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Real.sqrt d * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hc]

/-- For a kernel with the one-step bound, `|Σ_{x ∈ F} u_x · Db(x - y)| ≤ C_d |F|^{1/d}` for
every finite `F` and every `y`. -/
theorem exists_abs_sum_inner_centralDiff_le (hd : 2 ≤ d) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (F : Finset (Site d)) (y : Site d),
      |∑ x ∈ F, inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y))| ≤
        Cd * (F.card : ℝ) ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, hC₀pos, hC₀⟩ := sum_rpow_one_sub_le_card_rpow (d := d) hd1
  set Cgmax : ℝ := max Cg 0 with hCgmax
  have hCg_le : Cg ≤ Cgmax := by rw [hCgmax]; exact le_max_left _ _
  have hCgmax_nonneg : 0 ≤ Cgmax := by rw [hCgmax]; exact le_max_right _ _
  refine ⟨Real.sqrt d * Cgmax * C₀, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg d) hCgmax_nonneg) hC₀pos.le
  · intro F y
    have hterm : ∀ x ∈ F,
        |inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y))| ≤
          Real.sqrt d * Cgmax * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by
      intro x _
      have hinner : |inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y))| ≤
          ‖centralDiff b (x - y)‖ := by
        calc |inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y))|
            ≤ ‖unitDir (toSpace x)‖ * ‖centralDiff b (x - y)‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * ‖centralDiff b (x - y)‖ :=
              mul_le_mul_of_nonneg_right (norm_unitDir_le _) (norm_nonneg _)
          _ = ‖centralDiff b (x - y)‖ := one_mul _
      have hnorm := norm_centralDiff_le hCgmax_nonneg hCg_le hgrad (x - y)
      calc |inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y))|
          ≤ ‖centralDiff b (x - y)‖ := hinner
        _ ≤ Real.sqrt d * (Cgmax * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ))) := hnorm
        _ = Real.sqrt d * Cgmax * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by ring
    calc |∑ x ∈ F, inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y))|
        ≤ ∑ x ∈ F, |inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ F, Real.sqrt d * Cgmax * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = Real.sqrt d * Cgmax * ∑ x ∈ F, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ Real.sqrt d * Cgmax * (C₀ * (F.card : ℝ) ^ ((1 : ℝ) / d)) :=
          mul_le_mul_of_nonneg_left (hC₀ F y)
            (mul_nonneg (Real.sqrt_nonneg d) hCgmax_nonneg)
      _ = Real.sqrt d * Cgmax * C₀ * (F.card : ℝ) ^ ((1 : ℝ) / d) := by ring

end CERW.Support.LocalTime
