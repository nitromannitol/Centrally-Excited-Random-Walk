module

public import CERW.Support.Outer.Radius.HigherDimensionExterior

@[expose] public section

/-!
# Higher Dimension Width

A Young inequality absorbs the fractional power appearing in the exterior estimate. The resulting
arithmetic inequality bounds the outer width.
The section label `sec:outer-high`
refers to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- Weighted Young inequality in the form used in Step 5: if `a ^ (m + 1) = Θ w ^ m`, then
`lg * a ≤ δ * w + lg ^ (m + 1) * Θ / δ ^ m` for every `δ > 0`. -/
lemma ar_young (m : ℕ) {a w lg Θ δ : ℝ} (hlg : 0 < lg) (hΘ : 0 ≤ Θ) (hw : 0 ≤ w)
    (ha0 : 0 ≤ a) (hδ : 0 < δ) (ha : a ^ (m + 1) = Θ * w ^ m) :
    lg * a ≤ δ * w + lg ^ (m + 1) * Θ / δ ^ m := by
  by_contra h
  rw [not_le] at h
  have hδw : 0 ≤ δ * w := mul_nonneg hδ.le hw
  have hT : 0 ≤ lg ^ (m + 1) * Θ / δ ^ m := by positivity
  have hlt : δ * w < lg * a := by linarith
  have hapos : 0 < a := by
    rcases ha0.lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, mul_zero] at hlt
      exact absurd hlt (not_lt.2 hδw)
  have hwle : w ≤ lg * a / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hpow : w ^ m ≤ (lg * a / δ) ^ m := pow_le_pow_left₀ hw hwle m
  have hmul : a ^ m * a ≤ a ^ m * (Θ * lg ^ m / δ ^ m) := by
    calc a ^ m * a = Θ * w ^ m := by rw [← pow_succ, ha]
      _ ≤ Θ * (lg * a / δ) ^ m := mul_le_mul_of_nonneg_left hpow hΘ
      _ = a ^ m * (Θ * lg ^ m / δ ^ m) := by rw [div_pow, mul_pow]; ring
  have hale : a ≤ Θ * lg ^ m / δ ^ m :=
    le_of_mul_le_mul_left hmul (pow_pos hapos m)
  have hfin : lg * a ≤ lg ^ (m + 1) * Θ / δ ^ m := by
    calc lg * a ≤ lg * (Θ * lg ^ m / δ ^ m) := mul_le_mul_of_nonneg_left hale hlg.le
      _ = lg ^ (m + 1) * Θ / δ ^ m := by ring
  linarith

/-- The final arithmetic of Step 5 of `sec:outer-high`. -/
theorem arith_high (hd : 3 ≤ d) (K₁ K₂ K₃ : ℝ) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hK₃ : 0 < K₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ (lg r w L Θ : ℝ), 1 ≤ lg → 0 < r → 0 ≤ w → 0 ≤ L →
      w ≤ K₁ * lg * (1 + L) →
      L ≤ K₂ * ((Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) + Θ) →
      lg ≤ Θ → Θ ≤ K₃ * (w ^ 2 / r + lg) →
      K * lg ^ d * w ≤ r → w ≤ K * lg ^ (d + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hc : 0 < K₁ * K₂ := mul_pos hK₁ hK₂
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = K₁ + K₁ * K₂ * (2 * (K₁ * K₂)) ^ m + K₁ * K₂ := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; positivity
  refine ⟨4 * A * K₃, by positivity, ?_⟩
  intro lg r w L Θ hlg hr hw hL h1 h2 h3 h4 h5
  have hlg0 : 0 < lg := by linarith
  have hΘ1 : 1 ≤ Θ := hlg.trans h3
  have hΘ0 : 0 ≤ Θ := by linarith
  have ha0 : 0 ≤ (Θ * w ^ (m + 1 - 1)) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  generalize hadef : (Θ * w ^ (m + 1 - 1)) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) = a at ha0 h2
  have ha : a ^ (m + 1) = Θ * w ^ m := by
    rw [← hadef, one_div, Real.rpow_inv_natCast_pow (by positivity) (Nat.succ_ne_zero m)]
    simp
  have hc2 : 0 < 2 * (K₁ * K₂) := by positivity
  have hy := ar_young m hlg0 hΘ0 hw ha0 (inv_pos.2 hc2) ha
  have hy2 : K₁ * K₂ * (lg * a) ≤ w / 2 + K₁ * K₂ * (2 * (K₁ * K₂)) ^ m * (lg ^ (m + 1) * Θ) := by
    calc K₁ * K₂ * (lg * a)
        ≤ K₁ * K₂ * ((2 * (K₁ * K₂))⁻¹ * w + lg ^ (m + 1) * Θ / ((2 * (K₁ * K₂))⁻¹) ^ m) :=
          mul_le_mul_of_nonneg_left hy hc.le
      _ = w / 2 + K₁ * K₂ * (2 * (K₁ * K₂)) ^ m * (lg ^ (m + 1) * Θ) := by
          rw [inv_pow, div_inv_eq_mul]
          field_simp
  have hL2 : K₁ * lg * L ≤ K₁ * K₂ * (lg * a) + K₁ * K₂ * (lg * Θ) := by
    calc K₁ * lg * L ≤ K₁ * lg * (K₂ * (a + Θ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K₁ * K₂ * (lg * a) + K₁ * K₂ * (lg * Θ) := by ring
  have hlgm : 1 ≤ lg ^ m := one_le_pow₀ hlg
  have hlgle : lg ≤ lg ^ (m + 1) := by
    calc lg = lg * 1 := (mul_one lg).symm
      _ ≤ lg * lg ^ m := mul_le_mul_of_nonneg_left hlgm hlg0.le
      _ = lg ^ (m + 1) := (pow_succ' lg m).symm
  have hP1 : lg ≤ lg ^ (m + 1) * Θ := by
    calc lg ≤ lg ^ (m + 1) := hlgle
      _ = lg ^ (m + 1) * 1 := (mul_one _).symm
      _ ≤ lg ^ (m + 1) * Θ := mul_le_mul_of_nonneg_left hΘ1 (by positivity)
  have hP2 : lg * Θ ≤ lg ^ (m + 1) * Θ := mul_le_mul_of_nonneg_right hlgle hΘ0
  have hw3 : w ≤ 2 * A * (lg ^ (m + 1) * Θ) := by
    have e1 : K₁ * lg ≤ K₁ * (lg ^ (m + 1) * Θ) := mul_le_mul_of_nonneg_left hP1 hK₁.le
    have e2 : K₁ * K₂ * (lg * Θ) ≤ K₁ * K₂ * (lg ^ (m + 1) * Θ) :=
      mul_le_mul_of_nonneg_left hP2 hc.le
    have e3 : K₁ * lg * (1 + L) = K₁ * lg + K₁ * lg * L := by ring
    have e4 : A * (lg ^ (m + 1) * Θ) = K₁ * (lg ^ (m + 1) * Θ)
        + K₁ * K₂ * (2 * (K₁ * K₂)) ^ m * (lg ^ (m + 1) * Θ)
        + K₁ * K₂ * (lg ^ (m + 1) * Θ) := by rw [hAdef]; ring
    linarith
  have hQ : lg ^ (m + 1) * (w ^ 2 / r) * (4 * A * K₃) ≤ w := by
    have e : lg ^ (m + 1) * (w ^ 2 / r) * (4 * A * K₃)
        = w * (4 * A * K₃ * lg ^ (m + 1) * w) / r := by
      field_simp
    rw [e, div_le_iff₀ hr]
    exact mul_le_mul_of_nonneg_left h5 hw
  have hw4 : w ≤ 2 * A * (lg ^ (m + 1) * (K₃ * (w ^ 2 / r + lg))) :=
    calc w ≤ 2 * A * (lg ^ (m + 1) * Θ) := hw3
      _ ≤ 2 * A * (lg ^ (m + 1) * (K₃ * (w ^ 2 / r + lg))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity))
            (by positivity)
  have e5 : 2 * A * (lg ^ (m + 1) * (K₃ * (w ^ 2 / r + lg)))
      = lg ^ (m + 1) * (w ^ 2 / r) * (4 * A * K₃) / 2 + 2 * A * K₃ * (lg ^ (m + 1) * lg) := by
    ring
  have e6 : 4 * A * K₃ * lg ^ (m + 1 + 1) = 2 * (2 * A * K₃ * (lg ^ (m + 1) * lg)) := by
    rw [pow_succ _ (m + 1)]
    ring
  rw [e5] at hw4
  rw [e6]
  linarith
/-! ### The planar exterior analysis -/

end CERW.Support.Outer.Radius
