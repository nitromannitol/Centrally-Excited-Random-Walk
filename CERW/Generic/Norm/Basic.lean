import CERW.Model.Norm

/-!
# Elementary facts about a norm on `ℝ^d`

A function with `IsNorm Ψ` vanishes at the origin, is nonnegative and even, satisfies the reverse
triangle inequality, and is bounded by `Σ_i |x_i| Ψ(e_i)`.
-/

namespace CERW.Generic.Norm

open CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A norm vanishes at the origin, is nonnegative, and is even. -/
theorem map_zero_nonneg_neg (hΨ : IsNorm Ψ) :
    Ψ 0 = 0 ∧ (∀ x, 0 ≤ Ψ x) ∧ ∀ x, Ψ (-x) = Ψ x := by
  have hzero : Ψ 0 = 0 := by
    simpa using hΨ.smul 0 0
  have hneg : ∀ x, Ψ (-x) = Ψ x := by
    intro x
    simpa using hΨ.smul (-1) x
  refine ⟨hzero, fun x => ?_, hneg⟩
  have h := hΨ.add_le x (-x)
  rw [add_neg_cancel, hzero, hneg x] at h
  linarith

/-- The reverse triangle inequality `|Ψ x - Ψ y| ≤ Ψ (x - y)`. -/
theorem abs_sub_le (hΨ : IsNorm Ψ) (x y : EuclideanSpace ℝ (Fin d)) :
    |Ψ x - Ψ y| ≤ Ψ (x - y) := by
  have hxy : Ψ (y - x) = Ψ (x - y) := by
    simpa [neg_sub] using (map_zero_nonneg_neg hΨ).2.2 (x - y)
  have h₁ : Ψ x - Ψ y ≤ Ψ (x - y) := by
    have h := hΨ.add_le (x - y) y
    rw [sub_add_cancel] at h
    linarith
  have h₂ : Ψ y - Ψ x ≤ Ψ (x - y) := by
    have h := hΨ.add_le (y - x) x
    rw [sub_add_cancel, hxy] at h
    linarith
  rw [abs_sub_le_iff]
  exact ⟨h₁, h₂⟩

/-- Subadditivity and homogeneity bound `Ψ` of a finite combination of coordinate vectors by the
weighted sum of `Ψ (coordVec i)`. -/
private theorem sum_smul_coordVec_le (hΨ : IsNorm Ψ) (c : Fin d → ℝ) :
    ∀ s : Finset (Fin d),
      Ψ (∑ i ∈ s, c i • coordVec i) ≤ ∑ i ∈ s, |c i| * Ψ (coordVec i) := by
  intro s
  refine Finset.induction_on s ?base ?step
  · simp [(map_zero_nonneg_neg hΨ).1]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc Ψ (c a • coordVec a + ∑ i ∈ s, c i • coordVec i)
        ≤ Ψ (c a • coordVec a) + Ψ (∑ i ∈ s, c i • coordVec i) := hΨ.add_le _ _
      _ ≤ |c a| * Ψ (coordVec a) + ∑ i ∈ s, |c i| * Ψ (coordVec i) :=
            add_le_add (le_of_eq (hΨ.smul (c a) (coordVec a))) ih

/-- A norm is bounded by the coordinates: `Ψ x ≤ Σ_i |x_i| Ψ(e_i)`. -/
theorem le_sum_coord (hΨ : IsNorm Ψ) (x : EuclideanSpace ℝ (Fin d)) :
    Ψ x ≤ ∑ i, |x i| * Ψ (coordVec i) := by
  have hx : ∑ i, x i • coordVec i = x := by
    simpa [coordVec] using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  calc Ψ x = Ψ (∑ i, x i • coordVec i) := by rw [hx]
    _ ≤ ∑ i, |x i| * Ψ (coordVec i) := sum_smul_coordVec_le hΨ x Finset.univ

end CERW.Generic.Norm
