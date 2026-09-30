import CERW.Support.Main.LimitShape
import CERW.Support.Norm.LocalTime
import CERW.Generic.Norm.Subgradient

/-!
# The hypotheses of the norm statements can be met for every norm

Every norm has a subgradient at every point (Hahn–Banach), so a subgradient selection `ξ` with
`ξ 0 = 0` exists; with it, the walk exists under the ellipticity condition, and a locally finite
distributional Laplacian of the norm exists. These are the non-vacuity witnesses for the
statements about the walk with norm `Ψ` and for `lem:cell`.
-/

namespace CERW.Support.Main

open CERW LatticeProb

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Every norm has a subgradient at every point (Hahn–Banach). -/
theorem exists_subgradient (hΨ : IsNorm Ψ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ ξ : EuclideanSpace ℝ (Fin d), IsSubgradient Ψ x ξ := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, CERW.Generic.Norm.subgradient_zero hΨ⟩
  · have hnn : ∀ y, 0 ≤ Ψ y := fun y => by
      have h0 : Ψ 0 = 0 := by
        have := hΨ.smul 0 y
        simpa using this
      have h1 := hΨ.add_le y (-y)
      have h2 := hΨ.smul (-1 : ℝ) y
      simp at h2
      simp at h1
      rw [h0, h2] at h1
      linarith
    obtain ⟨g, hg1, hg2⟩ :=
      exists_extension_of_le_sublinear (LinearPMap.mkSpanSingleton x (Ψ x) hx) Ψ
      (fun c hc y => by rw [hΨ.smul, abs_of_pos hc])
      hΨ.add_le
      (fun y => by
        obtain ⟨y, hy⟩ := y
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        have h1 : (LinearPMap.mkSpanSingleton x (Ψ x) hx) ⟨c • x, hy⟩ = c * Ψ x := by
          rw [LinearPMap.mkSpanSingleton'_apply]
          simp
        rw [h1]
        show c * Ψ x ≤ Ψ (c • x)
        rw [hΨ.smul]
        exact mul_le_mul_of_nonneg_right (le_abs_self c) (hnn x))
    have hgx : g x = Ψ x := by
      have := hg1 ⟨x, Submodule.mem_span_singleton_self x⟩
      rw [show (⟨x, Submodule.mem_span_singleton_self x⟩ :
          (LinearPMap.mkSpanSingleton x (Ψ x) hx).domain)
        = ⟨(1:ℝ) • x, by simp⟩ from by simp] at this
      rw [LinearPMap.mkSpanSingleton'_apply] at this
      simpa using this
    let gc : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap g
    refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm gc, fun y => ?_⟩
    have hin : ∀ z,
        inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm gc) z = g z := by
      intro z
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    rw [hin, map_sub, hgx]
    have := hg2 y
    linarith

/-- A subgradient selection exists for every norm, with `ξ 0 = 0`. -/
theorem exists_subgradient_selection (hΨ : IsNorm Ψ) :
    ∃ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) ∧ ξ 0 = 0 := by
  classical
  refine ⟨fun x => if x = 0 then 0 else (exists_subgradient hΨ (toSpace x)).choose,
    fun x hx => ?_, by simp⟩
  simp only [hx, if_false]
  exact (exists_subgradient hΨ (toSpace x)).choose_spec


/-- Non-vacuity of the hypotheses of the norm statements, for every norm: there is a subgradient
selection with `ξ 0 = 0`, and under the ellipticity condition a realization of the walk. -/
theorem norm_hypotheses_inhabited {d : ℕ} (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) :
    ∃ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
        (_ : MeasureTheory.IsProbabilityMeasure μ) (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X := by
  obtain ⟨ξ, h1, h2⟩ := exists_subgradient_selection hΨ
  exact ⟨ξ, h1, h2, exists_norm_realization hd hΨ h1 h2 hε hell⟩

/-- Non-vacuity of the hypotheses of `lem:cell`, for every norm: a subgradient selection and a
locally finite distributional Laplacian exist. -/
theorem cell_hypotheses_inhabited {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) :
    ∃ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ m : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)),
        MeasureTheory.IsLocallyFiniteMeasure m ∧ IsDistribLaplacian Ψ m := by
  obtain ⟨ξ, h1, h2⟩ := exists_subgradient_selection hΨ
  exact ⟨ξ, h1, h2, CERW.Support.Norm.exists_isDistribLaplacian hΨ⟩

end CERW.Support.Main
