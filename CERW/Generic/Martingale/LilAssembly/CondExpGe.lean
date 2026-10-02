import CERW.Generic.Martingale.LilAssembly.Statements

/-!
# A conditional probability bounded below on average

If `μ (F ∩ A) ≥ q μ F` for every event `F` of the sub-σ-algebra `m`, then `μ[1_A | m] ≥ q`
almost surely: the event `{μ[1_A | m] < q}` is itself in `m`.
-/

universe u v

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology

/-- A conditional probability bounded below on every event of the sub-σ-algebra. -/
theorem condExp_ge_of_sets : CondExpGeOfSets.{u} := by
  intro Ω m m0 μ _ hm A q hA h
  have hind : Integrable (A.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have hgi : Integrable (μ[A.indicator (1 : Ω → ℝ) | m]) μ := integrable_condExp
  have hgm : StronglyMeasurable[m] (μ[A.indicator (1 : Ω → ℝ) | m]) := stronglyMeasurable_condExp
  have hF : MeasurableSet[m] {ω | (μ[A.indicator (1 : Ω → ℝ) | m]) ω < q} :=
    measurableSet_lt hgm.measurable measurable_const
  by_contra hne
  set g := μ[A.indicator (1 : Ω → ℝ) | m] with hg
  set F : Set Ω := {ω | g ω < q} with hFdef
  have hFm0 : MeasurableSet F := hm _ hF
  have hFpos : μ F ≠ 0 := by
    intro h0
    apply hne
    rw [ae_iff]
    simpa [hFdef, not_le] using h0
  have hint : ∫ ω in F, g ω ∂μ = (μ (F ∩ A)).toReal := by
    rw [hg, setIntegral_condExp hm hind hF, setIntegral_indicator hA]
    simp [Measure.real]
  have hfint : IntegrableOn (fun ω => q - g ω) F μ :=
    ((integrable_const q).sub hgi).integrableOn
  have hle : ∫ ω in F, (q - g ω) ∂μ ≤ 0 := by
    rw [integral_sub (integrable_const q).integrableOn hgi.integrableOn, hint, setIntegral_const]
    simp only [Measure.real, smul_eq_mul]
    linarith [h F hF]
  have hpos : 0 < ∫ ω in F, (q - g ω) ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hfint]
    · have hsub : F ⊆ Function.support (fun ω => q - g ω) ∩ F := fun ω hω =>
        ⟨sub_ne_zero.2 (ne_of_gt hω), hω⟩
      exact lt_of_lt_of_le (pos_iff_ne_zero.2 hFpos) (measure_mono hsub)
    · exact (ae_restrict_iff' hFm0).2 (Filter.Eventually.of_forall fun ω hω =>
        sub_nonneg.2 (le_of_lt hω))
  exact absurd hpos (not_lt.2 hle)

end CERW.Generic.Martingale.LilAssembly
