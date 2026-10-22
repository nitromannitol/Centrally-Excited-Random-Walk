import CERWAudit.FluctuationRates.SolutionBasic
import CERW.LimitShapes.Frozen.FluctuationRates

/-!
# FluctuationRates: comparator solution

The copied laws are transported field by field, and the certified theorems
supply the conclusions over the definitionally equal occupation quantities.
-/

universe u

namespace CERW.StatementAudit.FluctuationRates

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal

/-- The copied Euclidean walk law is the repository's cylinder-factorization law. -/
theorem isCERW_iff {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {X : ℕ → Ω → Site d} : IsCERW μ ε X ↔ CERW.IsCERW μ ε X := by
  constructor <;> rintro ⟨hm, hs, hst⟩ <;> exact ⟨hm, hs, hst⟩

/-- The copied norm hypotheses are the repository's norm hypotheses. -/
theorem isNorm_iff {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} :
    IsNorm Ψ ↔ CERW.IsNorm Ψ := by
  constructor <;> rintro ⟨ha, hs, hz⟩ <;> exact ⟨ha, hs, hz⟩

/-- The copied drift walk law is the repository's cylinder-factorization law. -/
theorem isDriftCERW_iff {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {X : ℕ → Ω → Site d} :
    IsDriftCERW μ ε ξ X ↔ CERW.IsDriftCERW μ ε ξ X := by
  constructor <;> rintro ⟨hm, hs, hst⟩ <;> exact ⟨hm, hs, hst⟩

/-- The `fluctuation_rates` assertion of the introduction, with all clauses. -/
theorem fluctuation_rates {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      (if d = 2 then
          |innerRadius Y n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
            maxRadius Y n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else
          |innerRadius Y n - r n| ≤ C * Real.log n ∧
            maxRadius Y n - r n ≤ C * Real.log n ^ ((d : ℝ) + 1)) ∧
      volume (((r n)⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          ≤ ENNReal.ofReal
            (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ∧
      ∀ x : Site d,
        |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (r n * Real.log n)
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good C (X · ω) n)
:= by
  intro ωd ε hε hεd r Good p hp
  obtain ⟨C, hC, hprob, hae⟩ := CERW.LimitShapes.fluctuation_rates hd ε hε hεd p hp
  refine ⟨C, hC, ?_, ?_⟩
  · intro Ω _ μ _ X hX
    exact hprob μ X (isCERW_iff.mp hX)
  · intro Ω _ μ _ X hX
    exact hae μ X (isCERW_iff.mp hX)


end CERW.StatementAudit.FluctuationRates
