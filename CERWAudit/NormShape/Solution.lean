import CERWAudit.NormShape.SolutionBasic
import CERW.LimitShapes.Frozen.NormShape

/-!
# NormShape: comparator solution

The copied laws are transported field by field, and the certified theorems
supply the conclusions over the definitionally equal occupation quantities.
-/

universe u

namespace CERW.StatementAudit.NormShape

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

/-- The `norm_shape` assertion of the introduction, with all clauses. -/
theorem norm_shape {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hεΨ : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | Ψ (toSpace x) < (1 - η) * r n} ⊆ ↑(departureRange (X · ω) n) ∧
        (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | Ψ (toSpace x) < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
:= by
  exact CERW.LimitShapes.norm_shape hd (isNorm_iff.mp hΨ) hξ hξ0 hε hεΨ μ X
    (isDriftCERW_iff.mp hX)


end CERW.StatementAudit.NormShape
