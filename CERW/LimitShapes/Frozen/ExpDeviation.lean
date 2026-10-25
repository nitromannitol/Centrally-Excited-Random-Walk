module

public import CERW.Frozen.ExpDeviation

@[expose] public section

/-!
# lem:exp-deviation

The statement at `lem:exp-deviation`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `lem:exp-deviation`, with the standing assumptions and constant scopes of
    the paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.exp_deviation :
    ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (m n : ℕ), 0 < m → 0 < n →
      ∀ b δ α : ℝ, 0 < b → 0 ≤ δ → 0 ≤ α → α ≤ 1 →
      ∀ S : Fin m → ℕ → Ω → ℝ,
        (∀ i, ∀ t ≤ n, StronglyMeasurable[ℱ t] (S i t)) →
        (∀ i, ∀ t ≤ n, Integrable (S i t) μ) →
        (∀ i, ∀ t < n, μ[S i (t + 1) | ℱ t] =ᵐ[μ] S i t) →
        (∀ i, ∀ᵐ ω ∂μ, S i 0 ω = 0) →
        (∀ i, ∀ t < n, ∀ᵐ ω ∂μ, |S i (t + 1) ω - S i t ω| ≤ b) →
      ∀ E : Set Ω, MeasurableSet E → 1 - α ≤ (μ E).toReal →
        (∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
          c₀ ≤ CERW.predBracket μ ℱ (S i) (S i) n ω ∧
            CERW.predBracket μ ℱ (S i) (S i) n ω ≤ C₀) →
      ∀ β : ℝ, C ≤ β → β * b ≤ c →
        (∀ i, Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | c * β ≤ S i n ω}).toReal ∧
          Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | S i n ω ≤ -(c * β)}).toReal) ∧
        ((∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E → |CERW.predBracket μ ℱ (S i) (S j) n ω| ≤ δ) →
          β ^ 2 * δ + β ^ 3 * b ≤ 1 →
          (μ {ω | ∀ i, S i n ω < c * β}).toReal
            ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * b
              + Real.exp (C * β ^ 2) * Real.sqrt α))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Frozen.exp_deviation
