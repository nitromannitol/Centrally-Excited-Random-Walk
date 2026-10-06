import CERW.Support.Lower.ExpDeviationAE
import CERW.Support.Statements

/-!
# The draft statement of the exponential deviation lemma for martingales up to time `n`

`CERW.Support.Statements.exp_deviation_upTo` is the statement of Lemma 9.1 (`lem:exp-deviation`) for
martingales with respect to a filtration of which the stages `0, …, n` are used, with the start and the
increments bounded almost surely. It is the statement of `CERW.Frozen.exp_deviation`, and
`CERW.Support.Lower.exp_deviation_upTo_holds` proves it with `exp_deviation_ae_upTo`. The lower bounds
of `Support/Lower` take it as a hypothesis, as they took `CERW.Support.Statements.exp_deviation`, and
apply it to their martingales with the martingale conditions up to time `n` read from the martingales.
-/

universe u

open MeasureTheory ProbabilityTheory

namespace CERW.Support.Statements

/-- The statement of `CERW.Frozen.exp_deviation`: Lemma 9.1 for martingales up to time `n`. -/
def exp_deviation_upTo : Prop :=
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

end CERW.Support.Statements

namespace CERW.Support.Lower

/-- `exp_deviation_upTo` is `exp_deviation_ae_upTo`. -/
theorem exp_deviation_upTo_holds : CERW.Support.Statements.exp_deviation_upTo.{u} :=
  @exp_deviation_ae_upTo

end CERW.Support.Lower
