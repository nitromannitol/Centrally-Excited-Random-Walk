import CERW.Generic.Martingale.FreedmanEvent
import CERW.Model.Bracket
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Statements of the lemmas in the martingale central limit theorem

The conditional Lindeberg sum `lind` and the pathwise predictable bracket `pathBracket` of a
process, and the closed statements of the lemmas that make up the proof of the central limit
theorem for martingales by the characteristic function with an exponential compensator. Each
statement is a proposition, so that the proof of a lemma can take the lemmas it uses as explicit
hypotheses.
-/

universe u

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal

/-- The conditional Lindeberg sum `∑_{i < n} E[(M_{i+1} - M_i)² 1{|M_{i+1} - M_i| > δ} | ℱ_i]`. -/
noncomputable def lind {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (δ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,
    μ[fun ω => (M (i + 1) ω - M i ω) ^ 2 * (if δ < |M (i + 1) ω - M i ω| then 1 else 0)
      | ℱ i] ω

/-- The pathwise predictable bracket `∑_{j < k} max (E[(M_{j+1} - M_j)² | ℱ_j], 0)`, which is
nondecreasing in `k` at every point. -/
noncomputable def pathBracket {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range k, max (μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | ℱ j] ω) 0

section PathBracket

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
  (M : ℕ → Ω → ℝ)

/-- The pathwise bracket vanishes at time `0`. -/
theorem pathBracket_zero (ω : Ω) : pathBracket μ ℱ M 0 ω = 0 := by
  simp only [pathBracket, Finset.range_zero, Finset.sum_empty]

/-- The pathwise bracket is nondecreasing. -/
theorem pathBracket_mono (k : ℕ) (ω : Ω) :
    pathBracket μ ℱ M k ω ≤ pathBracket μ ℱ M (k + 1) ω := by
  simp only [pathBracket, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (le_max_right _ _)

/-- The pathwise bracket is nonnegative. -/
theorem pathBracket_nonneg (k : ℕ) (ω : Ω) : 0 ≤ pathBracket μ ℱ M k ω := by
  simp only [pathBracket]
  exact Finset.sum_nonneg fun j _ => le_max_right _ _

/-- The pathwise bracket agrees with the predictable bracket almost surely. -/
theorem pathBracket_ae_eq_predBracket (k : ℕ) :
    pathBracket μ ℱ M k =ᵐ[μ] CERW.predBracket μ ℱ M M k := by
  filter_upwards [(eventually_all_finset (Finset.range k)).mpr
    (fun j _ => condExp_nonneg (μ := μ) (m := ℱ j)
      (f := fun ω => (M (j + 1) ω - M j ω) ^ 2)
      (Eventually.of_forall fun ω => sq_nonneg _))] with ω hω
  simp only [pow_two] at hω
  simp only [pathBracket, CERW.predBracket, Finset.sum_apply, pow_two]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [max_eq_left (by simpa only [Pi.zero_apply] using hω j hj)]

end PathBracket

/-- For every real `y`, the complex exponential `e^{iy}` differs from its second-order Taylor
polynomial `1 + iy - y²/2` by at most `4 min (|y|³, y²)`. -/
abbrev CexpTaylorBoundStatement : Prop :=
  ∀ y : ℝ, ‖Complex.exp (y * Complex.I) - (1 + y * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤
    4 * min (|y| ^ 3) (y ^ 2)

/-- For every `a ≥ 0`, the quantity `e^a (1 - a) - 1` has absolute value at most `a² e^a / 2`. -/
abbrev ExpMulOneSubBoundStatement : Prop :=
  ∀ a : ℝ, 0 ≤ a → |Real.exp a * (1 - a) - 1| ≤ a ^ 2 / 2 * Real.exp a

/-- A bounded `m`-measurable complex weight `W` satisfies
`E[W f] = E[W E[f | m]]` for every integrable real `f`. -/
abbrev IntegralMulCondExpStatement : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (f : Ω → ℝ) (W : Ω → ℂ) (K : ℝ),
    m ≤ m0 → Integrable f μ → StronglyMeasurable[m] W → (∀ᵐ ω ∂μ, ‖W ω‖ ≤ K) →
    ∫ ω, W ω * (f ω : ℂ) ∂μ = ∫ ω, W ω * (μ[f | m] ω : ℂ) ∂μ

/-- For a square-integrable `X` with `E[X | m] = 0` and `E[X² | m] ≤ c`, and a bounded
`m`-measurable weight `W`, the expectation of `W (e^{itX} e^{t² E[X² | m] / 2} - 1)` is bounded
by the second moment of the conditional variance and a Lindeberg truncation at level `δ ≥ 0`. -/
abbrev CexpIncrementStepBoundStatement : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (X : Ω → ℝ) (W : Ω → ℂ) (K c : ℝ),
    m ≤ m0 → MemLp X 2 μ → μ[X | m] =ᵐ[μ] 0 → StronglyMeasurable[m] W →
    (∀ᵐ ω ∂μ, ‖W ω‖ ≤ K) → (∀ᵐ ω ∂μ, μ[fun ω => X ω ^ 2 | m] ω ≤ c) →
    ∀ t δ : ℝ, 0 ≤ δ →
    ‖∫ ω, W ω * (Complex.exp (t * X ω * Complex.I) *
        Complex.exp ((t ^ 2 * μ[fun ω => X ω ^ 2 | m] ω / 2 : ℝ)) - 1) ∂μ‖ ≤
      K * Real.exp (t ^ 2 * c / 2) * (t ^ 4 / 8 * ∫ ω, μ[fun ω => X ω ^ 2 | m] ω ^ 2 ∂μ +
        4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
          t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ))

/-- A sequence of nonnegative functions bounded by `C` that tends to `0` in measure has
integrals tending to `0`. -/
abbrev TendstoIntegralOfTendstoInMeasureBoundedStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (C : ℝ), (∀ n, AEStronglyMeasurable (f n) μ) →
    (∀ n, ∀ᵐ ω ∂μ, 0 ≤ f n ω ∧ f n ω ≤ C) →
    TendstoInMeasure μ f atTop (fun _ => 0) →
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 0)

/-- The pathwise bracket vanishes at time `0`, is nondecreasing, is `ℱ_k`-measurable at time
`k + 1`, and agrees almost surely with the predictable bracket at all times. -/
abbrev PathBracketPropertiesStatement : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ),
    (∀ ω, pathBracket μ ℱ M 0 ω = 0) ∧
    (∀ k ω, pathBracket μ ℱ M k ω ≤ pathBracket μ ℱ M (k + 1) ω) ∧
    (∀ k, StronglyMeasurable[ℱ k] (pathBracket μ ℱ M (k + 1))) ∧
    (∀ᵐ ω ∂μ, ∀ k, pathBracket μ ℱ M k ω = CERW.predBracket μ ℱ M M k ω)

/-- For a square-integrable martingale, the increment cut off where the pathwise bracket
exceeds `c` has conditional mean zero, and its conditional second moment is the indicator times
the conditional second moment of the increment. -/
abbrev TruncatedIncrementCondExpStatement : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c : ℝ), 0 ≤ c →
    Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → ∀ k,
    μ[fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω) | ℱ k]
        =ᵐ[μ] 0 ∧
    μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2 | ℱ k]
        =ᵐ[μ] fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω *
          μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω

/-- For a square-integrable martingale, the conditional second moments of the truncated
increments sum to at most `c` almost surely, and each conditional Lindeberg term of the
truncated increment is at most that of the original increment. -/
abbrev TruncatedIncrementBoundsStatement : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c : ℝ), 0 ≤ c →
    Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → (∀ ω, M 0 ω = 0) →
    ∀ (n : ℕ) (δ : ℝ),
    (∀ᵐ ω ∂μ, ∑ k ∈ Finset.range n,
        μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2
          | ℱ k] ω ≤ c) ∧
    ∀ k, μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2 *
          (if δ < |bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)|
            then 1 else 0) | ℱ k]
        ≤ᵐ[μ] μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 *
          (if δ < |M (k + 1) ω - M k ω| then 1 else 0) | ℱ k]

/-- For a square-integrable martingale, the expectation of the exponential `e^{itM'_n + t² Q_n / 2}`
built from the martingale `M'` stopped predictably where its bracket exceeds `c` and the sum
`Q_n` of its conditional variances, differs from `1` by at most an explicit bound in the
Lindeberg quantity `E[min (lind, c)]`. -/
abbrev CompensatedCexpBoundStatement : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c : ℝ), 0 ≤ c →
    Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → (∀ ω, M 0 ω = 0) →
    ∀ (n : ℕ) (t δ : ℝ), 0 ≤ δ →
    ‖∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω * Complex.I +
        (t ^ 2 / 2 * ∑ k ∈ Finset.range n,
          μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω -
            predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω : ℝ)) ∂μ - 1‖ ≤
      Real.exp (t ^ 2 * c) *
        (t ^ 4 / 8 * (c * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ)) +
          4 * (δ * |t| ^ 3 * c + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ))

/-- For a square-integrable martingale started at `0` and `v ≥ 0`, the characteristic function of
`M_n` is within an explicit error of that of the centered Gaussian of variance `v`, in terms of
the probability that the bracket deviates from `v` by more than `η` and the Lindeberg quantity
`E[min (lind, v + 1)]`. -/
abbrev CharFunMartingaleBoundStatement : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ),
    Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → (∀ ω, M 0 ω = 0) →
    ∀ v : ℝ, 0 ≤ v → ∀ (n : ℕ) (t δ η : ℝ), 0 < δ → 0 < η → η ≤ 1 →
    ‖∫ ω, Complex.exp (t * M n ω * Complex.I) ∂μ - Complex.exp (-(t ^ 2 * v / 2 : ℝ))‖ ≤
      2 * μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|} +
      Real.exp (t ^ 2 * (v + 1)) *
        (t ^ 4 / 8 * ((v + 1) * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
          4 * (δ * |t| ^ 3 * (v + 1) + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
      Real.exp (t ^ 2 * (v + 1) / 2) *
        (t ^ 2 / 2 * (η + (v + 1) * μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|}))

/-- For an array of square-integrable martingales started at `0` whose conditional Lindeberg sums
tend to `0` in measure and whose predictable brackets tend to `v` in measure, the characteristic
function of the last term of row `n` converges to that of the centered Gaussian of variance `v`. -/
abbrev ArrayCharFunTendstoStatement : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M : ℕ → ℕ → Ω → ℝ) (v : ℝ≥0),
    (∀ n, Martingale (M n) ℱ μ) → (∀ n k, MemLp (M n k) 2 μ) → (∀ n ω, M n 0 ω = 0) →
    (∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ (fun n => lind μ ℱ (M n) δ n) atTop (fun _ => 0)) →
    TendstoInMeasure μ (fun n => CERW.predBracket μ ℱ (M n) (M n) n) atTop
      (fun _ => (v : ℝ)) →
    ∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (t * M n n ω * Complex.I) ∂μ) atTop
      (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ))))

/-- If the characteristic functions of measurable real random variables converge pointwise to
that of the centered Gaussian of variance `v`, the variables converge in distribution to it. -/
abbrev TendstoInDistributionOfCharFunStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (v : ℝ≥0), (∀ n, AEMeasurable (X n) μ) →
    (∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (t * X n ω * Complex.I) ∂μ) atTop
      (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ))))) →
    TendstoInDistribution X atTop id (fun _ => μ) (gaussianReal 0 v)

end CERW.Generic.Martingale.CLT
