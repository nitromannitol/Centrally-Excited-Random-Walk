import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The assembly of the lower half of the law of the iterated logarithm: the statements

The pieces of the assembly that do not depend on the padded process:

* `BlockArith`: the parameters of the blocks. For `x_k = θ^k`, the level jump `J_k`, the block
  bracket `v_k`, the block target `a_k`, the deficit `ρ_k` and the increment bound `b_k` meet the
  conditions of `CERW.Generic.Martingale.Tilt.SharpLowerTailLimit` eventually. The resulting
  lower bounds `exp (-(1 + η) a_k² / (2 v_k))` have divergent partial sums.
* `CondExpGeOfSets`: a conditional probability is at least `q` almost surely if
  `μ (F ∩ A) ≥ q μ F` for every event `F` of the sub-σ-algebra.
* `AeFstOfAeProd`: a property of the first coordinate that holds almost everywhere on a product
  with a probability measure holds almost everywhere.
* `PathCombine`: along one path, the eventual lower bound at the passage times and infinitely
  many large block increments give `S_n ≥ (1 - δ) ψ(P_n)` infinitely often, where
  `ψ(x) = √(2 x log log x)`.
-/

universe u v

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology

/-- The scale of the law of the iterated logarithm, `ψ(x) = √(2 x log log x)`. -/
noncomputable def lilScale (x : ℝ) : ℝ := Real.sqrt (2 * x * Real.log (Real.log x))

/-- The parameters of the blocks. -/
def BlockArith : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ θ η δ' : ℝ, 1 < θ ∧ 0 < η ∧ 0 < δ' ∧
    1 - δ ≤ (1 - δ / 2) * Real.sqrt (1 - 1 / θ) - (1 + δ') / Real.sqrt θ ∧
    ∀ ρ₀ ε₀ A₀ : ℝ, 0 < ρ₀ → 0 < ε₀ → ∃ ε : ℝ, 0 < ε ∧ ∃ k₀ : ℕ,
      let x : ℕ → ℝ := fun k => θ ^ k
      let J : ℕ → ℝ := fun k => max 1 (ε ^ 2 * x k / Real.log (Real.log (x k)))
      let w : ℕ → ℝ := fun k => x (k + 1) - x k + J k
      let ρ : ℕ → ℝ := fun k => (J k + J (k + 1)) / w k
      let a : ℕ → ℝ := fun k => (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (x (k + 1))
      let b : ℕ → ℝ := fun k => max 1 (ε * Real.sqrt (x (k + 1) / Real.log (Real.log (x k))))
      (∀ k, k₀ ≤ k → 0 < w k ∧ 0 < a k ∧ 0 ≤ ρ k ∧ ρ k ≤ ρ₀ ∧
        w k * (1 - ρ k) = x (k + 1) - x k - J (k + 1) ∧ A₀ * w k ≤ a k ^ 2 ∧
        a k * b k ≤ ε₀ * w k ∧ Real.exp (Real.exp 1) ≤ x k) ∧
      Tendsto (fun n => ∑ k ∈ Finset.range n,
        if k₀ ≤ k then Real.exp (-((1 + η) * (a k ^ 2 / (2 * w k)))) else 0) atTop atTop

/-- A conditional probability is bounded below by `q` almost surely if it is so on average over
every event of the sub-σ-algebra. -/
def CondExpGeOfSets : Prop :=
  ∀ {Ω : Type u} {m m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ], m ≤ m0 →
    ∀ (A : Set Ω) (q : ℝ), MeasurableSet A →
    (∀ F : Set Ω, MeasurableSet[m] F → q * (μ F).toReal ≤ (μ (F ∩ A)).toReal) →
    ∀ᵐ ω ∂μ, q ≤ (μ[A.indicator (1 : Ω → ℝ) | m]) ω

/-- A property of the first coordinate, almost everywhere on a product with a probability
measure, holds almost everywhere. -/
def AeFstOfAeProd : Prop :=
  ∀ {Ω : Type u} {Ξ : Type v} [MeasurableSpace Ω] [MeasurableSpace Ξ] (μ : Measure Ω)
    (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (p : Ω → Prop),
    (∀ᵐ z ∂(μ.prod ν), p z.1) → ∀ᵐ ω ∂μ, p ω

/-- Along one path: the eventual lower bound at the passage times `τ k` and infinitely many block
increments at least `a k` give `S_n ≥ (1 - δ) ψ(P_n)` infinitely often. -/
def PathCombine : Prop :=
  ∀ (S P : ℕ → ℝ) (τ : ℕ → ℕ) (x a : ℕ → ℝ) (θ δ δ' : ℝ), 1 < θ → 0 < δ → δ < 1 → 0 < δ' →
    1 - δ ≤ (1 - δ / 2) * Real.sqrt (1 - 1 / θ) - (1 + δ') / Real.sqrt θ →
    (∀ k, x (k + 1) = θ * x k) → Tendsto x atTop atTop → Tendsto τ atTop atTop →
    (∀ᶠ k in atTop, Real.exp (Real.exp 1) ≤ P (τ k) ∧ P (τ k) < x k) →
    (∀ᶠ k in atTop, (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (x (k + 1)) ≤ a k) →
    (∀ᶠ k in atTop, -((1 + δ') * lilScale (P (τ k))) ≤ S (τ k)) →
    (∃ᶠ k in atTop, a k ≤ S (τ (k + 1)) - S (τ k)) →
    ∃ᶠ n in atTop, (1 - δ) * lilScale (P n) ≤ S n

end CERW.Generic.Martingale.LilAssembly
