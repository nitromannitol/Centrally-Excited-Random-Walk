import CERW.Model.DriftKernel
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# The centrally excited random walk with a drift field

`IsDriftCERW μ ε ξ X` says that the process `X` on `(Ω, μ)` is the centrally excited random walk
with drift field `ξ` and parameter `ε`, started at the origin: every cylinder probability factors
through `driftStepProb`, exactly as `IsCERW` factors through `stepProb`. For a norm `Ψ` with chosen
subgradients `ξ(x) ∈ ∂Ψ(x)` this is the centrally excited random walk with norm `Ψ` of
`sec:norm-setup`.
-/

namespace CERW

open MeasureTheory LatticeProb

/-- The process `X` under `μ` is the centrally excited random walk on `ℤ^d` with drift field `ξ`
and parameter `ε`, started at the origin. -/
structure IsDriftCERW {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (X : ℕ → Ω → Site d) : Prop where
  /-- Each position is a random variable. -/
  measurable : ∀ n, Measurable (X n)
  /-- The walk starts at the origin. -/
  start : μ {ω | X 0 ω ≠ 0} = 0
  /-- The law of the next step given the whole past is `driftStepProb`. -/
  step : ∀ (n : ℕ) (x : ℕ → Site d),
    μ {ω | ∀ j ≤ n + 1, X j ω = x j} =
      μ {ω | ∀ j ≤ n, X j ω = x j} * ENNReal.ofReal (driftStepProb d ε ξ x n (x (n + 1) - x n))

end CERW
