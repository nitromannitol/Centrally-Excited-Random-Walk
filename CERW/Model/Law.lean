import CERW.Model.Kernel
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Centrally excited random walk

`IsCERW μ ε X` says that the process `X` on the measure space `(Ω, μ)` is centrally excited
random walk with parameter `ε` started at the origin. The paper specifies the process by
its conditional transition probabilities given the entire past (`eq:kernel` and the sentence
after it). On the countable state space `ℤ^d` this is the statement that every cylinder
probability factors: `P(X_0 = x_0, …, X_{n+1} = x_{n+1})` is
`P(X_0 = x_0, …, X_n = x_n)` times the one-step probability `stepProb` read off the past
`x_0, …, x_n`.

The predicate fixes the law of the path and nothing else. The sample space, the measure and
the realization are arbitrary. The results of the paper are stated for every realization;
that a realization exists is proved in `CERW.Support.Law.Existence`.
-/

namespace CERW

open MeasureTheory LatticeProb

/-- The process `X` under `μ` is centrally excited random walk on `ℤ^d` with parameter `ε`,
started at the origin: each `X n` is measurable, `X 0 = 0` almost surely, and every
cylinder probability factors through `stepProb`. -/
structure IsCERW {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ε : ℝ)
    (X : ℕ → Ω → Site d) : Prop where
  /-- Each position is a random variable. -/
  measurable : ∀ n, Measurable (X n)
  /-- The walk starts at the origin. -/
  start : μ {ω | X 0 ω ≠ 0} = 0
  /-- The law of the next step given the whole past is `stepProb`. -/
  step : ∀ (n : ℕ) (x : ℕ → Site d),
    μ {ω | ∀ j ≤ n + 1, X j ω = x j} =
      μ {ω | ∀ j ≤ n, X j ω = x j} * ENNReal.ofReal (stepProb d ε x n (x (n + 1) - x n))

end CERW
