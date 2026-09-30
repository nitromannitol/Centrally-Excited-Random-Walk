import Mathlib.Probability.Martingale.Basic

/-!
# The predictable bracket of discrete martingales

For real processes `S`, `T` adapted to a filtration `ℱ`, the predictable covariation
`⟨S, T⟩_n = Σ_{t<n} E((S_{t+1} - S_t)(T_{t+1} - T_t) | ℱ_t)`, and `⟨S⟩_n = ⟨S, S⟩_n`. It is a
conditional expectation, so it is defined up to a null set; statements use it under `∀ᵐ`.
-/

namespace CERW

open MeasureTheory

/-- The predictable covariation `⟨S, T⟩_n = Σ_{t<n} E((S_{t+1} - S_t)(T_{t+1} - T_t) | ℱ_t)`. -/
noncomputable def predBracket {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (S T : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ t ∈ Finset.range n, μ[fun ω => (S (t + 1) ω - S t ω) * (T (t + 1) ω - T t ω) | ℱ t]

end CERW
