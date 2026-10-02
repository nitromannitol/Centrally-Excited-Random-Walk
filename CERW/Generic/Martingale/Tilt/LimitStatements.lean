import CERW.Generic.Martingale.Tilt.Statements

/-!
# The sharp lower tail at an unbounded horizon: the statements

The block of the law of the iterated logarithm ends at an almost surely finite but unbounded
time, so the window `v (1 - ρ) ≤ varSum ≤ v` holds only eventually, never at a fixed horizon.
At the horizon `n` the window is used only on `W = {v (1 - ρ) ≤ varSum n}`. The rest costs
`∫_{Wᶜ} Z(s) ≤ e^{3 s² v} √μ(Wᶜ)` by Cauchy–Schwarz (`TiltLowerOn`, `TiltTailOn`). Letting
`n → ∞`, `μ(Wᶜ) → 0` and the gated sums settle at their limit `L` (`SharpLowerTailLimit`).
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- The lower tail of `N` around `s v (1 - ρ)`, weighted by `Z(s)`, on a set `W` where the bracket
is at least `v (1 - ρ)`. -/
def TiltLowerOn : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ), Increments μ ℱ Y b n →
    ∀ {v ρ s l w : ℝ} {W : Set Ω}, MeasurableSet W → 0 ≤ l → l ≤ s → s * b ≤ 1 / 2 →
    (∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ v) →
    (∀ᵐ ω ∂μ, ω ∈ W → v * (1 - ρ) ≤ varSum μ ℱ Y n ω) →
    ∫ ω in {ω | ∑ t ∈ Finset.range n, Y t ω ≤ s * v * (1 - ρ) - w} ∩ W,
        expMart μ ℱ Y s n ω ∂μ ≤
      Real.exp (l ^ 2 * v / 2 + 2 * ((s - l) ^ 3 + s ^ 3) * b * v - l * w)

/-- The tail of `N` above `s v (1 - ρ) - w` when the lower bound of the bracket holds only on `W`:
the complement of `W` costs `e^{3 s² v} √μ(Wᶜ)`. -/
def TiltTailOn : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ), Increments μ ℱ Y b n →
    ∀ {v ρ s w l₁ l₂ : ℝ} {W : Set Ω}, MeasurableSet W → 0 ≤ s → 0 ≤ l₁ → 0 ≤ l₂ → l₂ ≤ s →
    (s + l₁) * b ≤ 1 / 2 → (∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ v) →
    (∀ᵐ ω ∂μ, ω ∈ W → v * (1 - ρ) ≤ varSum μ ℱ Y n ω) →
    Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) *
        (1 - Real.exp (l₁ ^ 2 * v / 2 + 2 * ((s + l₁) ^ 3 + s ^ 3) * b * v - l₁ * w)
          - Real.exp (l₂ ^ 2 * v / 2 + 2 * ((s - l₂) ^ 3 + s ^ 3) * b * v - l₂ * w)
          - Real.exp (3 * s ^ 2 * v) * Real.sqrt (μ Wᶜ).toReal) ≤
      (μ {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω}).toReal

/-- **The sharp lower tail at an unbounded horizon.** For increments bounded by `b` at all times,
with bracket at most `v` at every time and eventually at least `v (1 - ρ)`, and partial sums
eventually equal to `L`, one has `P(L ≥ a) ≥ exp (-(1 + η) a² / (2 v))`, under the conditions of
`SharpLowerTail`. -/
def SharpLowerTailLimit : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ρ₀ ε₀ A₀ : ℝ, 0 < ρ₀ ∧ 0 < ε₀ ∧
    ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (b : ℝ) (L : Ω → ℝ), Measurable L →
      (∀ n, Increments μ ℱ Y b n) →
      ∀ {v a ρ : ℝ}, 0 < v → 0 < a → 0 ≤ ρ → ρ ≤ ρ₀ →
      (∀ n, ∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ v) →
      (∀ᵐ ω ∂μ, ∀ᶠ n in atTop, v * (1 - ρ) ≤ varSum μ ℱ Y n ω) →
      (∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∑ t ∈ Finset.range n, Y t ω = L ω) →
      A₀ * v ≤ a ^ 2 → a * b ≤ ε₀ * v →
      Real.exp (-((1 + η) * (a ^ 2 / (2 * v)))) ≤ (μ {ω | a ≤ L ω}).toReal

end CERW.Generic.Martingale.Tilt
