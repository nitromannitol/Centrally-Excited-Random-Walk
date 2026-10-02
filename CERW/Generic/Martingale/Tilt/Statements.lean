import CERW.Generic.Martingale.ExpMart

/-!
# A sharp lower tail for martingales with a pinned bracket: the statements

For increments `Y t`, `t < n`, bounded by `b` and conditionally centred, whose total conditional
variance `V = varSum` lies in `[v (1 - ρ), v]` almost surely, the sum `N = ∑_{t<n} Y t` satisfies
`P(N ≥ a) ≥ exp (-(1 + η) a² / (2 v))` once `a² / v` is large and `a b / v` and `ρ` are small
(`SharpLowerTail`). This is the sharp lower tail of the lower half of the martingale law of the
iterated logarithm.

The proof tilts by the exponential martingale `Z(s) = expMart s = exp (s N - K(s))`, whose mean is
one, but it never changes the measure. Since `Z(s) e^{±λ N} = Z(s ± λ) e^{K(s ± λ) - K(s) ± …}`,
the bound `|K(s) - s² V / 2| ≤ 2 |s|³ b V` controls the `Z(s)`-weighted mass of each tail of `N`
around `s v` (`TiltUpper`, `TiltLower`). On the window between those tails, `Z(s)⁻¹` is bounded
below, which gives the tail (`TiltTail`). `TailArith` chooses the parameters.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- The upper tail of `N` around `s v`, weighted by `Z(s)`. -/
def TiltUpper : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ), Increments μ ℱ Y b n →
    ∀ {v s l w : ℝ}, 0 ≤ s → 0 ≤ l → (s + l) * b ≤ 1 / 2 →
    (∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ v) →
    ∫ ω in {ω | s * v + w ≤ ∑ t ∈ Finset.range n, Y t ω}, expMart μ ℱ Y s n ω ∂μ ≤
      Real.exp (l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v - l * w)

/-- The lower tail of `N` around `s v (1 - ρ)`, weighted by `Z(s)`. -/
def TiltLower : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ), Increments μ ℱ Y b n →
    ∀ {v ρ s l w : ℝ}, 0 ≤ l → l ≤ s → s * b ≤ 1 / 2 →
    (∀ᵐ ω ∂μ, v * (1 - ρ) ≤ varSum μ ℱ Y n ω ∧ varSum μ ℱ Y n ω ≤ v) →
    ∫ ω in {ω | ∑ t ∈ Finset.range n, Y t ω ≤ s * v * (1 - ρ) - w}, expMart μ ℱ Y s n ω ∂μ ≤
      Real.exp (l ^ 2 * v / 2 + 2 * ((s - l) ^ 3 + s ^ 3) * b * v - l * w)

/-- The tail of `N` above `s v (1 - ρ) - w`, from the two weighted tails. -/
def TiltTail : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ), Increments μ ℱ Y b n →
    ∀ {v ρ s w l₁ l₂ : ℝ}, 0 ≤ s → 0 ≤ l₁ → 0 ≤ l₂ → l₂ ≤ s → (s + l₁) * b ≤ 1 / 2 →
    (∀ᵐ ω ∂μ, v * (1 - ρ) ≤ varSum μ ℱ Y n ω ∧ varSum μ ℱ Y n ω ≤ v) →
    Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) *
        (1 - Real.exp (l₁ ^ 2 * v / 2 + 2 * ((s + l₁) ^ 3 + s ^ 3) * b * v - l₁ * w)
          - Real.exp (l₂ ^ 2 * v / 2 + 2 * ((s - l₂) ^ 3 + s ^ 3) * b * v - l₂ * w)) ≤
      (μ {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω}).toReal

/-- The choice of the parameters. With `θ = min η 1 / 40`, for `w = θ a`,
`s = (a + w) / (v (1 - ρ))` and `l = w / v`, the window starts at `a`, the two weighted tails are
each at most `1/4`, and the prefactor beats `exp (-(1 + η) a² / (2 v))`. -/
def TailArith : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ρ₀ ε₀ A₀ θ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ 0 < ε₀ ∧ 0 < θ ∧
    ∀ v a ρ b : ℝ, 0 < v → 0 < a → 0 ≤ ρ → ρ ≤ ρ₀ → 0 ≤ b → A₀ * v ≤ a ^ 2 → a * b ≤ ε₀ * v →
      let w := θ * a
      let s := (a + w) / (v * (1 - ρ))
      let l := w / v
      0 ≤ s ∧ 0 ≤ l ∧ l ≤ s ∧ (s + l) * b ≤ 1 / 2 ∧ s * v * (1 - ρ) - w = a ∧
        Real.exp (l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v - l * w) ≤ 1 / 4 ∧
        Real.exp (l ^ 2 * v / 2 + 2 * ((s - l) ^ 3 + s ^ 3) * b * v - l * w) ≤ 1 / 4 ∧
        Real.exp (-((1 + η) * (a ^ 2 / (2 * v)))) ≤
          Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) * (1 / 2)

/-- **The sharp lower tail.** For every `η > 0` there are `ρ₀, ε₀ > 0` and `A₀` such that, for
increments bounded by `b` with total conditional variance in `[v (1 - ρ), v]` almost surely,
`ρ ≤ ρ₀`, `a² ≥ A₀ v` and `a b ≤ ε₀ v`, one has `P(∑_{t<n} Y t ≥ a) ≥ exp (-(1 + η) a² / (2 v))`. -/
def SharpLowerTail : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ρ₀ ε₀ A₀ : ℝ, 0 < ρ₀ ∧ 0 < ε₀ ∧
    ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ), Increments μ ℱ Y b n →
      ∀ {v a ρ : ℝ}, 0 < v → 0 < a → 0 ≤ ρ → ρ ≤ ρ₀ →
      (∀ᵐ ω ∂μ, v * (1 - ρ) ≤ varSum μ ℱ Y n ω ∧ varSum μ ℱ Y n ω ≤ v) →
      A₀ * v ≤ a ^ 2 → a * b ≤ ε₀ * v →
      Real.exp (-((1 + η) * (a ^ 2 / (2 * v)))) ≤
        (μ {ω | a ≤ ∑ t ∈ Finset.range n, Y t ω}).toReal

end CERW.Generic.Martingale.Tilt
