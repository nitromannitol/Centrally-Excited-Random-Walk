import Mathlib.Probability.Martingale.Basic

/-!
# Adapted sign sequences

A sequence of signs `ε j` on a probability space `(Ξ, ν)`, adapted to a filtration `𝒦` in the
sense that `ε (j + 1)` is `𝒦 (j + 1)`-measurable and has conditional mean zero given `𝒦 j`.
Independent fair coins give such a sequence; it is used to pad a martingale where its increments
are cut off.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory

/-- The signs `ε (j + 1)` are `𝒦 (j + 1)`-measurable, square to one, and have conditional mean
zero given `𝒦 j`, for a monotone family `𝒦` of sub-σ-algebras. -/
structure SignSequence {Ξ : Type*} {mΞ : MeasurableSpace Ξ} (ν : Measure Ξ)
    (𝒦 : ℕ → MeasurableSpace Ξ) (ε : ℕ → Ξ → ℝ) : Prop where
  mono : Monotone 𝒦
  le : ∀ n, 𝒦 n ≤ mΞ
  measurable : ∀ j, StronglyMeasurable[𝒦 (j + 1)] (ε (j + 1))
  sq_eq_one : ∀ j ξ, ε j ξ ^ 2 = 1
  condExp_eq_zero : ∀ j, ν[ε (j + 1) | 𝒦 j] =ᵐ[ν] 0

end CERW.Generic.Martingale.LilLower
