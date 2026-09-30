import CERW.Model.Space
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A norm on `ℝ^d` and its subgradients

The setting of `sec:norm-setup`. A norm `Ψ` on `ℝ^d = EuclideanSpace ℝ (Fin d)` is a function
with `IsNorm Ψ`: subadditive, absolutely homogeneous, and zero only at the origin. A
subgradient of `Ψ` at `x` is a vector `ξ` with `Ψ y ≥ Ψ x + ξ · (y - x)` for every `y`. The unit
ball `B_Ψ = {Ψ < 1}` has volume `normBallVolume Ψ`, and `Λ_Ψ` and `c_Ψ` are the largest and least
values of `Ψ` on the Euclidean unit sphere (`normMax`, `normMin`). The standard basis vector `e_i`
of `ℝ^d` is `coordVec i`.
-/

namespace CERW

open MeasureTheory

variable {d : ℕ}

/-- `Ψ` is a norm on `ℝ^d`: subadditive, absolutely homogeneous, and zero only at the origin.
Nonnegativity and `Ψ 0 = 0` follow. -/
structure IsNorm (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  /-- The triangle inequality. -/
  add_le : ∀ x y, Ψ (x + y) ≤ Ψ x + Ψ y
  /-- Absolute homogeneity. -/
  smul : ∀ (t : ℝ) x, Ψ (t • x) = |t| * Ψ x
  /-- Only the origin has norm zero. -/
  eq_zero : ∀ x, Ψ x = 0 → x = 0

/-- `ξ` is a subgradient of `Ψ` at `x`: `Ψ y ≥ Ψ x + ξ · (y - x)` for every `y`. -/
def IsSubgradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ y, Ψ x + inner ℝ ξ (y - x) ≤ Ψ y

/-- The standard basis vector `e_i` of `ℝ^d`. -/
noncomputable def coordVec (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single i 1

/-- The volume `|B_Ψ|` of the unit ball `B_Ψ = {y : Ψ y < 1}`. -/
noncomputable def normBallVolume (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  (volume {y : EuclideanSpace ℝ (Fin d) | Ψ y < 1}).toReal

/-- `Λ_Ψ = max_{|u| = 1} Ψ(u)`. -/
noncomputable def normMax (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  sSup (Ψ '' Metric.sphere 0 1)

/-- `c_Ψ = min_{|u| = 1} Ψ(u)`. -/
noncomputable def normMin (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  sInf (Ψ '' Metric.sphere 0 1)

end CERW
