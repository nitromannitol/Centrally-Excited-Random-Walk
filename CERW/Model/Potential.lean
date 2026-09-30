import CERW.Model.Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The inward-drift potential and its radial tail

For a set `D ⊆ ℝ^d` the potential of `eq:potential-intro` is
`U_D(y) = (2ε/ω_d) ∫_D u_v · (v - y) |v - y|^{-d} dv`, where `ω_d` is the volume of the
Euclidean unit ball. Its spherical averages are governed by the weighted exterior volume
`F(s) = σ_d^{-1} ∫_{D ∩ {|v| > s}} |v|^{1-d} dv` with `σ_d = d ω_d` (`eq:Fmass`, in the form
in which `lem:geometry` states it). Both are Bochner integrals, so they carry their meaning
only when the integrand is integrable. That holds for every bounded measurable `D`, which is
the only case the paper uses, and every statement using them carries those hypotheses.
-/

namespace CERW

open MeasureTheory

/-- The volume `ω_d` of the Euclidean unit ball of `ℝ^d`. -/
noncomputable def unitBallVolume (d : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

/-- The potential `U_D(y) = (2ε/ω_d) ∫_D u_v · (v - y) |v - y|^{-d} dv` of `eq:potential-intro`.
At the single point `v = y` the integrand reads `0`, which does not affect the integral. -/
noncomputable def potential (d : ℕ) (ε : ℝ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d

/-- The weighted exterior volume `F(s) = σ_d^{-1} ∫_{D ∩ {|v| > s}} |v|^{1-d} dv`, with
`σ_d = d ω_d` the area of the unit sphere (`eq:Fdef`, `eq:Fmass`). -/
noncomputable def tail (d : ℕ) (D : Set (EuclideanSpace ℝ (Fin d))) (s : ℝ) : ℝ :=
  (d * unitBallVolume d)⁻¹ * ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ))

end CERW
