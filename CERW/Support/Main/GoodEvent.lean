import CERW.Model.Occupation
import CERW.Model.Potential

/-!
# The event of the fluctuation theorem

`fluctGood d ε C Y n` is the event `Good C Y n` of `thm:fluctuations` for the path `Y` at time
`n`. It contains the inner and outer inclusions of `eq:sandwich`, the volume bound `eq:volume`
together with the symmetric difference, and the profile bound `eq:profile-rate`. The scale is
`N = n^{1/(d+1)}` and `L = log(n + 2)`. The rate is `Q = (L/N)^{1/2}` in the plane and
`Q = (L/N)^{d/(2d-1)}` for `d ≥ 3`.
-/

open scoped symmDiff Pointwise

namespace CERW.Support.Main

open MeasureTheory LatticeProb CERW

/-- The event `Good C Y n` of `thm:fluctuations`. -/
def fluctGood (d : ℕ) (ε C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
  let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
  let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  let L : ℝ := Real.log (n + 2)
  let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
  {x : Site d | euclidNorm x < (a - C * Q) * N} ⊆ ↑(departureRange Y n) ∧
  (↑(departureRange Y n) : Set (Site d)) ⊆ ↑(visitedRange Y n) ∧
  (↑(visitedRange Y n) : Set (Site d)) ⊆
    {x | euclidNorm x < (a + C * Q ^ ((1 : ℝ) / d) * L) * N} ∧
  volume ((N⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
      + ENNReal.ofReal |((departureRange Y n).card : ℝ) / N ^ d - ωd * a ^ d|
    ≤ ENNReal.ofReal (C * Q) ∧
  ∀ x : Site d,
    |(localTime Y n x : ℝ) / N - 2 * d * ε * max (a - euclidNorm x / N) 0| ≤ C * Q ^ ((1 : ℝ) / d)

end CERW.Support.Main
