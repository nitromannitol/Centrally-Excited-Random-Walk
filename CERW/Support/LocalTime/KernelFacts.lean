import CERW.Support.Law.StepMean
import CERW.Model.Potential

/-!
# The facts about the potential kernel used downstream

The potential kernel `b` enters the proofs only through the properties collected here. They are
the Poisson equation `(P - I) b = 1_{0}`, the level sets `eq:levelsets` of the radial profile
`h_d`, the gradient asymptotics and the one-step bound of `eq:gradient`, and logarithmic growth.
The cited asymptotics `eq:kernel-asymptotics` imply all of them, for the planar potential kernel
and for `b = -G` when `d ≥ 3`.
-/

namespace CERW.Support.LocalTime

open LatticeProb CERW CERW.Support.Law

/-- The properties of a potential kernel `b` with radial profile `h` used in the proofs. -/
structure KernelFacts (d : ℕ) (b : Site d → ℝ) (h : ℝ → ℝ) : Prop where
  /-- The Poisson equation `(P - I) b = 1_{0}`. -/
  poisson : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0
  /-- `eq:levelsets`: for large `r`, `b ≤ h(r)` on `|x| ≤ r - 1` and `b ≥ h(r)` on `|x| ≥ r + 1`. -/
  levels : ∃ r₁ : ℝ, ∀ r : ℝ, r₁ ≤ r → ∀ x : Site d,
    (euclidNorm x ≤ r - 1 → b x ≤ h r) ∧ (r + 1 ≤ euclidNorm x → h r ≤ b x)
  /-- The first estimate of `eq:gradient`: `Db(x) = (2/ω_d) x/|x|^d + O(|x|^{-d})`. -/
  gradAsymp : ∃ R Ca : ℝ, 1 ≤ R ∧ ∀ x : Site d, R ≤ euclidNorm x →
    ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
      Ca * euclidNorm x ^ (-(d : ℝ))
  /-- The second estimate of `eq:gradient`: `|b(x + e) - b(x)| ≤ C (1 + |x|)^{1-d}`. -/
  gradBound : ∃ Cg : ℝ, ∀ x e : Site d, e ∈ unitSteps d →
    |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))
  /-- Logarithmic growth: `|b(x)| ≤ C log(|x| + 2)`. -/
  growth : ∃ Cb : ℝ, ∀ x : Site d, |b x| ≤ Cb * Real.log (euclidNorm x + 2)

end CERW.Support.LocalTime
