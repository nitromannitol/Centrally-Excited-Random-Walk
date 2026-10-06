/-
# The term-level small-ball composition (`oct5.tex:188`)

`SmallBall.lean` proves the model theorem `gap_limsup_le_gaussian_ball`: under `IsCERW μ ε X`,
`limsup_n μ {Rout - Rin <= a √r_n} <= N(0, (1/2) I) (closedBall 0 (a √(3ε/π)))` for the literal model
radius `r_n` of the paper.  `GaussDisc.lean` and `SharpWidthDiskMass.lean` supply the exact
closed-disk mass and its coefficient form
`multivariateGaussian_halfI_smallBall_threePi`:
`μ (closedBall 0 (√(3δ/π) · a)) = ofReal (1 - e^{-(3δ/π) a²})`.

Composing the two bounds the limsup of `P (Rout - Rin <= a √r_n)` by `1 - e^{-(3ε/π) a²}`, with
no intermediate predicate (small-ball, CLT, annulus or disk-mass) left as a hypothesis: the only
inputs are the model hypotheses `0 < ε < 1/2` and `IsCERW μ ε X`.
-/
import CERW.Support.Lower.PlanarGap.SmallBall
import CERW.Support.Lower.PlanarGap.SharpWidthDiskMass

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open LatticeProb (Site euclidNorm)
open CERW CERW.Support.Law CERW.Support.Lower

universe u

namespace CERW.Support.Lower.PlanarGap

/-- **The small-ball bound of `oct5.tex:188`.**  For `0 < ε < 1/2`, `IsCERW μ ε X` and every
`a ≥ 0`, the limsup probability that the width `Rout - Rin` at time `n` is at most `a √r_n` is at
most `1 - e^{-(3ε/π) a²}`, with `r_n` the literal model radius of `gap_limsup_le_gaussian_ball`. -/
theorem gap_limsup_le_smallBall {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 ≤ a) :
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    limsup (fun n => μ {ω | maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
        a * Real.sqrt (r n)}) atTop ≤
      ENNReal.ofReal (1 - Real.exp (-((3 * ε / Real.pi) * a ^ 2))) := by
  intro r
  refine le_trans (gap_limsup_le_gaussian_ball (ε := ε) hε0 hεd (Ω := Ω) μ hX a) ?_
  rw [mul_comm a (Real.sqrt (3 * ε / Real.pi)),
    CERW.PlanarGap.multivariateGaussian_halfI_smallBall_threePi ε a hε0 ha]

end CERW.Support.Lower.PlanarGap
