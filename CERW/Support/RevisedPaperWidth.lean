import CERW.Generic.Martingale.Lil.LowerStatement
import CERW.Generic.Martingale.LilAssembly.StoutLower
import CERW.Support.Stout
import CERW.Model
import CERW.Support.Lower.ExpDeviation
import CERW.Support.Lower.SharpWidth
import CERW.Support.Main.LimitShape
import CERW.Support.Lower.PlanarGap.SmallBallCompose

/-!
# The difference of the radii in the plane

`thm:sharp` of the revised paper has a third assertion on the difference of the radii in the plane,
part (iv)(c): for every `a ≥ 0`,
`limsup_n P(Rout(n) - Rin(n) ≤ a √r_n) ≤ 1 - exp(-3 ε a² / π)`.
`sharp_width_extended` states parts (iv)(a), (iv)(b) and (iv)(c) together, for the radius `r_n` of
the paper. It applies the support results that prove parts (iv)(a) and (iv)(b), the polynomial lower
bound `sharp_width_poly_of` and the lower bound of the limsup `sharp_width_of`, and, for part
(iv)(c), `PlanarGap.gap_limsup_le_smallBall`; the latter composes the bound of the width by the
closed-disc mass of the Gaussian limit with the formula for that mass, and takes as inputs only
`0 < ε < 1/2` and the law of the walk.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.RevisedPaper

/-- `thm:sharp` part (iv), the difference of the radii in the plane: (a) a polynomial lower bound
at the scale `√(r_n log n)`, (b) the lower bound of the limsup at the scale `√(r_n log log n)`, and
(c) for every `a ≥ 0`, `limsup_n P(Rout(n) - Rin(n) ≤ a √r_n) ≤ 1 - exp(-3 ε a² / π)`. -/
theorem sharp_width_extended {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    (∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let E : Set Ω := {ω | c * Real.sqrt (r n * Real.log n)
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n}
        MeasurableSet E ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ E) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
        (Real.sqrt (Real.pi / (3 * ε)) - δ) * Real.sqrt (r n * Real.log (Real.log n))
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n) ∧
    (∀ a : ℝ, 0 ≤ a →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        limsup (fun n => μ {ω | CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n
          ≤ a * Real.sqrt (r n)}) atTop ≤
          ENNReal.ofReal (1 - Real.exp (-(3 * ε * a ^ 2 / Real.pi)))) := by
  intro ωd ε hε0 hε1 r
  refine ⟨CERW.Support.Lower.sharp_width_poly_of @CERW.Support.Lower.exp_deviation hd ε hε0 hε1,
    (CERW.Support.Lower.sharp_width_of @CERW.Support.Main.limit_shape
      @CERW.Support.Lower.exp_deviation hd (CERW.Support.stoutLIL_full
        CERW.Generic.Martingale.LilAssembly.stout_lower) ε hε0 hε1).2,
    fun a ha0 Ω _ μ _ X hX => ?_⟩
  subst hd
  have hc := CERW.Support.Lower.PlanarGap.gap_limsup_le_smallBall (ε := ε) hε0 hε1 μ hX ha0
  have hexp : -(3 * ε * a ^ 2 / Real.pi) = -((3 * ε / Real.pi) * a ^ 2) := by ring
  rw [hexp]
  exact hc

end CERW.Support.RevisedPaper
