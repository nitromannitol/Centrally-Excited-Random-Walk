import CERW.LimitShapes.PlanarLower.Width
import CERW.LimitShapes.Frozen.FluctuationRates
import CERW.Support.Lower.PlanarGap.SmallBallCompose

/-!
# Planar width small-ball bound

The three width conclusions of Theorem `thm:sharp` (iv) from the current shape and
fluctuation estimates and the compensated-position Gaussian limit.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.PlanarLower

/-- The width bounds of Theorem `thm:sharp` (iv) from the current norm shape. -/
theorem sharp_width_from_norm_shape {d : ℕ} (hd : d = 2) :
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
  obtain ⟨hpoly, hlil⟩ := sharp_width_lower_from_norm_shape hd ε hε0 hε1
  refine ⟨hpoly, hlil, ?_⟩
  subst d
  intro a ha Ω _ μ _ X hX
  have h := CERW.Support.Lower.PlanarGap.gap_limsup_le_smallBall_of_fluctuation_rates
    @CERW.LimitShapes.fluctuation_rates hε0 hε1 μ hX ha
  simpa only [div_mul_eq_mul_div] using h

end CERW.LimitShapes.PlanarLower
