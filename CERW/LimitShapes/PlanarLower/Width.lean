import CERW.LimitShapes.Frozen.LimitShape
import CERW.Support.Lower.ExpDeviationAE
import CERW.Support.Lower.SharpWidth
import CERW.Generic.Martingale.LilAssembly.StoutLower
import CERW.Support.Stout

/-!
# Planar width lower bounds

The polynomial and iterated-logarithm lower bounds of Theorem `thm:sharp` (iv)
use the current limit shape and the compensated-position martingale kernels.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.PlanarLower

/-- The polynomial and iterated-logarithm width bounds of Theorem `thm:sharp` (iv). -/
theorem sharp_width_lower_from_norm_shape {d : ℕ} (hd : d = 2) :
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
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n) := by
  intro ωd ε hε0 hε1 r
  exact CERW.Support.Lower.sharp_width_of @CERW.LimitShapes.limit_shape
    @CERW.Support.Lower.exp_deviation_ae_upTo hd
    (CERW.Support.stoutLIL_full CERW.Generic.Martingale.LilAssembly.stout_lower) ε hε0 hε1

end CERW.LimitShapes.PlanarLower
