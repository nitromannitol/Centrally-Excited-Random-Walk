module

public import CERW.LimitShapes.Frozen.MomentFluctuations
public import CERW.Support.Lower.SharpRadii
public import CERW.Generic.Martingale.CLT.Proved
public import CERW.Generic.Martingale.LilAssembly.StoutLower
public import CERW.Support.Stout

@[expose] public section

/-!
# Planar radius fluctuations

Theorem `thm:sharp` (ii) follows from the current moment fluctuations and the
pathwise moment-radius comparison.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

/-- The two radius lower bounds in Theorem `thm:sharp` (ii), from moment fluctuations. -/
theorem CERW.LimitShapes.PlanarLower.sharp_radii_lil_from_moment {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ r n - CERW.innerRadius (X · ω) n) ∧
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ CERW.maxRadius (X · ω) n - r n) := by
  have hmom : CERW.Support.Statements.moment_fluctuations.{u} := by
    intro d hd _ _
    exact CERW.LimitShapes.moment_fluctuations hd
  exact CERW.Support.Lower.sharp_radii_lil_of_clt
    CERW.Generic.Martingale.CLT.martingaleCLT_proved hmom hd
    (CERW.Support.stoutLIL_full CERW.Generic.Martingale.LilAssembly.stout_lower)
