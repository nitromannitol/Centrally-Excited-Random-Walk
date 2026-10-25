module

public import CERW.LimitShapes.LimitLaws.SiteFluctuations
public import CERW.Frozen.SiteFluctuations

@[expose] public section

/-!
# thm:site-fluctuations

The statement at `thm:site-fluctuations`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `thm:site-fluctuations`, with the standing assumptions and constant scopes
    of the paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.site_fluctuations {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let G : Site d → ℝ := LatticeProb.srwGreenInf d
    let σ : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (r n * Real.log (r n)) else Real.sqrt (r n)
    let lil : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (2 * r n * Real.log (r n) * Real.log (Real.log n))
      else Real.sqrt (2 * r n * Real.log (Real.log n))
    let v : ℝ := if d = 2 then 16 * ε / Real.pi else 2 * d * ε * (2 * G 0 - 1)
    let cov : Site d → Site d → ℝ := fun y z =>
      if d = 2 then 16 * ε / Real.pi else 2 * d * ε * (2 * G (y - z) - if y = z then 1 else 0)
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      let dev : Site d → ℕ → Ω → ℝ := fun y n ω =>
        (CERW.localTime (X · ω) n y : ℝ) - 2 * d * ε * (r n - euclidNorm y)
      (∀ y : Site d,
        TendstoInDistribution (fun n ω => dev y n ω / σ n) atTop id (fun _ => μ)
          (gaussianReal 0 v.toNNReal)) ∧
      (∀ y : Site d, ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ s : ℝ, s = 1 ∨ s = -1 →
        (∀ᶠ n : ℕ in atTop, s * dev y n ω ≤ (Real.sqrt v + δ) * lil n) ∧
        (∃ᶠ n : ℕ in atTop, (Real.sqrt v - δ) * lil n ≤ s * dev y n ω)) ∧
      (∀ (k : ℕ) (y : Fin k → Site d),
        TendstoInDistribution
          (fun n ω => (WithLp.toLp 2 (fun i => dev (y i) n ω / σ n) : EuclideanSpace ℝ (Fin k)))
          atTop id (fun _ => μ)
          (multivariateGaussian 0 (Matrix.of fun i j => cov (y i) (y j))))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.LimitLaws.site_fluctuations hd
