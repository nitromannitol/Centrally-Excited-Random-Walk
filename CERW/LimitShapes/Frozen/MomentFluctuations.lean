module

public import CERW.LimitShapes.LimitLaws.MomentFluctuations
public import CERW.Frozen.MomentFluctuations

@[expose] public section

/-!
# thm:moment-fluctuations

The statement at `thm:moment-fluctuations`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The conclusion of `thm:moment-fluctuations`, with the standing assumptions and constant scopes
    of the paper. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.moment_fluctuations {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let v₁ : ℝ := 2 * d * ωd / (ε * (d + 2) * (d + 3))
    let v₂ : ℝ := 2 / (ε * d * ωd * (d + 2) * (d + 3))
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      let S : ℕ → Ω → ℝ := fun n ω =>
        (∑ x ∈ CERW.departureRange (X · ω) n, euclidNorm x - n / (2 * ε)) /
          r n ^ (((d : ℝ) + 3) / 2)
      let R : ℕ → Ω → ℝ := fun n ω =>
        (CERW.momentRadius (X · ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2)
      TendstoInDistribution S atTop id (fun _ => μ) (gaussianReal 0 v₁.toNNReal) ∧
      TendstoInDistribution R atTop id (fun _ => μ) (gaussianReal 0 v₂.toNNReal) ∧
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
        (∀ᶠ n : ℕ in atTop, σ * S n ω ≤ (Real.sqrt v₁ + δ) * Real.sqrt (2 * Real.log (Real.log
            n))) ∧
        (∃ᶠ n : ℕ in atTop, (Real.sqrt v₁ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * S n
            ω) ∧
        (∀ᶠ n : ℕ in atTop, σ * R n ω ≤ (Real.sqrt v₂ + δ) * Real.sqrt (2 * Real.log (Real.log
            n))) ∧
        (∃ᶠ n : ℕ in atTop, (Real.sqrt v₂ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * R n ω)
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.LimitLaws.moment_fluctuations hd
