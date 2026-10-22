import CERW.LimitShapes

/-!
# Main theorems

The introduction's limit shapes, quantitative fluctuations, and sharpness results
are restated here in full. Each proof applies the corresponding certified theorem.
-/

universe u

namespace CERW.MainTheorems

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- The introduction's `limit_shape` conclusion, with all clauses and uniform constants. -/
theorem limit_shape {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | euclidNorm x < (1 - η) * r n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
:= by
  exact CERW.LimitShapes.limit_shape hd hε hεd μ X hX

/-- The introduction's `fluctuation_rates` conclusion, with all clauses and uniform constants. -/
theorem fluctuation_rates {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      (if d = 2 then
          |CERW.innerRadius Y n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
            CERW.maxRadius Y n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else
          |CERW.innerRadius Y n - r n| ≤ C * Real.log n ∧
            CERW.maxRadius Y n - r n ≤ C * Real.log n ^ ((d : ℝ) + 1)) ∧
      volume (((r n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          ≤ ENNReal.ofReal
            (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (r n * Real.log n)
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good C (X · ω) n)
:= by
  exact CERW.LimitShapes.fluctuation_rates hd

/-- The introduction's `sharp_radii` conclusion, with all clauses and uniform constants. -/
theorem sharp_radii {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let Ein : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ r n - CERW.innerRadius (X · ω) n}
        let Eout : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ CERW.maxRadius (X · ω) n - r n}
        MeasurableSet Ein ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Ein ∧
          MeasurableSet Eout ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Eout
:= by
  exact CERW.LimitShapes.sharp_radii hd

/-- The introduction's `sharp_radii_lil` conclusion, with all clauses and uniform constants. -/
theorem sharp_radii_lil {d : ℕ} (hd : d = 2) :
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
            ≤ CERW.maxRadius (X · ω) n - r n)
:= by
  exact CERW.LimitShapes.sharp_radii_lil hd

/-- The introduction's `sharp_bulk` conclusion, with all clauses and uniform constants. -/
theorem sharp_bulk {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∃ x : Site d, euclidNorm x ≤ Real.sqrt (r n) ∧
            c * (if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n))
              ≤ |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * (r n - euclidNorm x)|}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))
:= by
  exact CERW.LimitShapes.sharp_bulk hd

/-- The introduction's `sharp_width` conclusion, with all clauses and uniform constants. -/
theorem sharp_width {d : ℕ} (hd : d = 2) :
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
          ENNReal.ofReal (1 - Real.exp (-(3 * ε * a ^ 2 / Real.pi))))
:= by
  exact CERW.LimitShapes.sharp_width hd

/-- The introduction's `norm_shape` conclusion, with all clauses and uniform constants. -/
theorem norm_shape {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hεΨ : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | Ψ (CERW.toSpace x) < (1 - η) * r n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | Ψ (CERW.toSpace x) < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - Ψ (CERW.toSpace x)) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
:= by
  exact CERW.LimitShapes.norm_shape hd hΨ hξ hξ0 hε hεΨ μ X hX

end CERW.MainTheorems
