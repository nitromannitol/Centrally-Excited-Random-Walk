import CERWAudit.Sharpness.SolutionBasic
import CERW.LimitShapes.Frozen.SharpRadii
import CERW.LimitShapes.Frozen.SharpRadiiLil
import CERW.LimitShapes.Frozen.SharpBulk
import CERW.LimitShapes.Frozen.SharpWidth

/-!
# Sharpness: comparator solution

The copied laws are transported field by field, and the certified theorems
supply the conclusions over the definitionally equal occupation quantities.
-/

universe u

namespace CERW.StatementAudit.Sharpness

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal

/-- The copied Euclidean walk law is the repository's cylinder-factorization law. -/
theorem isCERW_iff {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {X : ℕ → Ω → Site d} : IsCERW μ ε X ↔ CERW.IsCERW μ ε X := by
  constructor <;> rintro ⟨hm, hs, hst⟩ <;> exact ⟨hm, hs, hst⟩

/-- The copied norm hypotheses are the repository's norm hypotheses. -/
theorem isNorm_iff {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} :
    IsNorm Ψ ↔ CERW.IsNorm Ψ := by
  constructor <;> rintro ⟨ha, hs, hz⟩ <;> exact ⟨ha, hs, hz⟩

/-- The copied drift walk law is the repository's cylinder-factorization law. -/
theorem isDriftCERW_iff {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {X : ℕ → Ω → Site d} :
    IsDriftCERW μ ε ξ X ↔ CERW.IsDriftCERW μ ε ξ X := by
  constructor <;> rintro ⟨hm, hs, hst⟩ <;> exact ⟨hm, hs, hst⟩

/-- The `sharp_radii` assertion of the introduction, with all clauses. -/
theorem sharp_radii {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let Ein : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ r n - innerRadius (X · ω) n}
        let Eout : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ maxRadius (X · ω) n - r n}
        MeasurableSet Ein ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Ein ∧
          MeasurableSet Eout ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Eout
:= by
  intro ωd ε hε hεd r p hp
  obtain ⟨c, hc, n₀, h⟩ := CERW.LimitShapes.sharp_radii hd ε hε hεd p hp
  refine ⟨c, hc, n₀, ?_⟩
  intro Ω _ μ _ X hX
  exact h μ X (isCERW_iff.mp hX)

/-- The `sharp_radii_lil` assertion of the introduction, with all clauses. -/
theorem sharp_radii_lil {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ r n - innerRadius (X · ω) n) ∧
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ maxRadius (X · ω) n - r n)
:= by
  intro ωd ε hε hεd r Ω _ μ _ X hX
  exact CERW.LimitShapes.sharp_radii_lil hd ε hε hεd μ X (isCERW_iff.mp hX)

/-- The `sharp_bulk` assertion of the introduction, with all clauses. -/
theorem sharp_bulk {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∃ x : Site d, euclidNorm x ≤ Real.sqrt (r n) ∧
            c * (if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n))
              ≤ |(localTime (X · ω) n x : ℝ) - 2 * d * ε * (r n - euclidNorm x)|}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))
:= by
  intro ωd ε hε hεd r
  obtain ⟨c, hc, n₀, h⟩ := CERW.LimitShapes.sharp_bulk hd ε hε hεd
  refine ⟨c, hc, n₀, ?_⟩
  intro Ω _ μ _ X hX
  exact h μ X (isCERW_iff.mp hX)

/-- The `sharp_width` assertion of the introduction, with all clauses. -/
theorem sharp_width {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    (∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let E : Set Ω := {ω | c * Real.sqrt (r n * Real.log n)
          ≤ maxRadius (X · ω) n - innerRadius (X · ω) n}
        MeasurableSet E ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ E) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
        (Real.sqrt (Real.pi / (3 * ε)) - δ) * Real.sqrt (r n * Real.log (Real.log n))
          ≤ maxRadius (X · ω) n - innerRadius (X · ω) n) ∧
    (∀ a : ℝ, 0 ≤ a →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X →
        limsup (fun n => μ {ω | maxRadius (X · ω) n - innerRadius (X · ω) n
          ≤ a * Real.sqrt (r n)}) atTop ≤
          ENNReal.ofReal (1 - Real.exp (-(3 * ε * a ^ 2 / Real.pi))))
:= by
  intro ωd ε hε hεd r
  obtain ⟨hpoly, hlil, hsmall⟩ := CERW.LimitShapes.sharp_width hd ε hε hεd
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨c, hc, n₀, h⟩ := hpoly p hp
    refine ⟨c, hc, n₀, ?_⟩
    intro Ω _ μ _ X hX
    exact h μ X (isCERW_iff.mp hX)
  · intro Ω _ μ _ X hX
    exact hlil μ X (isCERW_iff.mp hX)
  · intro a ha Ω _ μ _ X hX
    exact hsmall a ha μ X (isCERW_iff.mp hX)


end CERW.StatementAudit.Sharpness
