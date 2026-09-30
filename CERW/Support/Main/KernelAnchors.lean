import CERW.Support.Main.GoodCore
import CERW.Support.Main.FluctAssembly
import CERW.Support.Main.HausdorffAssembly
import CERW.Support.Main.HausdorffOneSided

/-!
# The fluctuation, shape and Hausdorff theorems from the kernel facts

The deterministic core `exists_good_of_event` supplies the hypothesis `hcore` of
`fluctuation_bounds_of_core`, `ball_shape_of_core`, `hausdorff_bound_of_core` (two-sided planar
remark) and `hausdorff_bound_one_sided_of_core` (one-sided planar remark).
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Main

open CERW CERW.Support.LocalTime

/-- `thm:fluctuations`, for any kernel `b` with the kernel facts. -/
theorem fluctuation_bounds_of_kernelFacts {d : ℕ} (hd : 2 ≤ d)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    let L : ℕ → ℝ := fun n => Real.log (n + 2)
    let Q : ℕ → ℝ := fun n =>
      if d = 2 then (L n / N n) ^ ((1 : ℝ) / 2) else (L n / N n) ^ ((d : ℝ) / (2 * d - 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      {x : Site d | euclidNorm x < (a - C * Q n) * N n} ⊆ ↑(CERW.departureRange Y n) ∧
      (↑(CERW.departureRange Y n) : Set (Site d)) ⊆ ↑(CERW.visitedRange Y n) ∧
      (↑(CERW.visitedRange Y n) : Set (Site d)) ⊆
        {x | euclidNorm x < (a + C * Q n ^ ((1 : ℝ) / d) * L n) * N n} ∧
      volume (((N n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
          + ENNReal.ofReal |((CERW.departureRange Y n).card : ℝ) / N n ^ d - ωd * a ^ d|
        ≤ ENNReal.ofReal (C * Q n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0|
          ≤ C * Q n ^ ((1 : ℝ) / d)
    (∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Good C (X · ω) n) :=
  fluctuation_bounds_of_core hd hK
    (fun _ hε _ _ hC₀ hC₁ _ _ hbd => exists_good_of_event hd hε hC₀ hC₁ hbd)

/-- `thm:shape`, for any kernel `b` with the kernel facts. -/
theorem ball_shape_of_kernelFacts {d : ℕ} (hd : 2 ≤ d)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < a → ∀ᶠ n in atTop,
        {x : Site d | euclidNorm x < (a - η) * N n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆ ↑(CERW.visitedRange (X · ω) n) ∧
        (↑(CERW.visitedRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (a + η) * N n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0|
          ≤ η) ∧
      Tendsto (fun n => ((CERW.visitedRange (X · ω) n).card : ℝ) / N n ^ d) atTop
        (𝓝 (ωd * a ^ d)) ∧
      (∀ x : Site d,
        Tendsto (fun n => (CERW.localTime (X · ω) n x : ℝ) / N n) atTop (𝓝 (2 * d * ε * a))) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x) :=
  ball_shape_of_core hd hK
    (fun _ hε _ _ hC₀ hC₁ _ _ hbd => exists_good_of_event hd hε hC₀ hC₁ hbd) hε hεd μ X hX

/-- `eq:hausdorff` with the two-sided planar remark, for any kernel `b` with the kernel facts. -/
theorem hausdorff_bound_of_kernelFacts {d : ℕ} (hd : 2 ≤ d)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ (Metric.hausdorffEDist
                    ((fun x => N⁻¹ • CERW.toSpace x) '' ↑(CERW.visitedRange (X · ω) n))
                    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) a)
                  ≤ ENNReal.ofReal (C * (if d = 2 then (n : ℝ) ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4)
                      else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
                        * L ^ ((2 * d : ℝ) / (2 * d - 1)))) ∧
                  (d = 2 → {x : Site d | euclidNorm x < a * N - C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
                    ∃ x : Site d, euclidNorm x < a * N + C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L ∧ x ∉ CERW.departureRange (X · ω) n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) :=
  hausdorff_bound_of_core hd hK
    (fun _ hε _ _ hC₀ hC₁ _ _ hbd => exists_good_of_event hd hε hC₀ hC₁ hbd)

/-- `eq:hausdorff` with the one-sided planar remark, for any kernel `b` with the kernel facts. -/
theorem hausdorff_bound_one_sided_of_kernelFacts {d : ℕ} (hd : 2 ≤ d)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ (Metric.hausdorffEDist
                    ((fun x => N⁻¹ • CERW.toSpace x) '' ↑(CERW.visitedRange (X · ω) n))
                    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) a)
                  ≤ ENNReal.ofReal (C * (if d = 2 then (n : ℝ) ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4)
                      else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
                        * L ^ ((2 * d : ℝ) / (2 * d - 1)))) ∧
                  (d = 2 → {x : Site d | euclidNorm x < a * N - C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L} ⊆ ↑(CERW.departureRange (X · ω) n)))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) :=
  hausdorff_bound_one_sided_of_core hd hK
    (fun _ hε _ _ hC₀ hC₁ _ _ hbd => exists_good_of_event hd hε hC₀ hC₁ hbd)

end CERW.Support.Main
