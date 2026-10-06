import CERW.Frozen.FixedSiteCentering
import CERW.Frozen.MomentFluctuations
import CERW.Frozen.SharpRadiiLil
import CERW.Frozen.SharpWidth
import CERW.Frozen.SiteFluctuations
import CERW.Support.Law.Existence

/-!
# Non-vacuity guards for the limit laws

For `d = 2` and `ε = 1/8`, the hypotheses of the frozen limit laws (moment fluctuations,
fixed-site centering, site fluctuations, the radii law of the iterated logarithm, and the
width of the shell) hold together, since centrally excited random walk exists with these
parameters. The guards carry no hypothesis beyond the parameters.
-/

namespace CERW.Support.Guards

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

/-- In dimension two with `ε = 1/8`, the sum of the distances from the origin over the departure
range and the moment radius satisfy the central limit theorem and the law of the iterated
logarithm of the frozen statement, for every centrally excited random walk. -/
theorem moment_fluctuations_applies :
    let d : ℕ := 2
    let ε : ℝ := 1 / 8
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let v₁ : ℝ := 2 * d * ωd / (ε * (d + 2) * (d + 3))
    let v₂ : ℝ := 2 / (ε * d * ωd * (d + 2) * (d + 3))
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      let S : ℕ → Ω → ℝ := fun n ω =>
        (∑ x ∈ CERW.departureRange (X · ω) n, euclidNorm x - n / (2 * ε)) /
          r n ^ (((d : ℝ) + 3) / 2)
      let R : ℕ → Ω → ℝ := fun n ω =>
        (CERW.momentRadius (X · ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2)
      TendstoInDistribution S atTop id (fun _ => μ) (gaussianReal 0 v₁.toNNReal) ∧
      TendstoInDistribution R atTop id (fun _ => μ) (gaussianReal 0 v₂.toNNReal) ∧
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
        (∀ᶠ n : ℕ in atTop,
          σ * S n ω ≤ (Real.sqrt v₁ + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
        (∃ᶠ n : ℕ in atTop,
          (Real.sqrt v₁ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * S n ω) ∧
        (∀ᶠ n : ℕ in atTop,
          σ * R n ω ≤ (Real.sqrt v₂ + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
        (∃ᶠ n : ℕ in atTop,
          (Real.sqrt v₂ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * R n ω) := by
  intro d ε ωd r v₁ v₂ Ω _ μ _ X hX
  have hd : 2 ≤ d := le_rfl
  have hε : 0 < ε := by norm_num [ε]
  have hεd : ε < 1 / (d : ℝ) := by norm_num [ε, d]
  exact CERW.Frozen.moment_fluctuations hd ε hε hεd μ X hX

/-- In dimension two with `ε = 1/8`, there is a probability space carrying a centrally excited
random walk, so the hypothesis of `moment_fluctuations` is satisfiable. -/
theorem moment_fluctuations_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8 : ℝ) X :=
  CERW.Support.Law.exists_isCERW (d := 2) (by norm_num) (by norm_num) (by norm_num)

/-- In dimension two with `ε = 1/8`, the potential of the cell set at every fixed site differs
from its centering by a deterministic constant times the frozen error, eventually almost
surely, for every centrally excited random walk. -/
theorem fixed_site_centering_applies :
    let d : ℕ := 2
    let ε : ℝ := 1 / 8
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ y : Site d, ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          |CERW.potential d ε (CERW.cellSet (X · ω) n) (CERW.toSpace y)
              - 2 * d * ε * (r n - euclidNorm y)
              - CERW.quadraticMart ε (X · ω) n / (ωd * r n ^ d)|
            ≤ C * if d = 2 then Real.log n ^ 3 else 1 := by
  intro d ε
  have hd : 2 ≤ d := le_rfl
  have hε : 0 < ε := by norm_num [ε]
  have hεd : ε < 1 / (d : ℝ) := by norm_num [ε, d]
  exact CERW.Frozen.fixed_site_centering hd ε hε hεd

/-- In dimension two with `ε = 1/8`, there is a probability space carrying a centrally excited
random walk, so the hypothesis of `fixed_site_centering` is satisfiable. -/
theorem fixed_site_centering_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8 : ℝ) X :=
  CERW.Support.Law.exists_isCERW (d := 2) (by norm_num) (by norm_num) (by norm_num)

/-- In dimension two with `ε = 1/8`, the local times at fixed sites satisfy the central limit
theorem, the law of the iterated logarithm and the joint limits of the frozen statement, for every
centrally excited random walk. -/
theorem site_fluctuations_applies :
    let d : ℕ := 2
    let ε : ℝ := 1 / 8
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
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
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
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
          (multivariateGaussian 0 (Matrix.of fun i j => cov (y i) (y j)))) := by
  intro d ε ωd r G σ lil v cov Ω _ μ _ X hX
  have hd : 2 ≤ d := le_rfl
  have hε : 0 < ε := by norm_num [ε]
  have hεd : ε < 1 / (d : ℝ) := by norm_num [ε, d]
  exact CERW.Frozen.site_fluctuations hd ε hε hεd μ X hX

/-- In dimension two with `ε = 1/8`, there is a probability space carrying a centrally excited
random walk, so the hypothesis of `site_fluctuations` is satisfiable. -/
theorem site_fluctuations_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8 : ℝ) X :=
  CERW.Support.Law.exists_isCERW (d := 2) (by norm_num) (by norm_num) (by norm_num)

/-- In dimension two with `ε = 1/8`, the inner and outer radii of centrally excited random walk
satisfy the lower bound of the law of the iterated logarithm of the frozen statement. -/
theorem sharp_radii_lil_applies :
    let d : ℕ := 2
    let ε : ℝ := 1 / 8
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ r n - CERW.innerRadius (X · ω) n) ∧
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ CERW.maxRadius (X · ω) n - r n) := by
  intro d ε ωd r Ω _ μ _ X hX
  have hε : 0 < ε := by norm_num [ε]
  have hεd : ε < 1 / (d : ℝ) := by norm_num [ε, d]
  exact CERW.Frozen.sharp_radii_lil rfl ε hε hεd μ X hX

/-- In dimension two with `ε = 1/8`, there is a probability space carrying a centrally excited
random walk, so the hypothesis of `sharp_radii_lil` is satisfiable. -/
theorem sharp_radii_lil_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8 : ℝ) X :=
  CERW.Support.Law.exists_isCERW (d := 2) (by norm_num) (by norm_num) (by norm_num)

/-- In dimension two with `ε = 1/8`, the width of the shell between the inner and outer radii of
centrally excited random walk is bounded below with polynomial probability and satisfies the lower
bound of the law of the iterated logarithm of the frozen statement, the latter given Stout's law of
the iterated logarithm. -/
theorem sharp_width_applies :
    let d : ℕ := 2
    let ε : ℝ := 1 / 8
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    (∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let E : Set Ω := {ω | c * Real.sqrt (r n * Real.log n)
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n}
        MeasurableSet E ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ E) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
        (Real.sqrt (Real.pi / (3 * ε)) - δ) * Real.sqrt (r n * Real.log (Real.log n))
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n) := by
  intro d ε ωd r
  have hε : 0 < ε := by norm_num [ε]
  have hεd : ε < 1 / (d : ℝ) := by norm_num [ε, d]
  have h := CERW.Frozen.sharp_width rfl ε hε hεd
  exact ⟨h.1, h.2.1⟩

/-- In dimension two with `ε = 1/8`, there is a probability space carrying a centrally excited
random walk, so the hypothesis of `sharp_width` is satisfiable. -/
theorem sharp_width_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8 : ℝ) X :=
  CERW.Support.Law.exists_isCERW (d := 2) (by norm_num) (by norm_num) (by norm_num)

end CERW.Support.Guards
