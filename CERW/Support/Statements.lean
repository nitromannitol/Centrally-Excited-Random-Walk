import CERW.Model
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# The statements of the revised paper, as propositions

Each `Prop` below is the draft statement of one node of the revised paper, verbatim, so that a
Support proof of one statement can assume the statements it depends on. The two cited results
are `CERW.Support.Statements.MartingaleCLT` and `StoutLIL`. When the surface is frozen, each
frozen theorem is proved by applying the Support theorem for its statement.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Statements

def MartingaleCLT : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ), Martingale S ℱ μ → (∀ n, MemLp (S n) 2 μ) →
    (∀ ω, S 0 ω = 0) → ∀ (s : ℕ → ℝ), (∀ n, 0 < s n) → ∀ v : ℝ≥0,
    (∀ δ : ℝ, 0 < δ → TendstoInMeasure μ
      (fun n => ∑ i ∈ Finset.range n,
        μ[fun ω => ((S (i + 1) ω - S i ω) / s n) ^ 2 *
          (if δ < |S (i + 1) ω - S i ω| / s n then 1 else 0) | ℱ i])
      atTop (fun _ => 0)) →
    TendstoInMeasure μ (fun n => fun ω => CERW.predBracket μ ℱ S S n ω / s n ^ 2) atTop
      (fun _ => (v : ℝ)) →
    TendstoInDistribution (fun n ω => S n ω / s n) atTop id (fun _ => μ) (gaussianReal 0 v)

def StoutLIL : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ), Martingale S ℱ μ → (∀ n, MemLp (S n) 2 μ) →
    (∀ ω, S 0 ω = 0) → ∀ B : ℕ → Ω → ℝ, (∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) →
    (∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ B (n + 1) ω) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω) atTop atTop) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
        Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S n ω)
          (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ S S n ω))
      atTop (𝓝 0)) →
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      (∀ᶠ n : ℕ in atTop, S n ω ≤ (1 + δ) * Real.sqrt (2 * CERW.predBracket μ ℱ S S n ω *
        Real.log (Real.log (CERW.predBracket μ ℱ S S n ω)))) ∧
      (∃ᶠ n : ℕ in atTop, (1 - δ) * Real.sqrt (2 * CERW.predBracket μ ℱ S S n ω *
        Real.log (Real.log (CERW.predBracket μ ℱ S S n ω))) ≤ S n ω)

/-- The draft statement of `CERW.Frozen.bulk_profile`. -/
def bulk_profile : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
        let Good : (ℕ → Site d) → ℕ → Prop := fun Y n =>
          ∀ y : Site d, euclidNorm y ≤ θ * r n →
            |(CERW.localTime Y n y : ℝ) - 2 * d * ε * (r n - euclidNorm y)|
              ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n)
        (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ Good (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
        (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good (X · ω) n)

/-- The draft statement of `CERW.Frozen.cell_gradient`. -/
def cell_gradient : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      ∃ C : ℝ, 0 < C ∧
        ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m →
          CERW.IsDistribLaplacian Ψ m →
        ∀ x : Site d,
          ENNReal.ofReal (∫ v in CERW.cell x, ‖gradient Ψ v - ξ x‖)
            ≤ ENNReal.ofReal C * m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))

/-- The draft statement of `CERW.Frozen.contact_potential`. -/
def contact_potential : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
      ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
      let r : ℕ → ℝ := fun n =>
        ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
      let q : ℕ → ℝ := fun n =>
        if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
      ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
          μ {ω | ¬ ∀ y₀ : EuclideanSpace ℝ (Fin d),
              Ψ y₀ = CERW.normInnerRadius Ψ (X · ω) n →
              y₀ ∈ closure (CERW.cellSet (X · ω) n)ᶜ →
              CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y₀ ≤ C * r n * q n}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The draft statement of `CERW.Frozen.drift_crossing`. -/
def drift_crossing : Prop :=
  ∀ {d : ℕ} {ε : ℝ} (_ : 0 ≤ ε)
      (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ) (C : ℝ),
      let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => CERW.toSpace (x t) + ε •
        ∑ j ∈ Finset.range t, if x j ∉ CERW.departureRange x j then ξ (x j) else 0
      (∀ s t : ℕ, s < t → t ≤ n → ‖Z t - Z s‖ ≤ C * Real.sqrt ((t - s : ℝ) * Real.log n)) →
      ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ s t : ℕ, s < t → t ≤ n →
        (∀ j : ℕ, s ≤ j → j < t → x j ∉ CERW.departureRange x j → 0 ≤ inner ℝ u (ξ (x j))) →
        inner ℝ u (CERW.toSpace (x t) - CERW.toSpace (x s))
          ≤ C * Real.sqrt ((t - s : ℝ) * Real.log n)

/-- The draft statement of `CERW.Frozen.exp_deviation`. -/
def exp_deviation : Prop :=
  
      ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (ℱ : Filtration ℕ m0) (m n : ℕ), 0 < m → 0 < n →
        ∀ b δ α : ℝ, 0 < b → 0 ≤ δ → 0 ≤ α → α ≤ 1 →
        ∀ S : Fin m → ℕ → Ω → ℝ, (∀ i, Martingale (S i) ℱ μ) → (∀ i ω, S i 0 ω = 0) →
          (∀ i, ∀ t < n, ∀ ω, |S i (t + 1) ω - S i t ω| ≤ b) →
        ∀ E : Set Ω, MeasurableSet E → 1 - α ≤ (μ E).toReal →
          (∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
            c₀ ≤ CERW.predBracket μ ℱ (S i) (S i) n ω ∧
              CERW.predBracket μ ℱ (S i) (S i) n ω ≤ C₀) →
        ∀ β : ℝ, C ≤ β → β * b ≤ c →
          (∀ i, Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | c * β ≤ S i n ω}).toReal ∧
            Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | S i n ω ≤ -(c * β)}).toReal) ∧
          ((∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E → |CERW.predBracket μ ℱ (S i) (S j) n ω| ≤ δ) →
            β ^ 2 * δ + β ^ 3 * b ≤ 1 →
            (μ {ω | ∀ i, S i n ω < c * β}).toReal
              ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * b
                + Real.exp (C * β ^ 2) * Real.sqrt α))

/-- The draft statement of `CERW.Frozen.fixed_site_centering`. -/
def fixed_site_centering : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      ∀ y : Site d, ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
          ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
            |CERW.potential d ε (CERW.cellSet (X · ω) n) (CERW.toSpace y)
                - 2 * d * ε * (r n - euclidNorm y)
                - CERW.quadraticMart ε (X · ω) n / (ωd * r n ^ d)|
              ≤ C * if d = 2 then Real.log n ^ 3 else 1

/-- The draft statement of `CERW.Frozen.fluctuation_rates`. -/
def fluctuation_rates : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
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
        volume ((r n)⁻¹ • CERW.cellSet Y n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
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

/-- The draft statement of `CERW.Frozen.freedman_bound`. -/
def freedman_bound : Prop :=
  
      ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 2 ≤ n →
        ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ), Martingale Z ℱ μ →
          (∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) →
          μ {ω | ¬ |Z n ω - Z 0 ω|
              ≤ C * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log n) + Real.log n)}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The draft statement of `CERW.Frozen.inner_radius`. -/
def inner_radius : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      let q : ℕ → ℝ := fun n =>
        if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
      ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (|CERW.innerRadius (X · ω) n - r n| ≤ C * r n * q n ∧
                    volume ((r n)⁻¹ • CERW.cellSet (X · ω) n ∆
                        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
                      ≤ ENNReal.ofReal (C * q n) ∧
                    ∀ y : EuclideanSpace ℝ (Fin d),
                      |CERW.cellLocalTime (X · ω) n y - 2 * d * ε * max (r n - ‖y‖) 0|
                        ≤ C * r n * q n ^ ((1 : ℝ) / d))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The draft statement of `CERW.Frozen.layer_potential`. -/
def layer_potential : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d)
      {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (_ : CERW.IsNorm Ψ) {ε : ℝ} (_ : 0 < ε)
      {a b : ℝ} (_ : 0 ≤ b) (_ : 0 < a) {D : Set (EuclideanSpace ℝ (Fin d))}
      (_ : MeasurableSet D) (_ : D ⊆ {v | b ≤ Ψ v ∧ Ψ v ≤ b + a})
      (y : EuclideanSpace ℝ (Fin d)),
      |CERW.normPotential d ε Ψ D y| ≤ 2 * d * ε * a

/-- The draft statement of `CERW.Frozen.limit_shape`. -/
def limit_shape : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1 / (d : ℝ))
      {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d) (_ : CERW.IsCERW μ ε X),
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

/-- The draft statement of `CERW.Frozen.log_lower_bounds`. -/
def log_lower_bounds : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      ∃ c C h₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ ∃ n₀ : ℕ,
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
          (∀ n : ℕ, n₀ ≤ n → ∀ h : ℝ, h₀ ≤ h → h ≤ r n / 8 →
            μ {ω | r n - h ≤ CERW.innerRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ r n + h}
              ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (d - 1) * Real.exp (-(C * h))))) ∧
            μ {ω | CERW.maxRadius (X · ω) n ≤ r n + h}
              ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (d - 1) * Real.exp (-(C * h))))
                + Real.exp (-(c * r n ^ ((d : ℝ) - 3) * h ^ 2)))) ∧
          ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
            c * Real.log n < max (r n - CERW.innerRadius (X · ω) n)
              (CERW.maxRadius (X · ω) n - r n) ∧
            (3 ≤ d → c * Real.log n < CERW.maxRadius (X · ω) n - r n)

/-- The draft statement of `CERW.Frozen.moment_fluctuations`. -/
def moment_fluctuations : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d)
      (_ : MartingaleCLT.{u}) (_ : StoutLIL.{u}),
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
          (∀ᶠ n : ℕ in atTop, σ * S n ω ≤ (Real.sqrt v₁ + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
          (∃ᶠ n : ℕ in atTop, (Real.sqrt v₁ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * S n ω) ∧
          (∀ᶠ n : ℕ in atTop, σ * R n ω ≤ (Real.sqrt v₂ + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
          (∃ᶠ n : ℕ in atTop, (Real.sqrt v₂ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * R n ω)

/-- The draft statement of `CERW.Frozen.moreau_cap`. -/
def moreau_cap : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d)
      {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (_ : CERW.IsNorm Ψ) {τ : ℝ} (_ : 0 < τ)
      (x y : EuclideanSpace ℝ (Fin d)),
      let η : ℝ := CERW.normMin Ψ ^ 4 / (8 * CERW.normMax Ψ ^ 2)
      let q : EuclideanSpace ℝ (Fin d) := gradient (CERW.moreauEnvelope Ψ τ) x
      CERW.moreauEnvelope Ψ τ y ≤ CERW.moreauEnvelope Ψ τ x →
      inner ℝ q x - η * τ < inner ℝ q y →
      τ * CERW.normMax Ψ < ‖y‖ →
      ∀ ξ : EuclideanSpace ℝ (Fin d), CERW.IsSubgradient Ψ y ξ →
        CERW.normMin Ψ ^ 2 / 2 ≤ inner ℝ q ξ

/-- The draft statement of `CERW.Frozen.near_far`. -/
def near_far : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∃ C : ℝ, 0 < C ∧
        ∀ w b lam : ℝ, 1 ≤ w → w ≤ b → 1 ≤ lam →
        ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
          D ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w} →
          (∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
            volume (D ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (lam * t ^ (d - 1))) →
          (∀ y : EuclideanSpace ℝ (Fin d), ∫ v in D, ‖v - y‖ ^ (2 - (d : ℝ)) ≤ lam * b) →
          ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
            CERW.positivePotential d ε D y
              ≤ C * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + C * lam

/-- The draft statement of `CERW.Frozen.norm_ball_potential`. -/
def norm_ball_potential : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d)
      {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (_ : CERW.IsNorm Ψ) (ε : ℝ) {ρ : ℝ} (_ : 0 < ρ)
      (y : EuclideanSpace ℝ (Fin d)),
      CERW.normPotential d ε Ψ {v | Ψ v < ρ} y = 2 * d * ε * max (ρ - Ψ y) 0

/-- The draft statement of `CERW.Frozen.norm_coarse_bounds`. -/
def norm_coarse_bounds : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
      ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
      let r : ℕ → ℝ := fun n =>
        ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
      ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (c * r n ^ d ≤ ((CERW.departureRange (X · ω) n).card : ℝ) ∧
                    ((CERW.departureRange (X · ω) n).card : ℝ) ≤ C * r n ^ d ∧
                    c * r n ≤ (CERW.maxLocalTime (X · ω) n : ℝ) ∧
                    (CERW.maxLocalTime (X · ω) n : ℝ) ≤ C * r n ∧
                    c * r n ≤ CERW.maxRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ C * r n)}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The draft statement of `CERW.Frozen.norm_local_time_potential`. -/
def norm_local_time_potential : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
      ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
      ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ ((CERW.maxLocalTime (X · ω) n : ℝ)
                      ≤ C * ((CERW.departureRange (X · ω) n).card : ℝ) ^ ((1 : ℝ) / d)
                        + C * Real.log n ^ 2 ∧
                    (∀ s t : ℕ, s < t → t ≤ n →
                      (CERW.intervalMax (X · ω) s t : ℝ)
                        ≤ C * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / d)
                          + C * Real.log n ^ 2) ∧
                    ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
                      |CERW.cellLocalTime (X · ω) n y
                          - CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y|
                        ≤ C * Real.log n + C *
                          (if d = 2 then Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                            else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n)))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The draft statement of `CERW.Frozen.norm_potential_geometry`. -/
def norm_potential_geometry : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
        ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
          let R : ℝ := (volume D).toReal
          (∀ y, |CERW.normPotential d ε Ψ D y| ≤ C * ε * R ^ ((1 : ℝ) / d)) ∧
          (∀ y z, |CERW.normPotential d ε Ψ D y - CERW.normPotential d ε Ψ D z|
              ≤ C * ε * R ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
          (∀ s : ℝ, 0 < s →
            let A : ℝ := (d * ωd)⁻¹ * ∫ θ, CERW.normPotential d ε Ψ D (s • (θ : EuclideanSpace ℝ (Fin d)))
                ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
            let B : ℝ := 2 * ε / ωd * ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d
            A = B ∧ 2 * d * ε * CERW.normMin Ψ * CERW.tail d D s ≤ B ∧
              B ≤ 2 * d * ε * CERW.normMax Ψ * CERW.tail d D s ∧
              ((∀ v, Ψ v = ‖v‖) → B = 2 * d * ε * CERW.tail d D s))

/-- The draft statement of `CERW.Frozen.norm_radial_test`. -/
def norm_radial_test : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
      ∃ ρ₀ : ℝ, 8 * d < ρ₀ ∧
      ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
      ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ ∀ ρ : ℕ, ρ₀ ≤ ρ → ρ ≤ n →
              CERW.tail d (CERW.cellSet (X · ω) n) ((ρ : ℝ) + 4 * d)
                ≤ C * (CERW.shellMax (X · ω) n ρ : ℝ)
                    * (CERW.tail d (CERW.cellSet (X · ω) n) ((ρ : ℝ) - 4 * d)
                      - CERW.tail d (CERW.cellSet (X · ω) n) ((ρ : ℝ) + 4 * d))
                  + C * Real.sqrt
                      (((((CERW.departureRange (X · ω) n).filter
                          (fun x => (ρ : ℝ) - 4 * d ≤ euclidNorm x)).sup
                          (CERW.localTime (X · ω) n) : ℕ) : ℝ)
                        * (ρ : ℝ) ^ (1 - (d : ℝ))
                        * CERW.tail d (CERW.cellSet (X · ω) n) ((ρ : ℝ) - 4 * d) * Real.log n)
                  + C * (ρ : ℝ) ^ (1 - (d : ℝ)) * Real.log n}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The draft statement of `CERW.Frozen.norm_shape`. -/
def norm_shape : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d)
      {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (_ : CERW.IsNorm Ψ)
      {ξ : Site d → EuclideanSpace ℝ (Fin d)}
      (_ : ∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) (_ : ξ 0 = 0)
      {ε : ℝ} (_ : 0 < ε) (_ : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ))
      {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d) (_ : CERW.IsDriftCERW μ ε ξ X),
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

/-- The draft statement of `CERW.Frozen.norm_shape_rates`. -/
def norm_shape_rates : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
      ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
      let r : ℕ → ℝ := fun n =>
        ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
      ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (|CERW.normInnerRadius Ψ (X · ω) n - r n|
                      ≤ C * (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
                        else (r n * Real.log n) ^ ((1 : ℝ) / 2)) ∧
                    CERW.normMaxRadius Ψ (X · ω) n - r n
                      ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
                        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) ∧
                    ∀ x : Site d,
                      |(CERW.localTime (X · ω) n x : ℝ)
                          - 2 * d * ε * max (r n - Ψ (CERW.toSpace x)) 0|
                        ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                          else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The draft statement of `CERW.Frozen.outer_crossing`. -/
def outer_crossing : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
      ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
      ∀ α : ℝ, 0 < α → ∀ C₁ : ℝ, 0 < C₁ → ∃ C : ℝ, 0 < C ∧
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ n : ℕ, 2 ≤ n → ∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ ≤ CERW.normMax Ψ →
        ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ CERW.unitSteps d) →
          let Λ : ℝ := CERW.normMax Ψ
          let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => CERW.toSpace (x t) + ε •
            ∑ j ∈ Finset.range t, if x j ∉ CERW.departureRange x j then ξ (x j) else 0
          (∀ s t : ℕ, s < t → t ≤ n →
            ‖Z t - Z s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) →
          (∀ k : ℕ, k ≤ n →
            |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
                (fun z => max (inner ℝ q (CERW.toSpace z) - k * Λ) 0) x n|
              ≤ C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (CERW.departureRange x n).filter
                    (fun z => k * Λ - Λ < inner ℝ q (CERW.toSpace z)),
                    (CERW.localTime x n z : ℝ)) + Real.log n)) →
          ∀ j₀ : ℕ, j₀ ≤ n →
          (∀ j ≤ n, inner ℝ q (CERW.toSpace (x j)) ≤ inner ℝ q (CERW.toSpace (x j₀))) →
          let T : ℝ := inner ℝ q (CERW.toSpace (x j₀))
          ∀ h : ℝ, 0 < h →
          (∀ j ≤ n, T - h < inner ℝ q (CERW.toSpace (x j)) → α ≤ inner ℝ q (ξ (x j))) →
          ∀ b : ℝ, 0 ≤ b →
            T ≤ max (T - h) b + C * (1 + ((((CERW.departureRange x n).filter
                (fun z => b ≤ inner ℝ q (CERW.toSpace z))).sup (CERW.localTime x n) : ℕ) : ℝ))
              * Real.log n

/-- The draft statement of `CERW.Frozen.outer_radius`. -/
def outer_radius : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ CERW.maxRadius (X · ω) n ≤ r n + C *
              (if d = 2 then Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
                else Real.log n ^ ((d : ℝ) + 1))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The draft statement of `CERW.Frozen.separated_brackets`. -/
def separated_brackets : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      let e₁ : Site d := LatticeProb.unit ⟨0, by omega⟩
      let g : Site d → ℝ := CERW.latticeKernel d
      let σ : ℕ → ℝ := fun n =>
        if d = 2 then Real.sqrt (r n * Real.log (r n)) else Real.sqrt (r n)
      let k : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
      let m : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
      let y : ℕ → ℕ → Site d := fun n i => ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • e₁
      let f : ℕ → ℕ → Site d → ℝ := fun n i z =>
        if d = 2 then g (z - (y n i + (k n : ℤ) • e₁)) - g (z - y n i) else g (z - y n i)
      ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ,
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
          μ {ω | ¬ ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
              let B : ℝ := CERW.dynkinBracket (CERW.stepProb d ε) (f n i) (f n j) (X · ω) n /
                σ n ^ 2
              (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(10 : ℝ)))

/-- The draft statement of `CERW.Frozen.sharp_bulk`. -/
def sharp_bulk : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d),
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

/-- The draft statement of `CERW.Frozen.sharp_radii`. -/
def sharp_radii : Prop :=
  ∀ {d : ℕ} (_ : d = 2),
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

/-- The draft statement of `CERW.Frozen.sharp_radii_lil`. -/
def sharp_radii_lil : Prop :=
  ∀ {d : ℕ} (_ : d = 2)
      (_ : StoutLIL.{u}),
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

/-- The draft statement of `CERW.Frozen.sharp_width`. -/
def sharp_width : Prop :=
  ∀ {d : ℕ} (_ : d = 2)
      (_ : StoutLIL.{u}),
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
            ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n)

/-- The draft statement of `CERW.Frozen.site_fluctuations`. -/
def site_fluctuations : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d)
      (_ : MartingaleCLT.{u}) (_ : StoutLIL.{u}),
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

end CERW.Support.Statements
