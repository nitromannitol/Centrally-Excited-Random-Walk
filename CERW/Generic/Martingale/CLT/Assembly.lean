import CERW.External.MartingaleCLT
import Mathlib.MeasureTheory.Measure.LevyConvergence
import CERW.Generic.Martingale.CLT.Interfaces
import CERW.Generic.Martingale.CLT.ArrayForm

/-!
# Assembly of the martingale central limit theorem

The array form `ArrayCLT` of the martingale central limit theorem is derived from the two
hypotheses that remain as inputs: convergence of the characteristic function of the last term of
each row (`H1`), and the passage from characteristic-function convergence to convergence in
distribution (`H2`). The array form implies the single-martingale form
`CERW.External.MartingaleCLT` carried by the paper.

The unconditional discharge of `H1` and `H2` — from the increment step bound, the path-bracket
properties, the truncated increments, the compensated exponential and the characteristic-function
bound — is the remaining step; the analytic packets are in the sibling modules.
-/

universe u

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal

/-- The array form of the martingale central limit theorem follows from convergence of the
characteristic functions of the last row terms and the passage from characteristic-function
convergence to convergence in distribution. -/
theorem arrayCLT_of_charFun
    (hH1 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → ℕ → Ω → ℝ) (v : ℝ≥0),
      (∀ n, Martingale (M n) ℱ μ) → (∀ n k, MemLp (M n k) 2 μ) →
      (∀ n ω, M n 0 ω = 0) →
      (∀ δ : ℝ, 0 < δ →
        TendstoInMeasure μ (fun n => lind μ ℱ (M n) δ n) atTop (fun _ => 0)) →
      TendstoInMeasure μ (fun n => CERW.predBracket μ ℱ (M n) (M n) n) atTop
        (fun _ => (v : ℝ)) →
      ∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (t * M n n ω * Complex.I) ∂μ) atTop
        (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ)))))
    (hH2 : ∀ {Ω : Type u} [_m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ) (v : ℝ≥0), (∀ n, AEMeasurable (X n) μ) →
      (∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (t * X n ω * Complex.I) ∂μ) atTop
        (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ))))) →
      TendstoInDistribution X atTop id (fun _ => μ) (gaussianReal 0 v)) :
    ArrayCLT.{u} := by
  intro Ω m0 μ hprob ℱ M v hMart hLp hzero hLind hBr
  have hchar : ∀ t : ℝ, Tendsto
      (fun n => ∫ ω, Complex.exp (t * M n n ω * Complex.I) ∂μ) atTop
      (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ)))) :=
    hH1 μ ℱ M v hMart hLp hzero
      (fun δ hδ => hLind δ hδ) hBr
  exact hH2 μ (fun n => M n n) v
    (fun n => (hLp n n).aestronglyMeasurable.aemeasurable) hchar

/-- **The martingale central limit theorem**, assembled from the two remaining inputs. -/
theorem martingaleCLT_holds
    (hH1 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → ℕ → Ω → ℝ) (v : ℝ≥0),
      (∀ n, Martingale (M n) ℱ μ) → (∀ n k, MemLp (M n k) 2 μ) →
      (∀ n ω, M n 0 ω = 0) →
      (∀ δ : ℝ, 0 < δ →
        TendstoInMeasure μ (fun n => lind μ ℱ (M n) δ n) atTop (fun _ => 0)) →
      TendstoInMeasure μ (fun n => CERW.predBracket μ ℱ (M n) (M n) n) atTop
        (fun _ => (v : ℝ)) →
      ∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (t * M n n ω * Complex.I) ∂μ) atTop
        (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ)))))
    (hH2 : ∀ {Ω : Type u} [_m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ) (v : ℝ≥0), (∀ n, AEMeasurable (X n) μ) →
      (∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (t * X n ω * Complex.I) ∂μ) atTop
        (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ))))) →
      TendstoInDistribution X atTop id (fun _ => μ) (gaussianReal 0 v)) :
    CERW.External.MartingaleCLT.{u} :=
  martingaleCLT_of_arrayCLT (arrayCLT_of_charFun hH1 hH2)

end CERW.Generic.Martingale.CLT
